import V185TrunkScan23Chunk1230

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7294263 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 7, 3, 2]
def baseStart_7294263 : Nat := 118140960795 + 7294263 * 2 ^ 59
def prefixEnd_7294263 : Nat := 4983230072969 + 3 ^ 40 * 7294263 * 2
def baseEnd_7294263 : Nat := 3745462939306699896166801

theorem tailTrace_7294263 : CollatzResearch.WordTrace tailWord_7294263 prefixEnd_7294263 3745462939306699896166801 := by
  unfold tailWord_7294263
  simp only [CollatzResearch.WordTrace]
  refine ⟨266043627973138386785415443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177362418648758924523610295 266043627973138386785415443)
  ·
    refine ⟨399065441959707580178123165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266043627973138386785415443 399065441959707580178123165)
    ·
      refine ⟨149649540734890342566796187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399065441959707580178123165 149649540734890342566796187)
      ·
        refine ⟨224474311102335513850194281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149649540734890342566796187 224474311102335513850194281)
        ·
          refine ⟨168355733326751635387645711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224474311102335513850194281 168355733326751635387645711)
          ·
            refine ⟨252533599990127453081468567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168355733326751635387645711 252533599990127453081468567)
            ·
              refine ⟨378800399985191179622202851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252533599990127453081468567 378800399985191179622202851)
              ·
                refine ⟨568200599977786769433304277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378800399985191179622202851 568200599977786769433304277)
                ·
                  refine ⟨13317201561979377408593069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 568200599977786769433304277 13317201561979377408593069)
                  ·
                    refine ⟨4993950585742266528222401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13317201561979377408593069 4993950585742266528222401)
                    ·
                      refine ⟨3745462939306699896166801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993950585742266528222401 3745462939306699896166801)
                      ·
                        rfl

theorem cell23_7294263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_7294263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294263 prefixEnd_7294263 := by exact prefixLift 7294263
  have htrace : WordTrace (prefixWord ++ tailWord_7294263) baseStart_7294263 baseEnd_7294263 := by
    simpa [prefixWord, tailWord_7294263, baseEnd_7294263] using wordTrace_append hprefix tailTrace_7294263
  have hstable : (prefixWord ++ tailWord_7294263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294263).length < 2 ^ (prefixWord ++ tailWord_7294263).sum := by decide
  have hdescent : baseEnd_7294263 < baseStart_7294263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294266 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_7294266 : Nat := 118140960795 + 7294266 * 2 ^ 59
def prefixEnd_7294266 : Nat := 4983230072969 + 3 ^ 40 * 7294266 * 2
def baseEnd_7294266 : Nat := 3745464479748663384429287

theorem tailTrace_7294266 : CollatzResearch.WordTrace tailWord_7294266 prefixEnd_7294266 3745464479748663384429287 := by
  unfold tailWord_7294266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66510934348031879574443663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177362491594751678865183101 66510934348031879574443663)
  ·
    refine ⟨99766401522047819361665495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66510934348031879574443663 99766401522047819361665495)
    ·
      refine ⟨149649602283071729042498243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99766401522047819361665495 149649602283071729042498243)
      ·
        refine ⟨224474403424607593563747365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149649602283071729042498243 224474403424607593563747365)
        ·
          refine ⟨42088950642113923793202631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224474403424607593563747365 42088950642113923793202631)
          ·
            refine ⟨63133425963170885689803947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42088950642113923793202631 63133425963170885689803947)
            ·
              refine ⟨94700138944756328534705921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63133425963170885689803947 94700138944756328534705921)
              ·
                refine ⟨71025104208567246401029441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94700138944756328534705921 71025104208567246401029441)
                ·
                  refine ⟨53268828156425434800772081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71025104208567246401029441 53268828156425434800772081)
                  ·
                    refine ⟨39951621117319076100579061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53268828156425434800772081 39951621117319076100579061)
                    ·
                      refine ⟨3745464479748663384429287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39951621117319076100579061 3745464479748663384429287)
                      ·
                        rfl

theorem cell23_7294266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_7294266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294266 prefixEnd_7294266 := by exact prefixLift 7294266
  have htrace : WordTrace (prefixWord ++ tailWord_7294266) baseStart_7294266 baseEnd_7294266 := by
    simpa [prefixWord, tailWord_7294266, baseEnd_7294266] using wordTrace_append hprefix tailTrace_7294266
  have hstable : (prefixWord ++ tailWord_7294266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294266).length < 2 ^ (prefixWord ++ tailWord_7294266).sum := by decide
  have hdescent : baseEnd_7294266 < baseStart_7294266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294270 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_7294270 : Nat := 118140960795 + 7294270 * 2 ^ 59
def prefixEnd_7294270 : Nat := 4983230072969 + 3 ^ 40 * 7294270 * 2
def baseEnd_7294270 : Nat := 3745466533671281368779269

theorem tailTrace_7294270 : CollatzResearch.WordTrace tailWord_7294270 prefixEnd_7294270 3745466533671281368779269 := by
  unfold tailWord_7294270
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255485410514128372615033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177362588856075351320613509 33255485410514128372615033)
  ·
    refine ⟨24941614057885596279461275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33255485410514128372615033 24941614057885596279461275)
    ·
      refine ⟨37412421086828394419191913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24941614057885596279461275 37412421086828394419191913)
      ·
        refine ⟨28059315815121295814393935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37412421086828394419191913 28059315815121295814393935)
        ·
          refine ⟨42088973722681943721590903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28059315815121295814393935 42088973722681943721590903)
          ·
            refine ⟨63133460584022915582386355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42088973722681943721590903 63133460584022915582386355)
            ·
              refine ⟨94700190876034373373579533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63133460584022915582386355 94700190876034373373579533)
              ·
                refine ⟨35512571578512890015092325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94700190876034373373579533 35512571578512890015092325)
                ·
                  refine ⟨6658607170971166877829811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35512571578512890015092325 6658607170971166877829811)
                  ·
                    refine ⟨9987910756456750316744717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6658607170971166877829811 9987910756456750316744717)
                    ·
                      refine ⟨3745466533671281368779269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9987910756456750316744717 3745466533671281368779269)
                      ·
                        rfl

theorem cell23_7294270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_7294270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294270 prefixEnd_7294270 := by exact prefixLift 7294270
  have htrace : WordTrace (prefixWord ++ tailWord_7294270) baseStart_7294270 baseEnd_7294270 := by
    simpa [prefixWord, tailWord_7294270, baseEnd_7294270] using wordTrace_append hprefix tailTrace_7294270
  have hstable : (prefixWord ++ tailWord_7294270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294270).length < 2 ^ (prefixWord ++ tailWord_7294270).sum := by decide
  have hdescent : baseEnd_7294270 < baseStart_7294270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294286 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_7294286 : Nat := 118140960795 + 7294286 * 2 ^ 59
def prefixEnd_7294286 : Nat := 4983230072969 + 3 ^ 40 * 7294286 * 2
def baseEnd_7294286 : Nat := 1248491583120584435393065

theorem tailTrace_7294286 : CollatzResearch.WordTrace tailWord_7294286 prefixEnd_7294286 1248491583120584435393065 := by
  unfold tailWord_7294286
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255558356506882714187839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177362977901370041142335141 33255558356506882714187839)
  ·
    refine ⟨49883337534760324071281759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33255558356506882714187839 49883337534760324071281759)
    ·
      refine ⟨74825006302140486106922639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49883337534760324071281759 74825006302140486106922639)
      ·
        refine ⟨112237509453210729160383959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74825006302140486106922639 112237509453210729160383959)
        ·
          refine ⟨168356264179816093740575939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112237509453210729160383959 168356264179816093740575939)
          ·
            refine ⟨252534396269724140610863909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168356264179816093740575939 252534396269724140610863909)
            ·
              refine ⟨47350199300573276364536983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252534396269724140610863909 47350199300573276364536983)
              ·
                refine ⟨71025298950859914546805475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47350199300573276364536983 71025298950859914546805475)
                ·
                  refine ⟨106537948426289871820208213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71025298950859914546805475 106537948426289871820208213)
                  ·
                    refine ⟨1248491583120584435393065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106537948426289871820208213 1248491583120584435393065)
                    ·
                      rfl

theorem cell23_7294286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_7294286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294286 prefixEnd_7294286 := by exact prefixLift 7294286
  have htrace : WordTrace (prefixWord ++ tailWord_7294286) baseStart_7294286 baseEnd_7294286 := by
    simpa [prefixWord, tailWord_7294286, baseEnd_7294286] using wordTrace_append hprefix tailTrace_7294286
  have hstable : (prefixWord ++ tailWord_7294286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294286).length < 2 ^ (prefixWord ++ tailWord_7294286).sum := by decide
  have hdescent : baseEnd_7294286 < baseStart_7294286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294296 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_7294296 : Nat := 118140960795 + 7294296 * 2 ^ 59
def prefixEnd_7294296 : Nat := 4983230072969 + 3 ^ 40 * 7294296 * 2
def baseEnd_7294296 : Nat := 3745479884168298267054149

theorem tailTrace_7294296 : CollatzResearch.WordTrace tailWord_7294296 prefixEnd_7294296 3745479884168298267054149 := by
  unfold tailWord_7294296
  simp only [CollatzResearch.WordTrace]
  refine ⟨133022415791009416710683371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177363221054679222280911161 133022415791009416710683371)
  ·
    refine ⟨199533623686514125066025057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133022415791009416710683371 199533623686514125066025057)
    ·
      refine ⟨149650217764885593799518793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199533623686514125066025057 149650217764885593799518793)
      ·
        refine ⟨112237663323664195349639095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149650217764885593799518793 112237663323664195349639095)
        ·
          refine ⟨168356494985496293024458643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112237663323664195349639095 168356494985496293024458643)
          ·
            refine ⟨252534742478244439536687965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168356494985496293024458643 252534742478244439536687965)
            ·
              refine ⟨94700528429341664826257987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252534742478244439536687965 94700528429341664826257987)
              ·
                refine ⟨142050792644012497239386981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94700528429341664826257987 142050792644012497239386981)
                ·
                  refine ⟨26634523620752343232385059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142050792644012497239386981 26634523620752343232385059)
                  ·
                    refine ⟨39951785431128514848577589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26634523620752343232385059 39951785431128514848577589)
                    ·
                      refine ⟨3745479884168298267054149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39951785431128514848577589 3745479884168298267054149)
                      ·
                        rfl

theorem cell23_7294296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_7294296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294296 prefixEnd_7294296 := by exact prefixLift 7294296
  have htrace : WordTrace (prefixWord ++ tailWord_7294296) baseStart_7294296 baseEnd_7294296 := by
    simpa [prefixWord, tailWord_7294296, baseEnd_7294296] using wordTrace_append hprefix tailTrace_7294296
  have hstable : (prefixWord ++ tailWord_7294296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294296).length < 2 ^ (prefixWord ++ tailWord_7294296).sum := by decide
  have hdescent : baseEnd_7294296 < baseStart_7294296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294327 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 2, 2, 2]
def baseStart_7294327 : Nat := 118140960795 + 7294327 * 2 ^ 59
def prefixEnd_7294327 : Nat := 4983230072969 + 3 ^ 40 * 7294327 * 2
def baseEnd_7294327 : Nat := 3745495802068587645766507

theorem tailTrace_7294327 : CollatzResearch.WordTrace tailWord_7294327 prefixEnd_7294327 3745495802068587645766507 := by
  unfold tailWord_7294327
  simp only [CollatzResearch.WordTrace]
  refine ⟨266045962244906525715745235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177363974829937683810496823 266045962244906525715745235)
  ·
    refine ⟨399068943367359788573617853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266045962244906525715745235 399068943367359788573617853)
    ·
      refine ⟨149650853762759920715106695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399068943367359788573617853 149650853762759920715106695)
      ·
        refine ⟨224476280644139881072660043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149650853762759920715106695 224476280644139881072660043)
        ·
          refine ⟨336714420966209821608990065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224476280644139881072660043 336714420966209821608990065)
          ·
            refine ⟨252535815724657366206742549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336714420966209821608990065 252535815724657366206742549)
            ·
              refine ⟨11837616362093314040941057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252535815724657366206742549 11837616362093314040941057)
              ·
                refine ⟨8878212271569985530705793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11837616362093314040941057 8878212271569985530705793)
                ·
                  refine ⟨6658659203677489148029345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8878212271569985530705793 6658659203677489148029345)
                  ·
                    refine ⟨4993994402758116861022009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658659203677489148029345 4993994402758116861022009)
                    ·
                      refine ⟨3745495802068587645766507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993994402758116861022009 3745495802068587645766507)
                      ·
                        rfl

theorem cell23_7294327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_7294327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294327 prefixEnd_7294327 := by exact prefixLift 7294327
  have htrace : WordTrace (prefixWord ++ tailWord_7294327) baseStart_7294327 baseEnd_7294327 := by
    simpa [prefixWord, tailWord_7294327, baseEnd_7294327] using wordTrace_append hprefix tailTrace_7294327
  have hstable : (prefixWord ++ tailWord_7294327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294327).length < 2 ^ (prefixWord ++ tailWord_7294327).sum := by decide
  have hdescent : baseEnd_7294327 < baseStart_7294327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294343 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_7294343 : Nat := 118140960795 + 7294343 * 2 ^ 59
def prefixEnd_7294343 : Nat := 4983230072969 + 3 ^ 40 * 7294343 * 2
def baseEnd_7294343 : Nat := 3745504017759059583166433

theorem tailTrace_7294343 : CollatzResearch.WordTrace tailWord_7294343 prefixEnd_7294343 3745504017759059583166433 := by
  unfold tailWord_7294343
  simp only [CollatzResearch.WordTrace]
  refine ⟨266046545812848560448327683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177364363875232373632218455 266046545812848560448327683)
  ·
    refine ⟨399069818719272840672491525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266046545812848560448327683 399069818719272840672491525)
    ·
      refine ⟨74825591009863657626092161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399069818719272840672491525 74825591009863657626092161)
      ·
        refine ⟨56119193257397743219569121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74825591009863657626092161 56119193257397743219569121)
        ·
          refine ⟨42089394943048307414676841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56119193257397743219569121 42089394943048307414676841)
          ·
            refine ⟨31567046207286230561007631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42089394943048307414676841 31567046207286230561007631)
            ·
              refine ⟨47350569310929345841511447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31567046207286230561007631 47350569310929345841511447)
              ·
                refine ⟨71025853966394018762267171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47350569310929345841511447 71025853966394018762267171)
                ·
                  refine ⟨106538780949591028143400757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71025853966394018762267171 106538780949591028143400757)
                  ·
                    refine ⟨9988010714024158888443821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106538780949591028143400757 9988010714024158888443821)
                    ·
                      refine ⟨3745504017759059583166433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9988010714024158888443821 3745504017759059583166433)
                      ·
                        rfl

theorem cell23_7294343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_7294343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294343 prefixEnd_7294343 := by exact prefixLift 7294343
  have htrace : WordTrace (prefixWord ++ tailWord_7294343) baseStart_7294343 baseEnd_7294343 := by
    simpa [prefixWord, tailWord_7294343, baseEnd_7294343] using wordTrace_append hprefix tailTrace_7294343
  have hstable : (prefixWord ++ tailWord_7294343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294343).length < 2 ^ (prefixWord ++ tailWord_7294343).sum := by decide
  have hdescent : baseEnd_7294343 < baseStart_7294343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294350 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_7294350 : Nat := 118140960795 + 7294350 * 2 ^ 59
def prefixEnd_7294350 : Nat := 4983230072969 + 3 ^ 40 * 7294350 * 2
def baseEnd_7294350 : Nat := 416167512458182339530989

theorem tailTrace_7294350 : CollatzResearch.WordTrace tailWord_7294350 prefixEnd_7294350 416167512458182339530989 := by
  unfold tailWord_7294350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255850140477900080479063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177364534082548800429221669 33255850140477900080479063)
  ·
    refine ⟨49883775210716850120718595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33255850140477900080479063 49883775210716850120718595)
    ·
      refine ⟨74825662816075275181077893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49883775210716850120718595 74825662816075275181077893)
      ·
        refine ⟨14029811778014114096452105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74825662816075275181077893 14029811778014114096452105)
        ·
          refine ⟨10522358833510585572339079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14029811778014114096452105 10522358833510585572339079)
          ·
            refine ⟨15783538250265878358508619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10522358833510585572339079 15783538250265878358508619)
            ·
              refine ⟨23675307375398817537762929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15783538250265878358508619 23675307375398817537762929)
              ·
                refine ⟨17756480531549113153322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23675307375398817537762929 17756480531549113153322197)
                ·
                  refine ⟨416167512458182339530989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17756480531549113153322197 416167512458182339530989)
                  ·
                    rfl

theorem cell23_7294350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_7294350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294350 prefixEnd_7294350 := by exact prefixLift 7294350
  have htrace : WordTrace (prefixWord ++ tailWord_7294350) baseStart_7294350 baseEnd_7294350 := by
    simpa [prefixWord, tailWord_7294350, baseEnd_7294350] using wordTrace_append hprefix tailTrace_7294350
  have hstable : (prefixWord ++ tailWord_7294350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294350).length < 2 ^ (prefixWord ++ tailWord_7294350).sum := by decide
  have hdescent : baseEnd_7294350 < baseStart_7294350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294383 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_7294383 : Nat := 118140960795 + 7294383 * 2 ^ 59
def prefixEnd_7294383 : Nat := 4983230072969 + 3 ^ 40 * 7294383 * 2
def baseEnd_7294383 : Nat := 3745524556985239426666249

theorem tailTrace_7294383 : CollatzResearch.WordTrace tailWord_7294383 prefixEnd_7294383 3745524556985239426666249 := by
  unfold tailWord_7294383
  simp only [CollatzResearch.WordTrace]
  refine ⟨266048004732703647279783803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177365336488469098186522535 266048004732703647279783803)
  ·
    refine ⟨399072007099055470919675705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266048004732703647279783803 399072007099055470919675705)
    ·
      refine ⟨299304005324291603189756779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399072007099055470919675705 299304005324291603189756779)
      ·
        refine ⟨448956007986437404784635169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299304005324291603189756779 448956007986437404784635169)
        ·
          refine ⟨336717005989828053588476377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448956007986437404784635169 336717005989828053588476377)
          ·
            refine ⟨252537754492371040191357283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336717005989828053588476377 252537754492371040191357283)
            ·
              refine ⟨378806631738556560287035925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252537754492371040191357283 378806631738556560287035925)
              ·
                refine ⟨17756560862744838763454809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 378806631738556560287035925 17756560862744838763454809)
                ·
                  refine ⟨13317420647058629072591107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17756560862744838763454809 13317420647058629072591107)
                  ·
                    refine ⟨19976130970587943608886661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13317420647058629072591107 19976130970587943608886661)
                    ·
                      refine ⟨3745524556985239426666249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19976130970587943608886661 3745524556985239426666249)
                      ·
                        rfl

theorem cell23_7294383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_7294383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294383 prefixEnd_7294383 := by exact prefixLift 7294383
  have htrace : WordTrace (prefixWord ++ tailWord_7294383) baseStart_7294383 baseEnd_7294383 := by
    simpa [prefixWord, tailWord_7294383, baseEnd_7294383] using wordTrace_append hprefix tailTrace_7294383
  have hstable : (prefixWord ++ tailWord_7294383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294383).length < 2 ^ (prefixWord ++ tailWord_7294383).sum := by decide
  have hdescent : baseEnd_7294383 < baseStart_7294383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294400 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 2, 4, 2]
def baseStart_7294400 : Nat := 118140960795 + 7294400 * 2 ^ 59
def prefixEnd_7294400 : Nat := 4983230072969 + 3 ^ 40 * 7294400 * 2
def baseEnd_7294400 : Nat := 3745533286156365860153671

theorem tailTrace_7294400 : CollatzResearch.WordTrace tailWord_7294400 prefixEnd_7294400 3745533286156365860153671 := by
  unfold tailWord_7294400
  simp only [CollatzResearch.WordTrace]
  refine ⟨133024312386821029591576327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177365749849094706122101769 133024312386821029591576327)
  ·
    refine ⟨199536468580231544387364491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133024312386821029591576327 199536468580231544387364491)
    ·
      refine ⟨299304702870347316581046737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199536468580231544387364491 299304702870347316581046737)
      ·
        refine ⟨224478527152760487435785053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299304702870347316581046737 224478527152760487435785053)
        ·
          refine ⟨84179447682285182788419395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224478527152760487435785053 84179447682285182788419395)
          ·
            refine ⟨126269171523427774182629093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84179447682285182788419395 126269171523427774182629093)
            ·
              refine ⟨23675469660642707659242955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126269171523427774182629093 23675469660642707659242955)
              ·
                refine ⟨35513204490964061488864433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23675469660642707659242955 35513204490964061488864433)
                ·
                  refine ⟨26634903368223046116648325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35513204490964061488864433 26634903368223046116648325)
                  ·
                    refine ⟨4994044381541821146871561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26634903368223046116648325 4994044381541821146871561)
                    ·
                      refine ⟨3745533286156365860153671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994044381541821146871561 3745533286156365860153671)
                      ·
                        rfl

theorem cell23_7294400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_7294400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294400 prefixEnd_7294400 := by exact prefixLift 7294400
  have htrace : WordTrace (prefixWord ++ tailWord_7294400) baseStart_7294400 baseEnd_7294400 := by
    simpa [prefixWord, tailWord_7294400, baseEnd_7294400] using wordTrace_append hprefix tailTrace_7294400
  have hstable : (prefixWord ++ tailWord_7294400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294400).length < 2 ^ (prefixWord ++ tailWord_7294400).sum := by decide
  have hdescent : baseEnd_7294400 < baseStart_7294400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294403 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 3]
def baseStart_7294403 : Nat := 118140960795 + 7294403 * 2 ^ 59
def prefixEnd_7294403 : Nat := 4983230072969 + 3 ^ 40 * 7294403 * 2
def baseEnd_7294403 : Nat := 3745534826598329348416157

theorem tailTrace_7294403 : CollatzResearch.WordTrace tailWord_7294403 prefixEnd_7294403 3745534826598329348416157 := by
  unfold tailWord_7294403
  simp only [CollatzResearch.WordTrace]
  refine ⟨266048734192631190695511863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177365822795087460463674575 266048734192631190695511863)
  ·
    refine ⟨399073101288946786043267795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266048734192631190695511863 399073101288946786043267795)
    ·
      refine ⟨598609651933420179064901693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399073101288946786043267795 598609651933420179064901693)
      ·
        refine ⟨224478619475032567149338135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598609651933420179064901693 224478619475032567149338135)
        ·
          refine ⟨336717929212548850724007203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224478619475032567149338135 336717929212548850724007203)
          ·
            refine ⟨505076893818823276086010805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336717929212548850724007203 505076893818823276086010805)
            ·
              refine ⟨47350958795514682133063513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 505076893818823276086010805 47350958795514682133063513)
              ·
                refine ⟨35513219096636011599797635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47350958795514682133063513 35513219096636011599797635)
                ·
                  refine ⟨53269828644954017399696453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35513219096636011599797635 53269828644954017399696453)
                  ·
                    refine ⟨9988092870928878262443085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53269828644954017399696453 9988092870928878262443085)
                    ·
                      refine ⟨3745534826598329348416157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9988092870928878262443085 3745534826598329348416157)
                      ·
                        rfl

theorem cell23_7294403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_7294403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294403 prefixEnd_7294403 := by exact prefixLift 7294403
  have htrace : WordTrace (prefixWord ++ tailWord_7294403) baseStart_7294403 baseEnd_7294403 := by
    simpa [prefixWord, tailWord_7294403, baseEnd_7294403] using wordTrace_append hprefix tailTrace_7294403
  have hstable : (prefixWord ++ tailWord_7294403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294403).length < 2 ^ (prefixWord ++ tailWord_7294403).sum := by decide
  have hdescent : baseEnd_7294403 < baseStart_7294403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294410 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_7294410 : Nat := 118140960795 + 7294410 * 2 ^ 59
def prefixEnd_7294410 : Nat := 4983230072969 + 3 ^ 40 * 7294410 * 2
def baseEnd_7294410 : Nat := 1248512806987636940342875

theorem tailTrace_7294410 : CollatzResearch.WordTrace tailWord_7294410 prefixEnd_7294410 1248512806987636940342875 := by
  unfold tailWord_7294410
  simp only [CollatzResearch.WordTrace]
  refine ⟨66512247375901457722754171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177365993002403887260677789 66512247375901457722754171)
  ·
    refine ⟨99768371063852186584131257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66512247375901457722754171 99768371063852186584131257)
    ·
      refine ⟨74826278297889139938098443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99768371063852186584131257 74826278297889139938098443)
      ·
        refine ⟨112239417446833709907147665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74826278297889139938098443 112239417446833709907147665)
        ·
          refine ⟨84179563085125282430360749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112239417446833709907147665 84179563085125282430360749)
          ·
            refine ⟨31567336156921980911385281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84179563085125282430360749 31567336156921980911385281)
            ·
              refine ⟨23675502117691485683538961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31567336156921980911385281 23675502117691485683538961)
              ·
                refine ⟨17756626588268614262654221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23675502117691485683538961 17756626588268614262654221)
                ·
                  refine ⟨6658734970600730348495333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17756626588268614262654221 6658734970600730348495333)
                  ·
                    refine ⟨1248512806987636940342875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6658734970600730348495333 1248512806987636940342875)
                    ·
                      rfl

theorem cell23_7294410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_7294410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294410 prefixEnd_7294410 := by exact prefixLift 7294410
  have htrace : WordTrace (prefixWord ++ tailWord_7294410) baseStart_7294410 baseEnd_7294410 := by
    simpa [prefixWord, tailWord_7294410, baseEnd_7294410] using wordTrace_append hprefix tailTrace_7294410
  have hstable : (prefixWord ++ tailWord_7294410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294410).length < 2 ^ (prefixWord ++ tailWord_7294410).sum := by decide
  have hdescent : baseEnd_7294410 < baseStart_7294410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294437 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7294437 : Nat := 118140960795 + 7294437 * 2 ^ 59
def prefixEnd_7294437 : Nat := 4983230072969 + 3 ^ 40 * 7294437 * 2
def baseEnd_7294437 : Nat := 3745552284940582215391001

theorem tailTrace_7294437 : CollatzResearch.WordTrace tailWord_7294437 prefixEnd_7294437 3745552284940582215391001 := by
  unfold tailWord_7294437
  simp only [CollatzResearch.WordTrace]
  refine ⟨266049974274508014502249565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177366649516338676334833043 266049974274508014502249565)
  ·
    refine ⟨99768740352940505438343587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266049974274508014502249565 99768740352940505438343587)
    ·
      refine ⟨149653110529410758157515381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99768740352940505438343587 149653110529410758157515381)
      ·
        refine ⟨14029979112132258577267067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149653110529410758157515381 14029979112132258577267067)
        ·
          refine ⟨21044968668198387865900601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14029979112132258577267067 21044968668198387865900601)
          ·
            refine ⟨15783726501148790899425451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21044968668198387865900601 15783726501148790899425451)
            ·
              refine ⟨23675589751723186349138177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15783726501148790899425451 23675589751723186349138177)
              ·
                refine ⟨17756692313792389761853633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23675589751723186349138177 17756692313792389761853633)
                ·
                  refine ⟨13317519235344292321390225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17756692313792389761853633 13317519235344292321390225)
                  ·
                    refine ⟨9988139426508219241042669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13317519235344292321390225 9988139426508219241042669)
                    ·
                      refine ⟨3745552284940582215391001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9988139426508219241042669 3745552284940582215391001)
                      ·
                        rfl

theorem cell23_7294437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7294437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294437 prefixEnd_7294437 := by exact prefixLift 7294437
  have htrace : WordTrace (prefixWord ++ tailWord_7294437) baseStart_7294437 baseEnd_7294437 := by
    simpa [prefixWord, tailWord_7294437, baseEnd_7294437] using wordTrace_append hprefix tailTrace_7294437
  have hstable : (prefixWord ++ tailWord_7294437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294437).length < 2 ^ (prefixWord ++ tailWord_7294437).sum := by decide
  have hdescent : baseEnd_7294437 < baseStart_7294437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294460 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_7294460 : Nat := 118140960795 + 7294460 * 2 ^ 59
def prefixEnd_7294460 : Nat := 4983230072969 + 3 ^ 40 * 7294460 * 2
def baseEnd_7294460 : Nat := 3745564094995635625403395

theorem tailTrace_7294460 : CollatzResearch.WordTrace tailWord_7294460 prefixEnd_7294460 3745564094995635625403395 := by
  unfold tailWord_7294460
  simp only [CollatzResearch.WordTrace]
  refine ⟨133025406576712344715168417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177367208768949792953557889 133025406576712344715168417)
  ·
    refine ⟨99769054932534258536376313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133025406576712344715168417 99769054932534258536376313)
    ·
      refine ⟨74826791199400693902282235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99769054932534258536376313 74826791199400693902282235)
      ·
        refine ⟨112240186799101040853423353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74826791199400693902282235 112240186799101040853423353)
        ·
          refine ⟨84180140099325780640067515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112240186799101040853423353 84180140099325780640067515)
          ·
            refine ⟨126270210148988670960101273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84180140099325780640067515 126270210148988670960101273)
            ·
              refine ⟨94702657611741503220075955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126270210148988670960101273 94702657611741503220075955)
              ·
                refine ⟨142053986417612254830113933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94702657611741503220075955 142053986417612254830113933)
                ·
                  refine ⟨53270244906604595561292725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142053986417612254830113933 53270244906604595561292725)
                  ·
                    refine ⟨4994085459994180833871193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53270244906604595561292725 4994085459994180833871193)
                    ·
                      refine ⟨3745564094995635625403395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994085459994180833871193 3745564094995635625403395)
                      ·
                        rfl

theorem cell23_7294460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_7294460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294460 prefixEnd_7294460 := by exact prefixLift 7294460
  have htrace : WordTrace (prefixWord ++ tailWord_7294460) baseStart_7294460 baseEnd_7294460 := by
    simpa [prefixWord, tailWord_7294460, baseEnd_7294460] using wordTrace_append hprefix tailTrace_7294460
  have hstable : (prefixWord ++ tailWord_7294460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294460).length < 2 ^ (prefixWord ++ tailWord_7294460).sum := by decide
  have hdescent : baseEnd_7294460 < baseStart_7294460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294483 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 3, 6]
def baseStart_7294483 : Nat := 118140960795 + 7294483 * 2 ^ 59
def prefixEnd_7294483 : Nat := 4983230072969 + 3 ^ 40 * 7294483 * 2
def baseEnd_7294483 : Nat := 1248525301683563011805263

theorem tailTrace_7294483 : CollatzResearch.WordTrace tailWord_7294483 prefixEnd_7294483 1248525301683563011805263 := by
  unfold tailWord_7294483
  simp only [CollatzResearch.WordTrace]
  refine ⟨266051652032341364358424103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177367768021560909572282735 266051652032341364358424103)
  ·
    refine ⟨399077478048512046537636155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266051652032341364358424103 399077478048512046537636155)
    ·
      refine ⟨598616217072768069806454233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399077478048512046537636155 598616217072768069806454233)
      ·
        refine ⟨448962162804576052354840675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598616217072768069806454233 448962162804576052354840675)
        ·
          refine ⟨673443244206864078532261013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448962162804576052354840675 673443244206864078532261013)
          ·
            refine ⟨31567652072196753681199735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 673443244206864078532261013 31567652072196753681199735)
            ·
              refine ⟨47351478108295130521799603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31567652072196753681199735 47351478108295130521799603)
              ·
                refine ⟨71027217162442695782699405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47351478108295130521799603 71027217162442695782699405)
                ·
                  refine ⟨26635206435916010918512277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71027217162442695782699405 26635206435916010918512277)
                  ·
                    refine ⟨1248525301683563011805263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26635206435916010918512277 1248525301683563011805263)
                    ·
                      rfl

theorem cell23_7294483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 6].length) (baseStart_7294483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294483 prefixEnd_7294483 := by exact prefixLift 7294483
  have htrace : WordTrace (prefixWord ++ tailWord_7294483) baseStart_7294483 baseEnd_7294483 := by
    simpa [prefixWord, tailWord_7294483, baseEnd_7294483] using wordTrace_append hprefix tailTrace_7294483
  have hstable : (prefixWord ++ tailWord_7294483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294483).length < 2 ^ (prefixWord ++ tailWord_7294483).sum := by decide
  have hdescent : baseEnd_7294483 < baseStart_7294483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294517 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_7294517 : Nat := 118140960795 + 7294517 * 2 ^ 59
def prefixEnd_7294517 : Nat := 4983230072969 + 3 ^ 40 * 7294517 * 2
def baseEnd_7294517 : Nat := 1248531121130980634130211

theorem tailTrace_7294517 : CollatzResearch.WordTrace tailWord_7294517 prefixEnd_7294517 1248531121130980634130211 := by
  unfold tailWord_7294517
  simp only [CollatzResearch.WordTrace]
  refine ⟨266052892114218188165161805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177368594742812125443441203 266052892114218188165161805)
  ·
    refine ⟨99769834542831820561935677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266052892114218188165161805 99769834542831820561935677)
    ·
      refine ⟨37413687953561932710725879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99769834542831820561935677 37413687953561932710725879)
      ·
        refine ⟨56120531930342899066088819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37413687953561932710725879 56120531930342899066088819)
        ·
          refine ⟨84180797895514348599133229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56120531930342899066088819 84180797895514348599133229)
          ·
            refine ⟨31567799210817880724674961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84180797895514348599133229 31567799210817880724674961)
            ·
              refine ⟨23675849408113410543506221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31567799210817880724674961 23675849408113410543506221)
              ·
                refine ⟨8878443528042528953814833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23675849408113410543506221 8878443528042528953814833)
                ·
                  refine ⟨6658832646031896715361125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8878443528042528953814833 6658832646031896715361125)
                  ·
                    refine ⟨1248531121130980634130211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6658832646031896715361125 1248531121130980634130211)
                    ·
                      rfl

theorem cell23_7294517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_7294517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294517 prefixEnd_7294517 := by exact prefixLift 7294517
  have htrace : WordTrace (prefixWord ++ tailWord_7294517) baseStart_7294517 baseEnd_7294517 := by
    simpa [prefixWord, tailWord_7294517, baseEnd_7294517] using wordTrace_append hprefix tailTrace_7294517
  have hstable : (prefixWord ++ tailWord_7294517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294517).length < 2 ^ (prefixWord ++ tailWord_7294517).sum := by decide
  have hdescent : baseEnd_7294517 < baseStart_7294517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294520 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_7294520 : Nat := 118140960795 + 7294520 * 2 ^ 59
def prefixEnd_7294520 : Nat := 4983230072969 + 3 ^ 40 * 7294520 * 2
def baseEnd_7294520 : Nat := 3745594903834905390653119

theorem tailTrace_7294520 : CollatzResearch.WordTrace tailWord_7294520 prefixEnd_7294520 3745594903834905390653119 := by
  unfold tailWord_7294520
  simp only [CollatzResearch.WordTrace]
  refine ⟨133026500766603659838760507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177368667688804879785014009 133026500766603659838760507)
  ·
    refine ⟨199539751149905489758140761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133026500766603659838760507 199539751149905489758140761)
    ·
      refine ⟨149654813362429117318605571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199539751149905489758140761 149654813362429117318605571)
      ·
        refine ⟨224482220043643675977908357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149654813362429117318605571 224482220043643675977908357)
        ·
          refine ⟨42090416258183189245857817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224482220043643675977908357 42090416258183189245857817)
          ·
            refine ⟨31567812193637391934393363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42090416258183189245857817 31567812193637391934393363)
            ·
              refine ⟨47351718290456087901590045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31567812193637391934393363 47351718290456087901590045)
              ·
                refine ⟨17756894358921032963096267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47351718290456087901590045 17756894358921032963096267)
                ·
                  refine ⟨26635341538381549444644401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17756894358921032963096267 26635341538381549444644401)
                  ·
                    refine ⟨19976506153786162083483301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26635341538381549444644401 19976506153786162083483301)
                    ·
                      refine ⟨3745594903834905390653119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19976506153786162083483301 3745594903834905390653119)
                      ·
                        rfl

theorem cell23_7294520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_7294520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294520 prefixEnd_7294520 := by exact prefixLift 7294520
  have htrace : WordTrace (prefixWord ++ tailWord_7294520) baseStart_7294520 baseEnd_7294520 := by
    simpa [prefixWord, tailWord_7294520, baseEnd_7294520] using wordTrace_append hprefix tailTrace_7294520
  have hstable : (prefixWord ++ tailWord_7294520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294520).length < 2 ^ (prefixWord ++ tailWord_7294520).sum := by decide
  have hdescent : baseEnd_7294520 < baseStart_7294520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294567 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_7294567 : Nat := 118140960795 + 7294567 * 2 ^ 59
def prefixEnd_7294567 : Nat := 4983230072969 + 3 ^ 40 * 7294567 * 2
def baseEnd_7294567 : Nat := 3745619037425666706765403

theorem tailTrace_7294567 : CollatzResearch.WordTrace tailWord_7294567 prefixEnd_7294567 3745619037425666706765403 := by
  unfold tailWord_7294567
  simp only [CollatzResearch.WordTrace]
  refine ⟨266054715764037046704481955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177369810509358031136321303 266054715764037046704481955)
  ·
    refine ⟨399082073646055570056722933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266054715764037046704481955 399082073646055570056722933)
    ·
      refine ⟨37413944404317709692817775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 399082073646055570056722933 37413944404317709692817775)
      ·
        refine ⟨56120916606476564539226663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37413944404317709692817775 56120916606476564539226663)
        ·
          refine ⟨84181374909714846808839995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56120916606476564539226663 84181374909714846808839995)
          ·
            refine ⟨126272062364572270213259993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84181374909714846808839995 126272062364572270213259993)
            ·
              refine ⟨94704046773429202659944995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126272062364572270213259993 94704046773429202659944995)
              ·
                refine ⟨142056070160143803989917493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94704046773429202659944995 142056070160143803989917493)
                ·
                  refine ⟨13317756577513481624054765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142056070160143803989917493 13317756577513481624054765)
                  ·
                    refine ⟨4994158716567555609020537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13317756577513481624054765 4994158716567555609020537)
                    ·
                      refine ⟨3745619037425666706765403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994158716567555609020537 3745619037425666706765403)
                      ·
                        rfl

theorem cell23_7294567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_7294567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294567 prefixEnd_7294567 := by exact prefixLift 7294567
  have htrace : WordTrace (prefixWord ++ tailWord_7294567) baseStart_7294567 baseEnd_7294567 := by
    simpa [prefixWord, tailWord_7294567, baseEnd_7294567] using wordTrace_append hprefix tailTrace_7294567
  have hstable : (prefixWord ++ tailWord_7294567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294567).length < 2 ^ (prefixWord ++ tailWord_7294567).sum := by decide
  have hdescent : baseEnd_7294567 < baseStart_7294567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294597 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 3, 4, 2]
def baseStart_7294597 : Nat := 118140960795 + 7294597 * 2 ^ 59
def prefixEnd_7294597 : Nat := 4983230072969 + 3 ^ 40 * 7294597 * 2
def baseEnd_7294597 : Nat := 3745634441845301589390265

theorem tailTrace_7294597 : CollatzResearch.WordTrace tailWord_7294597 prefixEnd_7294597 3745634441845301589390265 := by
  unfold tailWord_7294597
  simp only [CollatzResearch.WordTrace]
  refine ⟨266055809953928361828074045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177370539969285574552049363 266055809953928361828074045)
  ·
    refine ⟨99770928732723135685527767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266055809953928361828074045 99770928732723135685527767)
    ·
      refine ⟨149656393099084703528291651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99770928732723135685527767 149656393099084703528291651)
      ·
        refine ⟨224484589648627055292437477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149656393099084703528291651 224484589648627055292437477)
        ·
          refine ⟨42090860559117572867332027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224484589648627055292437477 42090860559117572867332027)
          ·
            refine ⟨63136290838676359300998041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42090860559117572867332027 63136290838676359300998041)
            ·
              refine ⟨47352218129007269475748531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63136290838676359300998041 47352218129007269475748531)
              ·
                refine ⟨71028327193510904213622797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47352218129007269475748531 71028327193510904213622797)
                ·
                  refine ⟨26635622697566589080108549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71028327193510904213622797 26635622697566589080108549)
                  ·
                    refine ⟨4994179255793735452520353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26635622697566589080108549 4994179255793735452520353)
                    ·
                      refine ⟨3745634441845301589390265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994179255793735452520353 3745634441845301589390265)
                      ·
                        rfl

theorem cell23_7294597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_7294597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294597 prefixEnd_7294597 := by exact prefixLift 7294597
  have htrace : WordTrace (prefixWord ++ tailWord_7294597) baseStart_7294597 baseEnd_7294597 := by
    simpa [prefixWord, tailWord_7294597, baseEnd_7294597] using wordTrace_append hprefix tailTrace_7294597
  have hstable : (prefixWord ++ tailWord_7294597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294597).length < 2 ^ (prefixWord ++ tailWord_7294597).sum := by decide
  have hdescent : baseEnd_7294597 < baseStart_7294597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294674 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7294674 : Nat := 118140960795 + 7294674 * 2 ^ 59
def prefixEnd_7294674 : Nat := 4983230072969 + 3 ^ 40 * 7294674 * 2
def baseEnd_7294674 : Nat := 3745673979855697788127411

theorem tailTrace_7294674 : CollatzResearch.WordTrace tailWord_7294674 prefixEnd_7294674 3745673979855697788127411 := by
  unfold tailWord_7294674
  simp only [CollatzResearch.WordTrace]
  refine ⟨66514654593662350994656769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177372412249766269319084717 66514654593662350994656769)
  ·
    refine ⟨49885990945246763245992577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66514654593662350994656769 49885990945246763245992577)
    ·
      refine ⟨37414493208935072434494433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49885990945246763245992577 37414493208935072434494433)
      ·
        refine ⟨28060869906701304325870825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37414493208935072434494433 28060869906701304325870825)
        ·
          refine ⟨21045652430025978244403119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28060869906701304325870825 21045652430025978244403119)
          ·
            refine ⟨31568478645038967366604679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21045652430025978244403119 31568478645038967366604679)
            ·
              refine ⟨47352717967558451049907019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31568478645038967366604679 47352717967558451049907019)
              ·
                refine ⟨71029076951337676574860529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47352717967558451049907019 71029076951337676574860529)
                ·
                  refine ⟨53271807713503257431145397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71029076951337676574860529 53271807713503257431145397)
                  ·
                    refine ⟨4994231973140930384169881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53271807713503257431145397 4994231973140930384169881)
                    ·
                      refine ⟨3745673979855697788127411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994231973140930384169881 3745673979855697788127411)
                      ·
                        rfl

theorem cell23_7294674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7294674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294674 prefixEnd_7294674 := by exact prefixLift 7294674
  have htrace : WordTrace (prefixWord ++ tailWord_7294674) baseStart_7294674 baseEnd_7294674 := by
    simpa [prefixWord, tailWord_7294674, baseEnd_7294674] using wordTrace_append hprefix tailTrace_7294674
  have hstable : (prefixWord ++ tailWord_7294674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294674).length < 2 ^ (prefixWord ++ tailWord_7294674).sum := by decide
  have hdescent : baseEnd_7294674 < baseStart_7294674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294764 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 1, 5, 2]
def baseStart_7294764 : Nat := 118140960795 + 7294764 * 2 ^ 59
def prefixEnd_7294764 : Nat := 4983230072969 + 3 ^ 40 * 7294764 * 2
def baseEnd_7294764 : Nat := 3745720193114602436001997

theorem tailTrace_7294764 : CollatzResearch.WordTrace tailWord_7294764 prefixEnd_7294764 3745720193114602436001997 := by
  unfold tailWord_7294764
  simp only [CollatzResearch.WordTrace]
  refine ⟨133030950472161674674701673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177374600629548899566268897 133030950472161674674701673)
  ·
    refine ⟨99773212854121256006026255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133030950472161674674701673 99773212854121256006026255)
    ·
      refine ⟨149659819281181884009039383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99773212854121256006026255 149659819281181884009039383)
      ·
        refine ⟨224489728921772826013559075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149659819281181884009039383 224489728921772826013559075)
        ·
          refine ⟨336734593382659239020338613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224489728921772826013559075 336734593382659239020338613)
          ·
            refine ⟨31568868129624303658156745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 336734593382659239020338613 31568868129624303658156745)
            ·
              refine ⟨23676651097218227743617559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31568868129624303658156745 23676651097218227743617559)
              ·
                refine ⟨35514976645827341615426339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23676651097218227743617559 35514976645827341615426339)
                ·
                  refine ⟨53272464968741012423139509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35514976645827341615426339 53272464968741012423139509)
                  ·
                    refine ⟨4994293590819469914669329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53272464968741012423139509 4994293590819469914669329)
                    ·
                      refine ⟨3745720193114602436001997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994293590819469914669329 3745720193114602436001997)
                      ·
                        rfl

theorem cell23_7294764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_7294764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294764 prefixEnd_7294764 := by exact prefixLift 7294764
  have htrace : WordTrace (prefixWord ++ tailWord_7294764) baseStart_7294764 baseEnd_7294764 := by
    simpa [prefixWord, tailWord_7294764, baseEnd_7294764] using wordTrace_append hprefix tailTrace_7294764
  have hstable : (prefixWord ++ tailWord_7294764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294764).length < 2 ^ (prefixWord ++ tailWord_7294764).sum := by decide
  have hdescent : baseEnd_7294764 < baseStart_7294764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294781 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7294781 : Nat := 118140960795 + 7294781 * 2 ^ 59
def prefixEnd_7294781 : Nat := 4983230072969 + 3 ^ 40 * 7294781 * 2
def baseEnd_7294781 : Nat := 3745728922285728869489419

theorem tailTrace_7294781 : CollatzResearch.WordTrace tailWord_7294781 prefixEnd_7294781 3745728922285728869489419 := by
  unfold tailWord_7294781
  simp only [CollatzResearch.WordTrace]
  refine ⟨266062520985261761252772197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177375013990174507501848131 266062520985261761252772197)
  ·
    refine ⟨49886722684736580234894787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266062520985261761252772197 49886722684736580234894787)
    ·
      refine ⟨74830084027104870352342181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49886722684736580234894787 74830084027104870352342181)
      ·
        refine ⟨14030640755082163191064159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74830084027104870352342181 14030640755082163191064159)
        ·
          refine ⟨21045961132623244786596239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14030640755082163191064159 21045961132623244786596239)
          ·
            refine ⟨31568941698934867179894359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21045961132623244786596239 31568941698934867179894359)
            ·
              refine ⟨47353412548402300769841539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31568941698934867179894359 47353412548402300769841539)
              ·
                refine ⟨71030118822603451154762309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47353412548402300769841539 71030118822603451154762309)
                ·
                  refine ⟨13318147279238147091517933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71030118822603451154762309 13318147279238147091517933)
                  ·
                    refine ⟨4994305229714305159319225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13318147279238147091517933 4994305229714305159319225)
                    ·
                      refine ⟨3745728922285728869489419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994305229714305159319225 3745728922285728869489419)
                      ·
                        rfl

theorem cell23_7294781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7294781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294781 prefixEnd_7294781 := by exact prefixLift 7294781
  have htrace : WordTrace (prefixWord ++ tailWord_7294781) baseStart_7294781 baseEnd_7294781 := by
    simpa [prefixWord, tailWord_7294781, baseEnd_7294781] using wordTrace_append hprefix tailTrace_7294781
  have hstable : (prefixWord ++ tailWord_7294781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294781).length < 2 ^ (prefixWord ++ tailWord_7294781).sum := by decide
  have hdescent : baseEnd_7294781 < baseStart_7294781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294824 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7294824 : Nat := 118140960795 + 7294824 * 2 ^ 59
def prefixEnd_7294824 : Nat := 4983230072969 + 3 ^ 40 * 7294824 * 2
def baseEnd_7294824 : Nat := 3745751001953872201251721

theorem tailTrace_7294824 : CollatzResearch.WordTrace tailWord_7294824 prefixEnd_7294824 3745751001953872201251721 := by
  unfold tailWord_7294824
  simp only [CollatzResearch.WordTrace]
  refine ⟨133032044662052989798293763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177376059549403986397725017 133032044662052989798293763)
  ·
    refine ⟨199548066993079484697440645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133032044662052989798293763 199548066993079484697440645)
    ·
      refine ⟨37415262561202403380770121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199548066993079484697440645 37415262561202403380770121)
      ·
        refine ⟨28061446920901802535577591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37415262561202403380770121 28061446920901802535577591)
        ·
          refine ⟨42092170381352703803366387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28061446920901802535577591 42092170381352703803366387)
          ·
            refine ⟨63138255572029055705049581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42092170381352703803366387 63138255572029055705049581)
            ·
              refine ⟨23676845839510895889393593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63138255572029055705049581 23676845839510895889393593)
              ·
                refine ⟨17757634379633171917045195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23676845839510895889393593 17757634379633171917045195)
                ·
                  refine ⟨26636451569449757875567793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17757634379633171917045195 26636451569449757875567793)
                  ·
                    refine ⟨19977338677087318406675845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26636451569449757875567793 19977338677087318406675845)
                    ·
                      refine ⟨3745751001953872201251721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19977338677087318406675845 3745751001953872201251721)
                      ·
                        rfl

theorem cell23_7294824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7294824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294824 prefixEnd_7294824 := by exact prefixLift 7294824
  have htrace : WordTrace (prefixWord ++ tailWord_7294824) baseStart_7294824 baseEnd_7294824 := by
    simpa [prefixWord, tailWord_7294824, baseEnd_7294824] using wordTrace_append hprefix tailTrace_7294824
  have hstable : (prefixWord ++ tailWord_7294824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294824).length < 2 ^ (prefixWord ++ tailWord_7294824).sum := by decide
  have hdescent : baseEnd_7294824 < baseStart_7294824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294871 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 3, 3, 2]
def baseStart_7294871 : Nat := 118140960795 + 7294871 * 2 ^ 59
def prefixEnd_7294871 : Nat := 4983230072969 + 3 ^ 40 * 7294871 * 2
def baseEnd_7294871 : Nat := 3745775135544633517364005

theorem tailTrace_7294871 : CollatzResearch.WordTrace tailWord_7294871 prefixEnd_7294871 3745775135544633517364005 := by
  unfold tailWord_7294871
  simp only [CollatzResearch.WordTrace]
  refine ⟨266065803554935706623548467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177377202369957137749032311 266065803554935706623548467)
  ·
    refine ⟨399098705332403559935322701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266065803554935706623548467 399098705332403559935322701)
    ·
      refine ⟨149662014499651334975746013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399098705332403559935322701 149662014499651334975746013)
      ·
        refine ⟨56123255437369250615904755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149662014499651334975746013 56123255437369250615904755)
        ·
          refine ⟨84184883156053875923857133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56123255437369250615904755 84184883156053875923857133)
          ·
            refine ⟨31569331183520203471446425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84184883156053875923857133 31569331183520203471446425)
            ·
              refine ⟨23676998387640152603584819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31569331183520203471446425 23676998387640152603584819)
              ·
                refine ⟨35515497581460228905377229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23676998387640152603584819 35515497581460228905377229)
                ·
                  refine ⟨13318311593047585839516461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35515497581460228905377229 13318311593047585839516461)
                  ·
                    refine ⟨4994366847392844689818673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13318311593047585839516461 4994366847392844689818673)
                    ·
                      refine ⟨3745775135544633517364005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994366847392844689818673 3745775135544633517364005)
                      ·
                        rfl

theorem cell23_7294871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_7294871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294871 prefixEnd_7294871 := by exact prefixLift 7294871
  have htrace : WordTrace (prefixWord ++ tailWord_7294871) baseStart_7294871 baseEnd_7294871 := by
    simpa [prefixWord, tailWord_7294871, baseEnd_7294871] using wordTrace_append hprefix tailTrace_7294871
  have hstable : (prefixWord ++ tailWord_7294871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294871).length < 2 ^ (prefixWord ++ tailWord_7294871).sum := by decide
  have hdescent : baseEnd_7294871 < baseStart_7294871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294882 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_7294882 : Nat := 118140960795 + 7294882 * 2 ^ 59
def prefixEnd_7294882 : Nat := 4983230072969 + 3 ^ 40 * 7294882 * 2
def baseEnd_7294882 : Nat := 3745780783831832974326455

theorem tailTrace_7294882 : CollatzResearch.WordTrace tailWord_7294882 prefixEnd_7294882 3745780783831832974326455 := by
  unfold tailWord_7294882
  simp only [CollatzResearch.WordTrace]
  refine ⟨66516551189473963875549725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177377469838597237001465933 66516551189473963875549725)
  ·
    refine ⟨24943706696052736453331147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66516551189473963875549725 24943706696052736453331147)
    ·
      refine ⟨37415560044079104679996721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24943706696052736453331147 37415560044079104679996721)
      ·
        refine ⟨28061670033059328509997541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37415560044079104679996721 28061670033059328509997541)
        ·
          refine ⟨5261563131198624095624539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28061670033059328509997541 5261563131198624095624539)
          ·
            refine ⟨7892344696797936143436809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261563131198624095624539 7892344696797936143436809)
            ·
              refine ⟨5919258522598452107577607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7892344696797936143436809 5919258522598452107577607)
              ·
                refine ⟨8878887783897678161366411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919258522598452107577607 8878887783897678161366411)
                ·
                  refine ⟨13318331675846517242049617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8878887783897678161366411 13318331675846517242049617)
                  ·
                    refine ⟨9988748756884887931537213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13318331675846517242049617 9988748756884887931537213)
                    ·
                      refine ⟨3745780783831832974326455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9988748756884887931537213 3745780783831832974326455)
                      ·
                        rfl

theorem cell23_7294882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_7294882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294882 prefixEnd_7294882 := by exact prefixLift 7294882
  have htrace : WordTrace (prefixWord ++ tailWord_7294882) baseStart_7294882 baseEnd_7294882 := by
    simpa [prefixWord, tailWord_7294882, baseEnd_7294882] using wordTrace_append hprefix tailTrace_7294882
  have hstable : (prefixWord ++ tailWord_7294882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294882).length < 2 ^ (prefixWord ++ tailWord_7294882).sum := by decide
  have hdescent : baseEnd_7294882 < baseStart_7294882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294907 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 7]
def baseStart_7294907 : Nat := 118140960795 + 7294907 * 2 ^ 59
def prefixEnd_7294907 : Nat := 4983230072969 + 3 ^ 40 * 7294907 * 2
def baseEnd_7294907 : Nat := 416199291205355041834871

theorem tailTrace_7294907 : CollatzResearch.WordTrace tailWord_7294907 prefixEnd_7294907 416199291205355041834871 := by
  unfold tailWord_7294907
  simp only [CollatzResearch.WordTrace]
  refine ⟨266067116582805284771858975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177378077721870189847905983 266067116582805284771858975)
  ·
    refine ⟨399100674874207927157788463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266067116582805284771858975 399100674874207927157788463)
    ·
      refine ⟨598651012311311890736682695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399100674874207927157788463 598651012311311890736682695)
      ·
        refine ⟨897976518466967836105024043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598651012311311890736682695 897976518466967836105024043)
        ·
          refine ⟨1346964777700451754157536065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897976518466967836105024043 1346964777700451754157536065)
          ·
            refine ⟨1010223583275338815618152049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346964777700451754157536065 1010223583275338815618152049)
            ·
              refine ⟨757667687456504111713614037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010223583275338815618152049 757667687456504111713614037)
              ·
                refine ⟨17757836424761815118287829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 757667687456504111713614037 17757836424761815118287829)
                ·
                  refine ⟨416199291205355041834871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17757836424761815118287829 416199291205355041834871)
                  ·
                    rfl

theorem cell23_7294907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 7].length) (baseStart_7294907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294907 prefixEnd_7294907 := by exact prefixLift 7294907
  have htrace : WordTrace (prefixWord ++ tailWord_7294907) baseStart_7294907 baseEnd_7294907 := by
    simpa [prefixWord, tailWord_7294907, baseEnd_7294907] using wordTrace_append hprefix tailTrace_7294907
  have hstable : (prefixWord ++ tailWord_7294907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294907).length < 2 ^ (prefixWord ++ tailWord_7294907).sum := by decide
  have hdescent : baseEnd_7294907 < baseStart_7294907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294924 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 7]
def baseStart_7294924 : Nat := 118140960795 + 7294924 * 2 ^ 59
def prefixEnd_7294924 : Nat := 4983230072969 + 3 ^ 40 * 7294924 * 2
def baseEnd_7294924 : Nat := 416200261113257978889029

theorem tailTrace_7294924 : CollatzResearch.WordTrace tailWord_7294924 prefixEnd_7294924 416200261113257978889029 := by
  unfold tailWord_7294924
  simp only [CollatzResearch.WordTrace]
  refine ⟨133033868311871848337613913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177378491082495797783485217 133033868311871848337613913)
  ·
    refine ⟨99775401233903886253210435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133033868311871848337613913 99775401233903886253210435)
    ·
      refine ⟨149663101850855829379815653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99775401233903886253210435 149663101850855829379815653)
      ·
        refine ⟨28061831597035468008715435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149663101850855829379815653 28061831597035468008715435)
        ·
          refine ⟨42092747395553202013073153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28061831597035468008715435 42092747395553202013073153)
          ·
            refine ⟨31569560546664901509804865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42092747395553202013073153 31569560546664901509804865)
            ·
              refine ⟨23677170409998676132353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31569560546664901509804865 23677170409998676132353649)
              ·
                refine ⟨17757877807499007099265237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23677170409998676132353649 17757877807499007099265237)
                ·
                  refine ⟨416200261113257978889029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17757877807499007099265237 416200261113257978889029)
                  ·
                    rfl

theorem cell23_7294924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_7294924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294924 prefixEnd_7294924 := by exact prefixLift 7294924
  have htrace : WordTrace (prefixWord ++ tailWord_7294924) baseStart_7294924 baseEnd_7294924 := by
    simpa [prefixWord, tailWord_7294924, baseEnd_7294924] using wordTrace_append hprefix tailTrace_7294924
  have hstable : (prefixWord ++ tailWord_7294924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294924).length < 2 ^ (prefixWord ++ tailWord_7294924).sum := by decide
  have hdescent : baseEnd_7294924 < baseStart_7294924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295011 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 3]
def baseStart_7295011 : Nat := 118140960795 + 7295011 * 2 ^ 59
def prefixEnd_7295011 : Nat := 4983230072969 + 3 ^ 40 * 7295011 * 2
def baseEnd_7295011 : Nat := 3745847022836262969613361

theorem tailTrace_7295011 : CollatzResearch.WordTrace tailWord_7295011 prefixEnd_7295011 3745847022836262969613361 := by
  unfold tailWord_7295011
  simp only [CollatzResearch.WordTrace]
  refine ⟨266070909774428510533644887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177380606516285673689096591 266070909774428510533644887)
  ·
    refine ⟨399106364661642765800467331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266070909774428510533644887 399106364661642765800467331)
    ·
      refine ⟨598659546992464148700700997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399106364661642765800467331 598659546992464148700700997)
      ·
        refine ⟨112248665061087027881381437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598659546992464148700700997 112248665061087027881381437)
        ·
          refine ⟨42093249397907635455518039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112248665061087027881381437 42093249397907635455518039)
          ·
            refine ⟨63139874096861453183277059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42093249397907635455518039 63139874096861453183277059)
            ·
              refine ⟨94709811145292179774915589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63139874096861453183277059 94709811145292179774915589)
              ·
                refine ⟨17758089589742283707796673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94709811145292179774915589 17758089589742283707796673)
                ·
                  refine ⟨13318567192306712780847505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17758089589742283707796673 13318567192306712780847505)
                  ·
                    refine ⟨9988925394230034585635629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13318567192306712780847505 9988925394230034585635629)
                    ·
                      refine ⟨3745847022836262969613361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9988925394230034585635629 3745847022836262969613361)
                      ·
                        rfl

theorem cell23_7295011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_7295011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295011 prefixEnd_7295011 := by exact prefixLift 7295011
  have htrace : WordTrace (prefixWord ++ tailWord_7295011) baseStart_7295011 baseEnd_7295011 := by
    simpa [prefixWord, tailWord_7295011, baseEnd_7295011] using wordTrace_append hprefix tailTrace_7295011
  have hstable : (prefixWord ++ tailWord_7295011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295011).length < 2 ^ (prefixWord ++ tailWord_7295011).sum := by decide
  have hdescent : baseEnd_7295011 < baseStart_7295011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295051 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 1, 5, 2]
def baseStart_7295051 : Nat := 118140960795 + 7295051 * 2 ^ 59
def prefixEnd_7295051 : Nat := 4983230072969 + 3 ^ 40 * 7295051 * 2
def baseEnd_7295051 : Nat := 3745867562062442813113177

theorem tailTrace_7295051 : CollatzResearch.WordTrace tailWord_7295051 prefixEnd_7295051 3745867562062442813113177 := by
  unfold tailWord_7295051
  simp only [CollatzResearch.WordTrace]
  refine ⟨266072368694283597365101007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177381579129522398243400671 266072368694283597365101007)
  ·
    refine ⟨399108553041425396047651511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266072368694283597365101007 399108553041425396047651511)
    ·
      refine ⟨598662829562138094071477267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399108553041425396047651511 598662829562138094071477267)
      ·
        refine ⟨897994244343207141107215901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598662829562138094071477267 897994244343207141107215901)
        ·
          refine ⟨336747841628702677915205963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 897994244343207141107215901 336747841628702677915205963)
          ·
            refine ⟨505121762443054016872808945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336747841628702677915205963 505121762443054016872808945)
            ·
              refine ⟨378841321832290512654606709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505121762443054016872808945 378841321832290512654606709)
              ·
                refine ⟨35516373921777235561369379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378841321832290512654606709 35516373921777235561369379)
                ·
                  refine ⟨53274560882665853342054069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35516373921777235561369379 53274560882665853342054069)
                  ·
                    refine ⟨4994490082749923750817569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53274560882665853342054069 4994490082749923750817569)
                    ·
                      refine ⟨3745867562062442813113177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994490082749923750817569 3745867562062442813113177)
                      ·
                        rfl

theorem cell23_7295051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5, 2].length) (baseStart_7295051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295051 prefixEnd_7295051 := by exact prefixLift 7295051
  have htrace : WordTrace (prefixWord ++ tailWord_7295051) baseStart_7295051 baseEnd_7295051 := by
    simpa [prefixWord, tailWord_7295051, baseEnd_7295051] using wordTrace_append hprefix tailTrace_7295051
  have hstable : (prefixWord ++ tailWord_7295051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295051).length < 2 ^ (prefixWord ++ tailWord_7295051).sum := by decide
  have hdescent : baseEnd_7295051 < baseStart_7295051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295075 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 1, 1, 3]
def baseStart_7295075 : Nat := 118140960795 + 7295075 * 2 ^ 59
def prefixEnd_7295075 : Nat := 4983230072969 + 3 ^ 40 * 7295075 * 2
def baseEnd_7295075 : Nat := 3745879885598150719213067

theorem tailTrace_7295075 : CollatzResearch.WordTrace tailWord_7295075 prefixEnd_7295075 3745879885598150719213067 := by
  unfold tailWord_7295075
  simp only [CollatzResearch.WordTrace]
  refine ⟨266073244046196649463974679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177382162697464432975983119 266073244046196649463974679)
  ·
    refine ⟨399109866069294974195962019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266073244046196649463974679 399109866069294974195962019)
    ·
      refine ⟨598664799103942461293943029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399109866069294974195962019 598664799103942461293943029)
      ·
        refine ⟨56124824915994605746307159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 598664799103942461293943029 56124824915994605746307159)
        ·
          refine ⟨84187237373991908619460739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56124824915994605746307159 84187237373991908619460739)
          ·
            refine ⟨126280856060987862929191109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84187237373991908619460739 126280856060987862929191109)
            ·
              refine ⟨23677660511435224299223333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126280856060987862929191109 23677660511435224299223333)
              ·
                refine ⟨4439561345894104556104375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23677660511435224299223333 4439561345894104556104375)
                ·
                  refine ⟨6659342018841156834156563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439561345894104556104375 6659342018841156834156563)
                  ·
                    refine ⟨9989013028261735251234845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659342018841156834156563 9989013028261735251234845)
                    ·
                      refine ⟨3745879885598150719213067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9989013028261735251234845 3745879885598150719213067)
                      ·
                        rfl

theorem cell23_7295075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_7295075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295075 prefixEnd_7295075 := by exact prefixLift 7295075
  have htrace : WordTrace (prefixWord ++ tailWord_7295075) baseStart_7295075 baseEnd_7295075 := by
    simpa [prefixWord, tailWord_7295075, baseEnd_7295075] using wordTrace_append hprefix tailTrace_7295075
  have hstable : (prefixWord ++ tailWord_7295075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295075).length < 2 ^ (prefixWord ++ tailWord_7295075).sum := by decide
  have hdescent : baseEnd_7295075 < baseStart_7295075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295111 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_7295111 : Nat := 118140960795 + 7295111 * 2 ^ 59
def prefixEnd_7295111 : Nat := 4983230072969 + 3 ^ 40 * 7295111 * 2
def baseEnd_7295111 : Nat := 3745898370901712578362901

theorem tailTrace_7295111 : CollatzResearch.WordTrace tailWord_7295111 prefixEnd_7295111 3745898370901712578362901 := by
  unfold tailWord_7295111
  simp only [CollatzResearch.WordTrace]
  refine ⟨266074557074066227612285187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177383038049377485074856791 266074557074066227612285187)
  ·
    refine ⟨399111835611099341418427781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266074557074066227612285187 399111835611099341418427781)
    ·
      refine ⟨74833469177081126515955209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399111835611099341418427781 74833469177081126515955209)
      ·
        refine ⟨56125101882810844886966407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74833469177081126515955209 56125101882810844886966407)
        ·
          refine ⟨84187652824216267330449611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56125101882810844886966407 84187652824216267330449611)
          ·
            refine ⟨126281479236324400995674417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84187652824216267330449611 126281479236324400995674417)
            ·
              refine ⟨94711109427243300746755813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126281479236324400995674417 94711109427243300746755813)
              ·
                refine ⟨17758333017608118890016715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94711109427243300746755813 17758333017608118890016715)
                ·
                  refine ⟨26637499526412178335025073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17758333017608118890016715 26637499526412178335025073)
                  ·
                    refine ⟨19978124644809133751268805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26637499526412178335025073 19978124644809133751268805)
                    ·
                      refine ⟨3745898370901712578362901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19978124644809133751268805 3745898370901712578362901)
                      ·
                        rfl

theorem cell23_7295111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_7295111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295111 prefixEnd_7295111 := by exact prefixLift 7295111
  have htrace : WordTrace (prefixWord ++ tailWord_7295111) baseStart_7295111 baseEnd_7295111 := by
    simpa [prefixWord, tailWord_7295111, baseEnd_7295111] using wordTrace_append hprefix tailTrace_7295111
  have hstable : (prefixWord ++ tailWord_7295111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295111).length < 2 ^ (prefixWord ++ tailWord_7295111).sum := by decide
  have hdescent : baseEnd_7295111 < baseStart_7295111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295138 : List Nat := [3, 3, 1, 3, 1, 2, 2, 8]
def baseStart_7295138 : Nat := 118140960795 + 7295138 * 2 ^ 59
def prefixEnd_7295138 : Nat := 4983230072969 + 3 ^ 40 * 7295138 * 2
def baseEnd_7295138 : Nat := 138737490180717924915751

theorem tailTrace_7295138 : CollatzResearch.WordTrace tailWord_7295138 prefixEnd_7295138 138737490180717924915751 := by
  unfold tailWord_7295138
  simp only [CollatzResearch.WordTrace]
  refine ⟨66518885461242102805879517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177383694563312274149012045 66518885461242102805879517)
  ·
    refine ⟨24944582047965788552204819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66518885461242102805879517 24944582047965788552204819)
    ·
      refine ⟨37416873071948682828307229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24944582047965788552204819 37416873071948682828307229)
      ·
        refine ⟨14031327401980756060615211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37416873071948682828307229 14031327401980756060615211)
        ·
          refine ⟨21046991102971134090922817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14031327401980756060615211 21046991102971134090922817)
          ·
            refine ⟨15785243327228350568192113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21046991102971134090922817 15785243327228350568192113)
            ·
              refine ⟨11838932495421262926144085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15785243327228350568192113 11838932495421262926144085)
              ·
                refine ⟨138737490180717924915751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11838932495421262926144085 138737490180717924915751)
                ·
                  rfl

theorem cell23_7295138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_7295138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295138 prefixEnd_7295138 := by exact prefixLift 7295138
  have htrace : WordTrace (prefixWord ++ tailWord_7295138) baseStart_7295138 baseEnd_7295138 := by
    simpa [prefixWord, tailWord_7295138, baseEnd_7295138] using wordTrace_append hprefix tailTrace_7295138
  have hstable : (prefixWord ++ tailWord_7295138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295138).length < 2 ^ (prefixWord ++ tailWord_7295138).sum := by decide
  have hdescent : baseEnd_7295138 < baseStart_7295138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295169 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7295169 : Nat := 118140960795 + 7295169 * 2 ^ 59
def prefixEnd_7295169 : Nat := 4983230072969 + 3 ^ 40 * 7295169 * 2
def baseEnd_7295169 : Nat := 3745928152779673351437635

theorem tailTrace_7295169 : CollatzResearch.WordTrace tailWord_7295169 prefixEnd_7295169 3745928152779673351437635 := by
  unfold tailWord_7295169
  simp only [CollatzResearch.WordTrace]
  refine ⟨266076672507856103517896561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177384448338570735678597707 266076672507856103517896561)
  ·
    refine ⟨199557504380892077638422421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266076672507856103517896561 199557504380892077638422421)
    ·
      refine ⟨9354258017854316139301051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199557504380892077638422421 9354258017854316139301051)
      ·
        refine ⟨14031387026781474208951577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9354258017854316139301051 14031387026781474208951577)
        ·
          refine ⟨10523540270086105656713683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14031387026781474208951577 10523540270086105656713683)
          ·
            refine ⟨15785310405129158485070525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523540270086105656713683 15785310405129158485070525)
            ·
              refine ⟨5919491401923434431901447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15785310405129158485070525 5919491401923434431901447)
              ·
                refine ⟨8879237102885151647852171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919491401923434431901447 8879237102885151647852171)
                ·
                  refine ⟨13318855654327727471778257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879237102885151647852171 13318855654327727471778257)
                  ·
                    refine ⟨9989141740745795603833693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13318855654327727471778257 9989141740745795603833693)
                    ·
                      refine ⟨3745928152779673351437635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9989141740745795603833693 3745928152779673351437635)
                      ·
                        rfl

theorem cell23_7295169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7295169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295169 prefixEnd_7295169 := by exact prefixLift 7295169
  have htrace : WordTrace (prefixWord ++ tailWord_7295169) baseStart_7295169 baseEnd_7295169 := by
    simpa [prefixWord, tailWord_7295169, baseEnd_7295169] using wordTrace_append hprefix tailTrace_7295169
  have hstable : (prefixWord ++ tailWord_7295169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295169).length < 2 ^ (prefixWord ++ tailWord_7295169).sum := by decide
  have hdescent : baseEnd_7295169 < baseStart_7295169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295182 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_7295182 : Nat := 118140960795 + 7295182 * 2 ^ 59
def prefixEnd_7295182 : Nat := 4983230072969 + 3 ^ 40 * 7295182 * 2
def baseEnd_7295182 : Nat := 3745934828028181800575075

theorem tailTrace_7295182 : CollatzResearch.WordTrace tailWord_7295182 prefixEnd_7295182 3745934828028181800575075 := by
  unfold tailWord_7295182
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259643332101125842264975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177384764437872671158746533 33259643332101125842264975)
  ·
    refine ⟨49889464998151688763397463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33259643332101125842264975 49889464998151688763397463)
    ·
      refine ⟨74834197497227533145096195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49889464998151688763397463 74834197497227533145096195)
      ·
        refine ⟨112251296245841299717644293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74834197497227533145096195 112251296245841299717644293)
        ·
          refine ⟨21047118046095243697058305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112251296245841299717644293 21047118046095243697058305)
          ·
            refine ⟨15785338534571432772793729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21047118046095243697058305 15785338534571432772793729)
            ·
              refine ⟨11839003900928574579595297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15785338534571432772793729 11839003900928574579595297)
              ·
                refine ⟨8879252925696430934696473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11839003900928574579595297 8879252925696430934696473)
                ·
                  refine ⟨6659439694272323201022355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8879252925696430934696473 6659439694272323201022355)
                  ·
                    refine ⟨9989159541408484801533533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659439694272323201022355 9989159541408484801533533)
                    ·
                      refine ⟨3745934828028181800575075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9989159541408484801533533 3745934828028181800575075)
                      ·
                        rfl

theorem cell23_7295182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_7295182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295182 prefixEnd_7295182 := by exact prefixLift 7295182
  have htrace : WordTrace (prefixWord ++ tailWord_7295182) baseStart_7295182 baseEnd_7295182 := by
    simpa [prefixWord, tailWord_7295182, baseEnd_7295182] using wordTrace_append hprefix tailTrace_7295182
  have hstable : (prefixWord ++ tailWord_7295182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295182).length < 2 ^ (prefixWord ++ tailWord_7295182).sum := by decide
  have hdescent : baseEnd_7295182 < baseStart_7295182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295205 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7295205 : Nat := 118140960795 + 7295205 * 2 ^ 59
def prefixEnd_7295205 : Nat := 4983230072969 + 3 ^ 40 * 7295205 * 2
def baseEnd_7295205 : Nat := 3745946638083235210587469

theorem tailTrace_7295205 : CollatzResearch.WordTrace tailWord_7295205 prefixEnd_7295205 3745946638083235210587469 := by
  unfold tailWord_7295205
  simp only [CollatzResearch.WordTrace]
  refine ⟨266077985535725681666207069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177385323690483787777471379 266077985535725681666207069)
  ·
    refine ⟨99779244575897130624827651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266077985535725681666207069 99779244575897130624827651)
    ·
      refine ⟨149668866863845695937241477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99779244575897130624827651 149668866863845695937241477)
      ·
        refine ⟨28062912536971067988232777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149668866863845695937241477 28062912536971067988232777)
        ·
          refine ⟨21047184402728300991174583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28062912536971067988232777 21047184402728300991174583)
          ·
            refine ⟨31570776604092451486761875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21047184402728300991174583 31570776604092451486761875)
            ·
              refine ⟨47356164906138677230142813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31570776604092451486761875 47356164906138677230142813)
              ·
                refine ⟨17758561839802003961303555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47356164906138677230142813 17758561839802003961303555)
                ·
                  refine ⟨26637842759703005941955333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17758561839802003961303555 26637842759703005941955333)
                  ·
                    refine ⟨4994595517444313614116625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26637842759703005941955333 4994595517444313614116625)
                    ·
                      refine ⟨3745946638083235210587469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994595517444313614116625 3745946638083235210587469)
                      ·
                        rfl

theorem cell23_7295205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7295205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295205 prefixEnd_7295205 := by exact prefixLift 7295205
  have htrace : WordTrace (prefixWord ++ tailWord_7295205) baseStart_7295205 baseEnd_7295205 := by
    simpa [prefixWord, tailWord_7295205, baseEnd_7295205] using wordTrace_append hprefix tailTrace_7295205
  have hstable : (prefixWord ++ tailWord_7295205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295205).length < 2 ^ (prefixWord ++ tailWord_7295205).sum := by decide
  have hdescent : baseEnd_7295205 < baseStart_7295205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295211 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 7]
def baseStart_7295211 : Nat := 118140960795 + 7295211 * 2 ^ 59
def prefixEnd_7295211 : Nat := 4983230072969 + 3 ^ 40 * 7295211 * 2
def baseEnd_7295211 : Nat := 416216635440795798568049

theorem tailTrace_7295211 : CollatzResearch.WordTrace tailWord_7295211 prefixEnd_7295211 416216635440795798568049 := by
  unfold tailWord_7295211
  simp only [CollatzResearch.WordTrace]
  refine ⟨266078204373703944690925487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177385469582469296460616991 266078204373703944690925487)
  ·
    refine ⟨399117306560555917036388231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266078204373703944690925487 399117306560555917036388231)
    ·
      refine ⟨598675959840833875554582347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399117306560555917036388231 598675959840833875554582347)
      ·
        refine ⟨898013939761250813331873521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598675959840833875554582347 898013939761250813331873521)
        ·
          refine ⟨673510454820938109998905141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898013939761250813331873521 673510454820938109998905141)
          ·
            refine ⟨63141605139462947812397357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 673510454820938109998905141 63141605139462947812397357)
            ·
              refine ⟨23678101927298605429649009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63141605139462947812397357 23678101927298605429649009)
              ·
                refine ⟨17758576445473954072236757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23678101927298605429649009 17758576445473954072236757)
                ·
                  refine ⟨416216635440795798568049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17758576445473954072236757 416216635440795798568049)
                  ·
                    rfl

theorem cell23_7295211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 7].length) (baseStart_7295211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295211 prefixEnd_7295211 := by exact prefixLift 7295211
  have htrace : WordTrace (prefixWord ++ tailWord_7295211) baseStart_7295211 baseEnd_7295211 := by
    simpa [prefixWord, tailWord_7295211, baseEnd_7295211] using wordTrace_append hprefix tailTrace_7295211
  have hstable : (prefixWord ++ tailWord_7295211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295211).length < 2 ^ (prefixWord ++ tailWord_7295211).sum := by decide
  have hdescent : baseEnd_7295211 < baseStart_7295211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295239 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7295239 : Nat := 118140960795 + 7295239 * 2 ^ 59
def prefixEnd_7295239 : Nat := 4983230072969 + 3 ^ 40 * 7295239 * 2
def baseEnd_7295239 : Nat := 3745964096425488077562313

theorem tailTrace_7295239 : CollatzResearch.WordTrace tailWord_7295239 prefixEnd_7295239 3745964096425488077562313 := by
  unfold tailWord_7295239
  simp only [CollatzResearch.WordTrace]
  refine ⟨266079225617602505472944771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177386150411735003648629847 266079225617602505472944771)
  ·
    refine ⟨399118838426403758209417157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266079225617602505472944771 399118838426403758209417157)
    ·
      refine ⟨74834782204950704664265717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399118838426403758209417157 74834782204950704664265717)
      ·
        refine ⟨7015760831714128562274911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74834782204950704664265717 7015760831714128562274911)
        ·
          refine ⟨10523641247571192843412367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015760831714128562274911 10523641247571192843412367)
          ·
            refine ⟨15785461871356789265118551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523641247571192843412367 15785461871356789265118551)
            ·
              refine ⟨23678192807035183897677827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785461871356789265118551 23678192807035183897677827)
              ·
                refine ⟨35517289210552775846516741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23678192807035183897677827 35517289210552775846516741)
                ·
                  refine ⟨6659491726978645471221889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35517289210552775846516741 6659491726978645471221889)
                  ·
                    refine ⟨4994618795233984103416417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6659491726978645471221889 4994618795233984103416417)
                    ·
                      refine ⟨3745964096425488077562313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994618795233984103416417 3745964096425488077562313)
                      ·
                        rfl

theorem cell23_7295239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7295239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295239 prefixEnd_7295239 := by exact prefixLift 7295239
  have htrace : WordTrace (prefixWord ++ tailWord_7295239) baseStart_7295239 baseEnd_7295239 := by
    simpa [prefixWord, tailWord_7295239, baseEnd_7295239] using wordTrace_append hprefix tailTrace_7295239
  have hstable : (prefixWord ++ tailWord_7295239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295239).length < 2 ^ (prefixWord ++ tailWord_7295239).sum := by decide
  have hdescent : baseEnd_7295239 < baseStart_7295239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295251 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5]
def baseStart_7295251 : Nat := 118140960795 + 7295251 * 2 ^ 59
def prefixEnd_7295251 : Nat := 4983230072969 + 3 ^ 40 * 7295251 * 2
def baseEnd_7295251 : Nat := 3745970258193342030612257

theorem tailTrace_7295251 : CollatzResearch.WordTrace tailWord_7295251 prefixEnd_7295251 3745970258193342030612257 := by
  unfold tailWord_7295251
  simp only [CollatzResearch.WordTrace]
  refine ⟨266079663293559031522381607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177386442195706021014921071 266079663293559031522381607)
  ·
    refine ⟨399119494940338547283572411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266079663293559031522381607 399119494940338547283572411)
    ·
      refine ⟨598679242410507820925358617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399119494940338547283572411 598679242410507820925358617)
      ·
        refine ⟨449009431807880865694018963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598679242410507820925358617 449009431807880865694018963)
        ·
          refine ⟨673514147711821298541028445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449009431807880865694018963 673514147711821298541028445)
          ·
            refine ⟨252567805391932986952885667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673514147711821298541028445 252567805391932986952885667)
            ·
              refine ⟨378851708087899480429328501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252567805391932986952885667 378851708087899480429328501)
              ·
                refine ⟨35517347633240576290249547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378851708087899480429328501 35517347633240576290249547)
                ·
                  refine ⟨53276021449860864435374321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35517347633240576290249547 53276021449860864435374321)
                  ·
                    refine ⟨39957016087395648326530741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53276021449860864435374321 39957016087395648326530741)
                    ·
                      refine ⟨3745970258193342030612257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39957016087395648326530741 3745970258193342030612257)
                      ·
                        rfl

theorem cell23_7295251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_7295251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295251 prefixEnd_7295251 := by exact prefixLift 7295251
  have htrace : WordTrace (prefixWord ++ tailWord_7295251) baseStart_7295251 baseEnd_7295251 := by
    simpa [prefixWord, tailWord_7295251, baseEnd_7295251] using wordTrace_append hprefix tailTrace_7295251
  have hstable : (prefixWord ++ tailWord_7295251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295251).length < 2 ^ (prefixWord ++ tailWord_7295251).sum := by decide
  have hdescent : baseEnd_7295251 < baseStart_7295251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295288 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 5, 4]
def baseStart_7295288 : Nat := 118140960795 + 7295288 * 2 ^ 59
def prefixEnd_7295288 : Nat := 4983230072969 + 3 ^ 40 * 7295288 * 2
def baseEnd_7295288 : Nat := 1248663085659186128616529

theorem tailTrace_7295288 : CollatzResearch.WordTrace tailWord_7295288 prefixEnd_7295288 1248663085659186128616529 := by
  unfold tailWord_7295288
  simp only [CollatzResearch.WordTrace]
  refine ⟨133040506397212493420739259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177387341862949991227652345 133040506397212493420739259)
  ·
    refine ⟨199560759595818740131108889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133040506397212493420739259 199560759595818740131108889)
    ·
      refine ⟨149670569696864055098331667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199560759595818740131108889 149670569696864055098331667)
      ·
        refine ⟨224505854545296082647497501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149670569696864055098331667 224505854545296082647497501)
        ·
          refine ⟨84189695454486030992811563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224505854545296082647497501 84189695454486030992811563)
          ·
            refine ⟨126284543181729046489217345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84189695454486030992811563 126284543181729046489217345)
            ·
              refine ⟨94713407386296784866913009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126284543181729046489217345 94713407386296784866913009)
              ·
                refine ⟨71035055539722588650184757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94713407386296784866913009 71035055539722588650184757)
                ·
                  refine ⟨6659536456848992685954821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71035055539722588650184757 6659536456848992685954821)
                  ·
                    refine ⟨1248663085659186128616529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6659536456848992685954821 1248663085659186128616529)
                    ·
                      rfl

theorem cell23_7295288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_7295288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295288 prefixEnd_7295288 := by exact prefixLift 7295288
  have htrace : WordTrace (prefixWord ++ tailWord_7295288) baseStart_7295288 baseEnd_7295288 := by
    simpa [prefixWord, tailWord_7295288, baseEnd_7295288] using wordTrace_append hprefix tailTrace_7295288
  have hstable : (prefixWord ++ tailWord_7295288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295288).length < 2 ^ (prefixWord ++ tailWord_7295288).sum := by decide
  have hdescent : baseEnd_7295288 < baseStart_7295288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295385 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 4]
def baseStart_7295385 : Nat := 118140960795 + 7295385 * 2 ^ 59
def prefixEnd_7295385 : Nat := 4983230072969 + 3 ^ 40 * 7295385 * 2
def baseEnd_7295385 : Nat := 3746039064601044506336641

theorem tailTrace_7295385 : CollatzResearch.WordTrace tailWord_7295385 prefixEnd_7295385 3746039064601044506336641 := by
  unfold tailWord_7295385
  simp only [CollatzResearch.WordTrace]
  refine ⟨266084550675073572407759609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177389700450049048271839739 266084550675073572407759609)
  ·
    refine ⟨199563413006305179305819707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266084550675073572407759609 199563413006305179305819707)
    ·
      refine ⟨299345119509457768958729561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199563413006305179305819707 299345119509457768958729561)
      ·
        refine ⟨224508839632093326719047171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299345119509457768958729561 224508839632093326719047171)
        ·
          refine ⟨336763259448139990078570757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224508839632093326719047171 336763259448139990078570757)
          ·
            refine ⟨63143111146526248139732017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336763259448139990078570757 63143111146526248139732017)
            ·
              refine ⟨47357333359894686104799013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63143111146526248139732017 47357333359894686104799013)
              ·
                refine ⟨8879500004980253644649815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47357333359894686104799013 8879500004980253644649815)
                ·
                  refine ⟨13319250007470380466974723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879500004980253644649815 13319250007470380466974723)
                  ·
                    refine ⟨19978875011205570700462085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13319250007470380466974723 19978875011205570700462085)
                    ·
                      refine ⟨3746039064601044506336641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19978875011205570700462085 3746039064601044506336641)
                      ·
                        rfl

theorem cell23_7295385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_7295385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295385 prefixEnd_7295385 := by exact prefixLift 7295385
  have htrace : WordTrace (prefixWord ++ tailWord_7295385) baseStart_7295385 baseEnd_7295385 := by
    simpa [prefixWord, tailWord_7295385, baseEnd_7295385] using wordTrace_append hprefix tailTrace_7295385
  have hstable : (prefixWord ++ tailWord_7295385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295385).length < 2 ^ (prefixWord ++ tailWord_7295385).sum := by decide
  have hdescent : baseEnd_7295385 < baseStart_7295385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295399 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 1, 5]
def baseStart_7295399 : Nat := 118140960795 + 7295399 * 2 ^ 59
def prefixEnd_7295399 : Nat := 4983230072969 + 3 ^ 40 * 7295399 * 2
def baseEnd_7295399 : Nat := 1248682084443402483853859

theorem tailTrace_7295399 : CollatzResearch.WordTrace tailWord_7295399 prefixEnd_7295399 1248682084443402483853859 := by
  unfold tailWord_7295399
  simp only [CollatzResearch.WordTrace]
  refine ⟨266085061297022852798769251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177390040864681901865846167 266085061297022852798769251)
  ·
    refine ⟨399127591945534279198153877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266085061297022852798769251 399127591945534279198153877)
    ·
      refine ⟨18709105872446919337413463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 399127591945534279198153877 18709105872446919337413463)
      ·
        refine ⟨28063658808670379006120195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18709105872446919337413463 28063658808670379006120195)
        ·
          refine ⟨42095488213005568509180293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28063658808670379006120195 42095488213005568509180293)
          ·
            refine ⟨7892904039938544095471305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42095488213005568509180293 7892904039938544095471305)
            ·
              refine ⟨5919678029953908071603479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7892904039938544095471305 5919678029953908071603479)
              ·
                refine ⟨8879517044930862107405219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919678029953908071603479 8879517044930862107405219)
                ·
                  refine ⟨13319275567396293161107829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879517044930862107405219 13319275567396293161107829)
                  ·
                    refine ⟨1248682084443402483853859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13319275567396293161107829 1248682084443402483853859)
                    ·
                      rfl

theorem cell23_7295399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_7295399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295399 prefixEnd_7295399 := by exact prefixLift 7295399
  have htrace : WordTrace (prefixWord ++ tailWord_7295399) baseStart_7295399 baseEnd_7295399 := by
    simpa [prefixWord, tailWord_7295399, baseEnd_7295399] using wordTrace_append hprefix tailTrace_7295399
  have hstable : (prefixWord ++ tailWord_7295399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295399).length < 2 ^ (prefixWord ++ tailWord_7295399).sum := by decide
  have hdescent : baseEnd_7295399 < baseStart_7295399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295432 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_7295432 : Nat := 118140960795 + 7295432 * 2 ^ 59
def prefixEnd_7295432 : Nat := 4983230072969 + 3 ^ 40 * 7295432 * 2
def baseEnd_7295432 : Nat := 3746063198191805822448925

theorem tailTrace_7295432 : CollatzResearch.WordTrace tailWord_7295432 prefixEnd_7295432 3746063198191805822448925 := by
  unfold tailWord_7295432
  simp only [CollatzResearch.WordTrace]
  refine ⟨133043132452951649717360275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177390843270602199623147033 133043132452951649717360275)
  ·
    refine ⟨199564698679427474576040413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133043132452951649717360275 199564698679427474576040413)
    ·
      refine ⟨74836762004785302966015155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199564698679427474576040413 74836762004785302966015155)
      ·
        refine ⟨112255143007177954449022733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74836762004785302966015155 112255143007177954449022733)
        ·
          refine ⟨42095678627691732918383525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112255143007177954449022733 42095678627691732918383525)
          ·
            refine ⟨7892939742692199922196911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42095678627691732918383525 7892939742692199922196911)
            ·
              refine ⟨11839409614038299883295367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7892939742692199922196911 11839409614038299883295367)
              ·
                refine ⟨17759114421057449824943051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11839409614038299883295367 17759114421057449824943051)
                ·
                  refine ⟨26638671631586174737414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17759114421057449824943051 26638671631586174737414577)
                  ·
                    refine ⟨19979003723689631053060933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26638671631586174737414577 19979003723689631053060933)
                    ·
                      refine ⟨3746063198191805822448925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19979003723689631053060933 3746063198191805822448925)
                      ·
                        rfl

theorem cell23_7295432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_7295432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295432 prefixEnd_7295432 := by exact prefixLift 7295432
  have htrace : WordTrace (prefixWord ++ tailWord_7295432) baseStart_7295432 baseEnd_7295432 := by
    simpa [prefixWord, tailWord_7295432, baseEnd_7295432] using wordTrace_append hprefix tailTrace_7295432
  have hstable : (prefixWord ++ tailWord_7295432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295432).length < 2 ^ (prefixWord ++ tailWord_7295432).sum := by decide
  have hdescent : baseEnd_7295432 < baseStart_7295432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295442 : List Nat := [3, 2, 2, 4, 1, 1, 1, 9]
def baseStart_7295442 : Nat := 118140960795 + 7295442 * 2 ^ 59
def prefixEnd_7295442 : Nat := 4983230072969 + 3 ^ 40 * 7295442 * 2
def baseEnd_7295442 : Nat := 138743271592531510493477

theorem tailTrace_7295442 : CollatzResearch.WordTrace tailWord_7295442 prefixEnd_7295442 138743271592531510493477 := by
  unfold tailWord_7295442
  simp only [CollatzResearch.WordTrace]
  refine ⟨66521657408966767785646145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177391086423911380761723053 66521657408966767785646145)
  ·
    refine ⟨49891243056725075839234609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66521657408966767785646145 49891243056725075839234609)
    ·
      refine ⟨37418432292543806879425957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49891243056725075839234609 37418432292543806879425957)
      ·
        refine ⟨7015956054851963789892367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37418432292543806879425957 7015956054851963789892367)
        ·
          refine ⟨10523934082277945684838551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015956054851963789892367 10523934082277945684838551)
          ·
            refine ⟨15785901123416918527257827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523934082277945684838551 15785901123416918527257827)
            ·
              refine ⟨23678851685125377790886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785901123416918527257827 23678851685125377790886741)
              ·
                refine ⟨138743271592531510493477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23678851685125377790886741 138743271592531510493477)
                ·
                  rfl

theorem cell23_7295442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_7295442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295442 prefixEnd_7295442 := by exact prefixLift 7295442
  have htrace : WordTrace (prefixWord ++ tailWord_7295442) baseStart_7295442 baseEnd_7295442 := by
    simpa [prefixWord, tailWord_7295442, baseEnd_7295442] using wordTrace_append hprefix tailTrace_7295442
  have hstable : (prefixWord ++ tailWord_7295442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295442).length < 2 ^ (prefixWord ++ tailWord_7295442).sum := by decide
  have hdescent : baseEnd_7295442 < baseStart_7295442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295469 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7295469 : Nat := 118140960795 + 7295469 * 2 ^ 59
def prefixEnd_7295469 : Nat := 4983230072969 + 3 ^ 40 * 7295469 * 2
def baseEnd_7295469 : Nat := 3746082196976022177686255

theorem tailTrace_7295469 : CollatzResearch.WordTrace tailWord_7295469 prefixEnd_7295469 3746082196976022177686255 := by
  unfold tailWord_7295469
  simp only [CollatzResearch.WordTrace]
  refine ⟨266087614406769254753817461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177391742937846169835878307 266087614406769254753817461)
  ·
    refine ⟨24945713850634617633170387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266087614406769254753817461 24945713850634617633170387)
    ·
      refine ⟨37418570775951926449755581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24945713850634617633170387 37418570775951926449755581)
      ·
        refine ⟨14031964040981972418658343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37418570775951926449755581 14031964040981972418658343)
        ·
          refine ⟨21047946061472958627987515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14031964040981972418658343 21047946061472958627987515)
          ·
            refine ⟨31571919092209437941981273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21047946061472958627987515 31571919092209437941981273)
            ·
              refine ⟨23678939319157078456485955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31571919092209437941981273 23678939319157078456485955)
              ·
                refine ⟨35518408978735617684728933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23678939319157078456485955 35518408978735617684728933)
                ·
                  refine ⟨6659701683512928315886675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35518408978735617684728933 6659701683512928315886675)
                  ·
                    refine ⟨9989552525269392473830013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659701683512928315886675 9989552525269392473830013)
                    ·
                      refine ⟨3746082196976022177686255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9989552525269392473830013 3746082196976022177686255)
                      ·
                        rfl

theorem cell23_7295469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7295469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295469 prefixEnd_7295469 := by exact prefixLift 7295469
  have htrace : WordTrace (prefixWord ++ tailWord_7295469) baseStart_7295469 baseEnd_7295469 := by
    simpa [prefixWord, tailWord_7295469, baseEnd_7295469] using wordTrace_append hprefix tailTrace_7295469
  have hstable : (prefixWord ++ tailWord_7295469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295469).length < 2 ^ (prefixWord ++ tailWord_7295469).sum := by decide
  have hdescent : baseEnd_7295469 < baseStart_7295469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295488 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_7295488 : Nat := 118140960795 + 7295488 * 2 ^ 59
def prefixEnd_7295488 : Nat := 4983230072969 + 3 ^ 40 * 7295488 * 2
def baseEnd_7295488 : Nat := 3746091953108457603348667

theorem tailTrace_7295488 : CollatzResearch.WordTrace tailWord_7295488 prefixEnd_7295488 3746091953108457603348667 := by
  unfold tailWord_7295488
  simp only [CollatzResearch.WordTrace]
  refine ⟨133044153696850210499379559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177392204929133613999172745 133044153696850210499379559)
  ·
    refine ⟨199566230545275315749069339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133044153696850210499379559 199566230545275315749069339)
    ·
      refine ⟨299349345817912973623604009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199566230545275315749069339 299349345817912973623604009)
      ·
        refine ⟨224512009363434730217703007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299349345817912973623604009 224512009363434730217703007)
        ·
          refine ⟨336768014045152095326554511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224512009363434730217703007 336768014045152095326554511)
          ·
            refine ⟨505152021067728142989831767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336768014045152095326554511 505152021067728142989831767)
            ·
              refine ⟨757728031601592214484747651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505152021067728142989831767 757728031601592214484747651)
              ·
                refine ⟨1136592047402388321727121477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757728031601592214484747651 1136592047402388321727121477)
                ·
                  refine ⟨213111008887947810323835277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136592047402388321727121477 213111008887947810323835277)
                  ·
                    refine ⟨79916628332980428871438229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213111008887947810323835277 79916628332980428871438229)
                    ·
                      refine ⟨3746091953108457603348667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79916628332980428871438229 3746091953108457603348667)
                      ·
                        rfl

theorem cell23_7295488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_7295488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295488 prefixEnd_7295488 := by exact prefixLift 7295488
  have htrace : WordTrace (prefixWord ++ tailWord_7295488) baseStart_7295488 baseEnd_7295488 := by
    simpa [prefixWord, tailWord_7295488, baseEnd_7295488] using wordTrace_append hprefix tailTrace_7295488
  have hstable : (prefixWord ++ tailWord_7295488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295488).length < 2 ^ (prefixWord ++ tailWord_7295488).sum := by decide
  have hdescent : baseEnd_7295488 < baseStart_7295488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295545 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_7295545 : Nat := 118140960795 + 7295545 * 2 ^ 59
def prefixEnd_7295545 : Nat := 4983230072969 + 3 ^ 40 * 7295545 * 2
def baseEnd_7295545 : Nat := 1248707073835254626778635

theorem tailTrace_7295545 : CollatzResearch.WordTrace tailWord_7295545 prefixEnd_7295545 1248707073835254626778635 := by
  unfold tailWord_7295545
  simp only [CollatzResearch.WordTrace]
  refine ⟨266090386354493919733584089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177393590902995946489056059 266090386354493919733584089)
  ·
    refine ⟨199567789765870439800188067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266090386354493919733584089 199567789765870439800188067)
    ·
      refine ⟨299351684648805659700282101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199567789765870439800188067 299351684648805659700282101)
      ·
        refine ⟨28064220435825530596901447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299351684648805659700282101 28064220435825530596901447)
        ·
          refine ⟨42096330653738295895352171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28064220435825530596901447 42096330653738295895352171)
          ·
            refine ⟨63144495980607443843028257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42096330653738295895352171 63144495980607443843028257)
            ·
              refine ⟨47358371985455582882271193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63144495980607443843028257 47358371985455582882271193)
              ·
                refine ⟨35518778989091687161703395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47358371985455582882271193 35518778989091687161703395)
                ·
                  refine ⟨53278168483637530742555093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35518778989091687161703395 53278168483637530742555093)
                  ·
                    refine ⟨1248707073835254626778635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53278168483637530742555093 1248707073835254626778635)
                    ·
                      rfl

theorem cell23_7295545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_7295545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295545 prefixEnd_7295545 := by exact prefixLift 7295545
  have htrace : WordTrace (prefixWord ++ tailWord_7295545) baseStart_7295545 baseEnd_7295545 := by
    simpa [prefixWord, tailWord_7295545, baseEnd_7295545] using wordTrace_append hprefix tailTrace_7295545
  have hstable : (prefixWord ++ tailWord_7295545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295545).length < 2 ^ (prefixWord ++ tailWord_7295545).sum := by decide
  have hdescent : baseEnd_7295545 < baseStart_7295545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295562 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_7295562 : Nat := 118140960795 + 7295562 * 2 ^ 59
def prefixEnd_7295562 : Nat := 4983230072969 + 3 ^ 40 * 7295562 * 2
def baseEnd_7295562 : Nat := 1248709983558963437941109

theorem tailTrace_7295562 : CollatzResearch.WordTrace tailWord_7295562 prefixEnd_7295562 1248709983558963437941109 := by
  unfold tailWord_7295562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66522751598858082909238235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177394004263621554424635293 66522751598858082909238235)
  ·
    refine ⟨99784127398287124363857353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66522751598858082909238235 99784127398287124363857353)
    ·
      refine ⟨74838095548715343272893015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99784127398287124363857353 74838095548715343272893015)
      ·
        refine ⟨112257143323073014909339523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74838095548715343272893015 112257143323073014909339523)
        ·
          refine ⟨168385714984609522364009285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112257143323073014909339523 168385714984609522364009285)
          ·
            refine ⟨31572321559614285443251741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168385714984609522364009285 31572321559614285443251741)
            ·
              refine ⟨11839620584855357041219403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31572321559614285443251741 11839620584855357041219403)
              ·
                refine ⟨17759430877283035561829105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11839620584855357041219403 17759430877283035561829105)
                ·
                  refine ⟨13319573157962276671371829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17759430877283035561829105 13319573157962276671371829)
                  ·
                    refine ⟨1248709983558963437941109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13319573157962276671371829 1248709983558963437941109)
                    ·
                      rfl

theorem cell23_7295562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_7295562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295562 prefixEnd_7295562 := by exact prefixLift 7295562
  have htrace : WordTrace (prefixWord ++ tailWord_7295562) baseStart_7295562 baseEnd_7295562 := by
    simpa [prefixWord, tailWord_7295562, baseEnd_7295562] using wordTrace_append hprefix tailTrace_7295562
  have hstable : (prefixWord ++ tailWord_7295562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295562).length < 2 ^ (prefixWord ++ tailWord_7295562).sum := by decide
  have hdescent : baseEnd_7295562 < baseStart_7295562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295636 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7295636 : Nat := 118140960795 + 7295636 * 2 ^ 59
def prefixEnd_7295636 : Nat := 4983230072969 + 3 ^ 40 * 7295636 * 2
def baseEnd_7295636 : Nat := 3746167948245323024297987

theorem tailTrace_7295636 : CollatzResearch.WordTrace tailWord_7295636 prefixEnd_7295636 3746167948245323024297987 := by
  unfold tailWord_7295636
  simp only [CollatzResearch.WordTrace]
  refine ⟨133046852698582121137573381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177395803598109494850097841 133046852698582121137573381)
  ·
    refine ⟨24946284880984147713295009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133046852698582121137573381 24946284880984147713295009)
    ·
      refine ⟨18709713660738110784971257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24946284880984147713295009 18709713660738110784971257)
      ·
        refine ⟨14032285245553583088728443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18709713660738110784971257 14032285245553583088728443)
        ·
          refine ⟨21048427868330374633092665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14032285245553583088728443 21048427868330374633092665)
          ·
            refine ⟨15786320901247780974819499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21048427868330374633092665 15786320901247780974819499)
            ·
              refine ⟨23679481351871671462229249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15786320901247780974819499 23679481351871671462229249)
              ·
                refine ⟨17759611013903753596671937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23679481351871671462229249 17759611013903753596671937)
                ·
                  refine ⟨13319708260427815197503953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17759611013903753596671937 13319708260427815197503953)
                  ·
                    refine ⟨9989781195320861398127965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13319708260427815197503953 9989781195320861398127965)
                    ·
                      refine ⟨3746167948245323024297987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9989781195320861398127965 3746167948245323024297987)
                      ·
                        rfl

theorem cell23_7295636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7295636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295636 prefixEnd_7295636 := by exact prefixLift 7295636
  have htrace : WordTrace (prefixWord ++ tailWord_7295636) baseStart_7295636 baseEnd_7295636 := by
    simpa [prefixWord, tailWord_7295636, baseEnd_7295636] using wordTrace_append hprefix tailTrace_7295636
  have hstable : (prefixWord ++ tailWord_7295636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295636).length < 2 ^ (prefixWord ++ tailWord_7295636).sum := by decide
  have hdescent : baseEnd_7295636 < baseStart_7295636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295652 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_7295652 : Nat := 118140960795 + 7295652 * 2 ^ 59
def prefixEnd_7295652 : Nat := 4983230072969 + 3 ^ 40 * 7295652 * 2
def baseEnd_7295652 : Nat := 1248725387978598320565971

theorem tailTrace_7295652 : CollatzResearch.WordTrace tailWord_7295652 prefixEnd_7295652 1248725387978598320565971 := by
  unfold tailWord_7295652
  simp only [CollatzResearch.WordTrace]
  refine ⟨133047144482553138503864605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177396192643404184671819473 133047144482553138503864605)
  ·
    refine ⟨49892679180957426938949227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133047144482553138503864605 49892679180957426938949227)
    ·
      refine ⟨74839018771436140408423841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49892679180957426938949227 74839018771436140408423841)
      ·
        refine ⟨56129264078577105306317881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74839018771436140408423841 56129264078577105306317881)
        ·
          refine ⟨42096948058932828979738411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56129264078577105306317881 42096948058932828979738411)
          ·
            refine ⟨63145422088399243469607617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42096948058932828979738411 63145422088399243469607617)
            ·
              refine ⟨47359066566299432602205713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63145422088399243469607617 47359066566299432602205713)
              ·
                refine ⟨35519299924724574451654285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47359066566299432602205713 35519299924724574451654285)
                ·
                  refine ⟨13319737471771715419370357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35519299924724574451654285 13319737471771715419370357)
                  ·
                    refine ⟨1248725387978598320565971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13319737471771715419370357 1248725387978598320565971)
                    ·
                      rfl

theorem cell23_7295652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_7295652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295652 prefixEnd_7295652 := by exact prefixLift 7295652
  have htrace : WordTrace (prefixWord ++ tailWord_7295652) baseStart_7295652 baseEnd_7295652 := by
    simpa [prefixWord, tailWord_7295652, baseEnd_7295652] using wordTrace_append hprefix tailTrace_7295652
  have hstable : (prefixWord ++ tailWord_7295652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295652).length < 2 ^ (prefixWord ++ tailWord_7295652).sum := by decide
  have hdescent : baseEnd_7295652 < baseStart_7295652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295669 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_7295669 : Nat := 118140960795 + 7295669 * 2 ^ 59
def prefixEnd_7295669 : Nat := 4983230072969 + 3 ^ 40 * 7295669 * 2
def baseEnd_7295669 : Nat := 1248728297702307131728445

theorem tailTrace_7295669 : CollatzResearch.WordTrace tailWord_7295669 prefixEnd_7295669 1248728297702307131728445 := by
  unfold tailWord_7295669
  simp only [CollatzResearch.WordTrace]
  refine ⟨266094909006044688911098061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177396606004029792607398707 266094909006044688911098061)
  ·
    refine ⟨99785590877266758341661773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266094909006044688911098061 99785590877266758341661773)
    ·
      refine ⟨37419596578975034378123165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99785590877266758341661773 37419596578975034378123165)
      ·
        refine ⟨14032348717115637891796187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37419596578975034378123165 14032348717115637891796187)
        ·
          refine ⟨21048523075673456837694281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14032348717115637891796187 21048523075673456837694281)
          ·
            refine ⟨15786392306755092628270711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21048523075673456837694281 15786392306755092628270711)
            ·
              refine ⟨23679588460132638942406067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15786392306755092628270711 23679588460132638942406067)
              ·
                refine ⟨35519382690198958413609101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23679588460132638942406067 35519382690198958413609101)
                ·
                  refine ⟨13319768508824609405103413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35519382690198958413609101 13319768508824609405103413)
                  ·
                    refine ⟨1248728297702307131728445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13319768508824609405103413 1248728297702307131728445)
                    ·
                      rfl

theorem cell23_7295669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_7295669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295669 prefixEnd_7295669 := by exact prefixLift 7295669
  have htrace : WordTrace (prefixWord ++ tailWord_7295669) baseStart_7295669 baseEnd_7295669 := by
    simpa [prefixWord, tailWord_7295669, baseEnd_7295669] using wordTrace_append hprefix tailTrace_7295669
  have hstable : (prefixWord ++ tailWord_7295669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295669).length < 2 ^ (prefixWord ++ tailWord_7295669).sum := by decide
  have hdescent : baseEnd_7295669 < baseStart_7295669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295675 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_7295675 : Nat := 118140960795 + 7295675 * 2 ^ 59
def prefixEnd_7295675 : Nat := 4983230072969 + 3 ^ 40 * 7295675 * 2
def baseEnd_7295675 : Nat := 3746187973990848371710307

theorem tailTrace_7295675 : CollatzResearch.WordTrace tailWord_7295675 prefixEnd_7295675 3746187973990848371710307 := by
  unfold tailWord_7295675
  simp only [CollatzResearch.WordTrace]
  refine ⟨266095127844022951935816479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177396751896015301290544319 266095127844022951935816479)
  ·
    refine ⟨399142691766034427903724719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266095127844022951935816479 399142691766034427903724719)
    ·
      refine ⟨598714037649051641855587079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399142691766034427903724719 598714037649051641855587079)
      ·
        refine ⟨898071056473577462783380619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598714037649051641855587079 898071056473577462783380619)
        ·
          refine ⟨1347106584710366194175070929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898071056473577462783380619 1347106584710366194175070929)
          ·
            refine ⟨1010329938532774645631303197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347106584710366194175070929 1010329938532774645631303197)
            ·
              refine ⟨378873726949790492111738699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1010329938532774645631303197 378873726949790492111738699)
              ·
                refine ⟨568310590424685738167608049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378873726949790492111738699 568310590424685738167608049)
                ·
                  refine ⟨426232942818514303625706037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568310590424685738167608049 426232942818514303625706037)
                  ·
                    refine ⟨39959338389235715964909941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 426232942818514303625706037 39959338389235715964909941)
                    ·
                      refine ⟨3746187973990848371710307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39959338389235715964909941 3746187973990848371710307)
                      ·
                        rfl

theorem cell23_7295675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_7295675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295675 prefixEnd_7295675 := by exact prefixLift 7295675
  have htrace : WordTrace (prefixWord ++ tailWord_7295675) baseStart_7295675 baseEnd_7295675 := by
    simpa [prefixWord, tailWord_7295675, baseEnd_7295675] using wordTrace_append hprefix tailTrace_7295675
  have hstable : (prefixWord ++ tailWord_7295675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295675).length < 2 ^ (prefixWord ++ tailWord_7295675).sum := by decide
  have hdescent : baseEnd_7295675 < baseStart_7295675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295676 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_7295676 : Nat := 118140960795 + 7295676 * 2 ^ 59
def prefixEnd_7295676 : Nat := 4983230072969 + 3 ^ 40 * 7295676 * 2
def baseEnd_7295676 : Nat := 3746188487471502867797803

theorem tailTrace_7295676 : CollatzResearch.WordTrace tailWord_7295676 prefixEnd_7295676 3746188487471502867797803 := by
  unfold tailWord_7295676
  simp only [CollatzResearch.WordTrace]
  refine ⟨133047582158509664553301441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177396776211346219404401921 133047582158509664553301441)
  ·
    refine ⟨99785686618882248414976081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133047582158509664553301441 99785686618882248414976081)
    ·
      refine ⟨74839264964161686311232061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99785686618882248414976081 74839264964161686311232061)
      ·
        refine ⟨28064724361560632366712023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74839264964161686311232061 28064724361560632366712023)
        ·
          refine ⟨42097086542340948550068035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28064724361560632366712023 42097086542340948550068035)
          ·
            refine ⟨63145629813511422825102053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42097086542340948550068035 63145629813511422825102053)
            ·
              refine ⟨11839805590033391779706635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63145629813511422825102053 11839805590033391779706635)
              ·
                refine ⟨17759708385050087669559953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11839805590033391779706635 17759708385050087669559953)
                ·
                  refine ⟨13319781288787565752169965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17759708385050087669559953 13319781288787565752169965)
                  ·
                    refine ⟨4994917983295337157063737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13319781288787565752169965 4994917983295337157063737)
                    ·
                      refine ⟨3746188487471502867797803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994917983295337157063737 3746188487471502867797803)
                      ·
                        rfl

theorem cell23_7295676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_7295676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295676 prefixEnd_7295676 := by exact prefixLift 7295676
  have htrace : WordTrace (prefixWord ++ tailWord_7295676) baseStart_7295676 baseEnd_7295676 := by
    simpa [prefixWord, tailWord_7295676, baseEnd_7295676] using wordTrace_append hprefix tailTrace_7295676
  have hstable : (prefixWord ++ tailWord_7295676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295676).length < 2 ^ (prefixWord ++ tailWord_7295676).sum := by decide
  have hdescent : baseEnd_7295676 < baseStart_7295676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295700 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7295700 : Nat := 118140960795 + 7295700 * 2 ^ 59
def prefixEnd_7295700 : Nat := 4983230072969 + 3 ^ 40 * 7295700 * 2
def baseEnd_7295700 : Nat := 3746200811007210773897693

theorem tailTrace_7295700 : CollatzResearch.WordTrace tailWord_7295700 prefixEnd_7295700 3746200811007210773897693 := by
  unfold tailWord_7295700
  simp only [CollatzResearch.WordTrace]
  refine ⟨133048019834466190602738277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177397359779288254136984369 133048019834466190602738277)
  ·
    refine ⟨24946503718962410738013427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133048019834466190602738277 24946503718962410738013427)
    ·
      refine ⟨37419755578443616107020141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24946503718962410738013427 37419755578443616107020141)
      ·
        refine ⟨14032408341916356040132553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37419755578443616107020141 14032408341916356040132553)
        ·
          refine ⟨10524306256437267030099415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14032408341916356040132553 10524306256437267030099415)
          ·
            refine ⟨15786459384655900545149123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524306256437267030099415 15786459384655900545149123)
            ·
              refine ⟨23679689076983850817723685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15786459384655900545149123 23679689076983850817723685)
              ·
                refine ⟨4439941701934472028323191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23679689076983850817723685 4439941701934472028323191)
                ·
                  refine ⟨6659912552901708042484787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439941701934472028323191 6659912552901708042484787)
                  ·
                    refine ⟨9989868829352562063727181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659912552901708042484787 9989868829352562063727181)
                    ·
                      refine ⟨3746200811007210773897693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9989868829352562063727181 3746200811007210773897693)
                      ·
                        rfl

theorem cell23_7295700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7295700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295700 prefixEnd_7295700 := by exact prefixLift 7295700
  have htrace : WordTrace (prefixWord ++ tailWord_7295700) baseStart_7295700 baseEnd_7295700 := by
    simpa [prefixWord, tailWord_7295700, baseEnd_7295700] using wordTrace_append hprefix tailTrace_7295700
  have hstable : (prefixWord ++ tailWord_7295700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295700).length < 2 ^ (prefixWord ++ tailWord_7295700).sum := by decide
  have hdescent : baseEnd_7295700 < baseStart_7295700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295706 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2]
def baseStart_7295706 : Nat := 118140960795 + 7295706 * 2 ^ 59
def prefixEnd_7295706 : Nat := 4983230072969 + 3 ^ 40 * 7295706 * 2
def baseEnd_7295706 : Nat := 3746203891891137750422665

theorem tailTrace_7295706 : CollatzResearch.WordTrace tailWord_7295706 prefixEnd_7295706 3746203891891137750422665 := by
  unfold tailWord_7295706
  simp only [CollatzResearch.WordTrace]
  refine ⟨66524064626727661057548743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177397505671273762820129981 66524064626727661057548743)
  ·
    refine ⟨99786096940091491586323115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66524064626727661057548743 99786096940091491586323115)
    ·
      refine ⟨149679145410137237379484673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99786096940091491586323115 149679145410137237379484673)
      ·
        refine ⟨112259359057602928034613505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149679145410137237379484673 112259359057602928034613505)
        ·
          refine ⟨84194519293202196025960129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112259359057602928034613505 84194519293202196025960129)
          ·
            refine ⟨63145889469901647019470097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84194519293202196025960129 63145889469901647019470097)
            ·
              refine ⟨47359417102426235264602573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63145889469901647019470097 47359417102426235264602573)
              ·
                refine ⟨17759781413409838224225965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47359417102426235264602573 17759781413409838224225965)
                ·
                  refine ⟨6659918030028689334084737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17759781413409838224225965 6659918030028689334084737)
                  ·
                    refine ⟨4994938522521517000563553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6659918030028689334084737 4994938522521517000563553)
                    ·
                      refine ⟨3746203891891137750422665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994938522521517000563553 3746203891891137750422665)
                      ·
                        rfl

theorem cell23_7295706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_7295706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295706 prefixEnd_7295706 := by exact prefixLift 7295706
  have htrace : WordTrace (prefixWord ++ tailWord_7295706) baseStart_7295706 baseEnd_7295706 := by
    simpa [prefixWord, tailWord_7295706, baseEnd_7295706] using wordTrace_append hprefix tailTrace_7295706
  have hstable : (prefixWord ++ tailWord_7295706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295706).length < 2 ^ (prefixWord ++ tailWord_7295706).sum := by decide
  have hdescent : baseEnd_7295706 < baseStart_7295706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295740 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_7295740 : Nat := 118140960795 + 7295740 * 2 ^ 59
def prefixEnd_7295740 : Nat := 4983230072969 + 3 ^ 40 * 7295740 * 2
def baseEnd_7295740 : Nat := 3746221350233390617397509

theorem tailTrace_7295740 : CollatzResearch.WordTrace tailWord_7295740 prefixEnd_7295740 3746221350233390617397509 := by
  unfold tailWord_7295740
  simp only [CollatzResearch.WordTrace]
  refine ⟨133048749294393734018466337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177398332392524978691288449 133048749294393734018466337)
  ·
    refine ⟨99786561970795300513849753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133048749294393734018466337 99786561970795300513849753)
    ·
      refine ⟨74839921478096475385387315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99786561970795300513849753 74839921478096475385387315)
      ·
        refine ⟨112259882217144713078080973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74839921478096475385387315 112259882217144713078080973)
        ·
          refine ⟨42097455831429267404280365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112259882217144713078080973 42097455831429267404280365)
          ·
            refine ⟨15786545936785975276605137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42097455831429267404280365 15786545936785975276605137)
            ·
              refine ⟨11839909452589481457453853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15786545936785975276605137 11839909452589481457453853)
              ·
                refine ⟨4439966044721055546545195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11839909452589481457453853 4439966044721055546545195)
                ·
                  refine ⟨6659949067081583319817793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439966044721055546545195 6659949067081583319817793)
                  ·
                    refine ⟨4994961800311187489863345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6659949067081583319817793 4994961800311187489863345)
                    ·
                      refine ⟨3746221350233390617397509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4994961800311187489863345 3746221350233390617397509)
                      ·
                        rfl

theorem cell23_7295740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_7295740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295740 prefixEnd_7295740 := by exact prefixLift 7295740
  have htrace : WordTrace (prefixWord ++ tailWord_7295740) baseStart_7295740 baseEnd_7295740 := by
    simpa [prefixWord, tailWord_7295740, baseEnd_7295740] using wordTrace_append hprefix tailTrace_7295740
  have hstable : (prefixWord ++ tailWord_7295740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295740).length < 2 ^ (prefixWord ++ tailWord_7295740).sum := by decide
  have hdescent : baseEnd_7295740 < baseStart_7295740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295792 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_7295792 : Nat := 118140960795 + 7295792 * 2 ^ 59
def prefixEnd_7295792 : Nat := 4983230072969 + 3 ^ 40 * 7295792 * 2
def baseEnd_7295792 : Nat := 3746248051227424413947269

theorem tailTrace_7295792 : CollatzResearch.WordTrace tailWord_7295792 prefixEnd_7295792 3746248051227424413947269 := by
  unfold tailWord_7295792
  simp only [CollatzResearch.WordTrace]
  refine ⟨133049697592299540458912815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177399596789732720611883753 133049697592299540458912815)
  ·
    refine ⟨199574546388449310688369223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133049697592299540458912815 199574546388449310688369223)
    ·
      refine ⟨299361819582673966032553835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199574546388449310688369223 299361819582673966032553835)
      ·
        refine ⟨449042729374010949048830753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299361819582673966032553835 449042729374010949048830753)
        ·
          refine ⟨336782047030508211786623065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449042729374010949048830753 336782047030508211786623065)
          ·
            refine ⟨252586535272881158839967299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336782047030508211786623065 252586535272881158839967299)
            ·
              refine ⟨378879802909321738259950949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252586535272881158839967299 378879802909321738259950949)
              ·
                refine ⟨71039963045497825923740803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378879802909321738259950949 71039963045497825923740803)
                ·
                  refine ⟨106559944568246738885611205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71039963045497825923740803 106559944568246738885611205)
                  ·
                    refine ⟨19979989606546263541052101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106559944568246738885611205 19979989606546263541052101)
                    ·
                      refine ⟨3746248051227424413947269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19979989606546263541052101 3746248051227424413947269)
                      ·
                        rfl

theorem cell23_7295792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_7295792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295792 prefixEnd_7295792 := by exact prefixLift 7295792
  have htrace : WordTrace (prefixWord ++ tailWord_7295792) baseStart_7295792 baseEnd_7295792 := by
    simpa [prefixWord, tailWord_7295792, baseEnd_7295792] using wordTrace_append hprefix tailTrace_7295792
  have hstable : (prefixWord ++ tailWord_7295792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295792).length < 2 ^ (prefixWord ++ tailWord_7295792).sum := by decide
  have hdescent : baseEnd_7295792 < baseStart_7295792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295829 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_7295829 : Nat := 118140960795 + 7295829 * 2 ^ 59
def prefixEnd_7295829 : Nat := 4983230072969 + 3 ^ 40 * 7295829 * 2
def baseEnd_7295829 : Nat := 3746267050011640769184599

theorem tailTrace_7295829 : CollatzResearch.WordTrace tailWord_7295829 prefixEnd_7295829 3746267050011640769184599 := by
  unfold tailWord_7295829
  simp only [CollatzResearch.WordTrace]
  refine ⟨266100744685465036236922541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177400496456976690824615027 266100744685465036236922541)
  ·
    refine ⟨99787779257049388588845953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266100744685465036236922541 99787779257049388588845953)
    ·
      refine ⟨74840834442787041441634465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99787779257049388588845953 74840834442787041441634465)
      ·
        refine ⟨56130625832090281081225849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74840834442787041441634465 56130625832090281081225849)
        ·
          refine ⟨42097969374067710810919387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56130625832090281081225849 42097969374067710810919387)
          ·
            refine ⟨63146954061101566216379081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42097969374067710810919387 63146954061101566216379081)
            ·
              refine ⟨47360215545826174662284311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63146954061101566216379081 47360215545826174662284311)
              ·
                refine ⟨71040323318739261993426467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47360215545826174662284311 71040323318739261993426467)
                ·
                  refine ⟨106560484978108892990139701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71040323318739261993426467 106560484978108892990139701)
                  ·
                    refine ⟨9990045466697708717825597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106560484978108892990139701 9990045466697708717825597)
                    ·
                      refine ⟨3746267050011640769184599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990045466697708717825597 3746267050011640769184599)
                      ·
                        rfl

theorem cell23_7295829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_7295829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295829 prefixEnd_7295829 := by exact prefixLift 7295829
  have htrace : WordTrace (prefixWord ++ tailWord_7295829) baseStart_7295829 baseEnd_7295829 := by
    simpa [prefixWord, tailWord_7295829, baseEnd_7295829] using wordTrace_append hprefix tailTrace_7295829
  have hstable : (prefixWord ++ tailWord_7295829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295829).length < 2 ^ (prefixWord ++ tailWord_7295829).sum := by decide
  have hdescent : baseEnd_7295829 < baseStart_7295829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295832 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_7295832 : Nat := 118140960795 + 7295832 * 2 ^ 59
def prefixEnd_7295832 : Nat := 4983230072969 + 3 ^ 40 * 7295832 * 2
def baseEnd_7295832 : Nat := 1248756196817868085815695

theorem tailTrace_7295832 : CollatzResearch.WordTrace tailWord_7295832 prefixEnd_7295832 1248756196817868085815695 := by
  unfold tailWord_7295832
  simp only [CollatzResearch.WordTrace]
  refine ⟨133050427052227083874640875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177400569402969445166187833 133050427052227083874640875)
  ·
    refine ⟨199575640578340625811961313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133050427052227083874640875 199575640578340625811961313)
    ·
      refine ⟨149681730433755469358970985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199575640578340625811961313 149681730433755469358970985)
      ·
        refine ⟨112261297825316602019228239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149681730433755469358970985 112261297825316602019228239)
        ·
          refine ⟨168391946737974903028842359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112261297825316602019228239 168391946737974903028842359)
          ·
            refine ⟨252587920106962354543263539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168391946737974903028842359 252587920106962354543263539)
            ·
              refine ⟨378881880160443531814895309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252587920106962354543263539 378881880160443531814895309)
              ·
                refine ⟨142080705060166324430585741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378881880160443531814895309 142080705060166324430585741)
                ·
                  refine ⟨53280264397562371661469653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142080705060166324430585741 53280264397562371661469653)
                  ·
                    refine ⟨1248756196817868085815695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53280264397562371661469653 1248756196817868085815695)
                    ·
                      rfl

theorem cell23_7295832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_7295832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295832 prefixEnd_7295832 := by exact prefixLift 7295832
  have htrace : WordTrace (prefixWord ++ tailWord_7295832) baseStart_7295832 baseEnd_7295832 := by
    simpa [prefixWord, tailWord_7295832, baseEnd_7295832] using wordTrace_append hprefix tailTrace_7295832
  have hstable : (prefixWord ++ tailWord_7295832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295832).length < 2 ^ (prefixWord ++ tailWord_7295832).sum := by decide
  have hdescent : baseEnd_7295832 < baseStart_7295832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295870 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_7295870 : Nat := 118140960795 + 7295870 * 2 ^ 59
def prefixEnd_7295870 : Nat := 4983230072969 + 3 ^ 40 * 7295870 * 2
def baseEnd_7295870 : Nat := 416254233635386123196879

theorem tailTrace_7295870 : CollatzResearch.WordTrace tailWord_7295870 prefixEnd_7295870 416254233635386123196879 := by
  unfold tailWord_7295870
  simp only [CollatzResearch.WordTrace]
  refine ⟨33262780009789562529895633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177401493385544333492776709 33262780009789562529895633)
  ·
    refine ⟨24947085007342171897421725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33262780009789562529895633 24947085007342171897421725)
    ·
      refine ⟨9355156877753314461533147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24947085007342171897421725 9355156877753314461533147)
      ·
        refine ⟨14032735316629971692299721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9355156877753314461533147 14032735316629971692299721)
        ·
          refine ⟨10524551487472478769224791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14032735316629971692299721 10524551487472478769224791)
          ·
            refine ⟨15786827231208718153837187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524551487472478769224791 15786827231208718153837187)
            ·
              refine ⟨23680240846813077230755781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15786827231208718153837187 23680240846813077230755781)
              ·
                refine ⟨4440045158777451980766709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23680240846813077230755781 4440045158777451980766709)
                ·
                  refine ⟨416254233635386123196879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4440045158777451980766709 416254233635386123196879)
                  ·
                    rfl

theorem cell23_7295870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_7295870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295870 prefixEnd_7295870 := by exact prefixLift 7295870
  have htrace : WordTrace (prefixWord ++ tailWord_7295870) baseStart_7295870 baseEnd_7295870 := by
    simpa [prefixWord, tailWord_7295870, baseEnd_7295870] using wordTrace_append hprefix tailTrace_7295870
  have hstable : (prefixWord ++ tailWord_7295870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295870).length < 2 ^ (prefixWord ++ tailWord_7295870).sum := by decide
  have hdescent : baseEnd_7295870 < baseStart_7295870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295889 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_7295889 : Nat := 118140960795 + 7295889 * 2 ^ 59
def prefixEnd_7295889 : Nat := 4983230072969 + 3 ^ 40 * 7295889 * 2
def baseEnd_7295889 : Nat := 3746297858850910534434323

theorem tailTrace_7295889 : CollatzResearch.WordTrace tailWord_7295889 prefixEnd_7295889 3746297858850910534434323 := by
  unfold tailWord_7295889
  simp only [CollatzResearch.WordTrace]
  refine ⟨266102933065247666484106721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177401955376831777656071147 266102933065247666484106721)
  ·
    refine ⟨199577199798935749863080041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266102933065247666484106721 199577199798935749863080041)
    ·
      refine ⟨149682899849201812397310031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199577199798935749863080041 149682899849201812397310031)
      ·
        refine ⟨224524349773802718595965047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149682899849201812397310031 224524349773802718595965047)
        ·
          refine ⟨336786524660704077893947571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224524349773802718595965047 336786524660704077893947571)
          ·
            refine ⟨505179786991056116840921357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336786524660704077893947571 505179786991056116840921357)
            ·
              refine ⟨189442420121646043815345509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505179786991056116840921357 189442420121646043815345509)
              ·
                refine ⟨35520453772808633215377283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189442420121646043815345509 35520453772808633215377283)
                ·
                  refine ⟨53280680659212949823065925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35520453772808633215377283 53280680659212949823065925)
                  ·
                    refine ⟨9990127623602428091824861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53280680659212949823065925 9990127623602428091824861)
                    ·
                      refine ⟨3746297858850910534434323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990127623602428091824861 3746297858850910534434323)
                      ·
                        rfl

theorem cell23_7295889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_7295889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295889 prefixEnd_7295889 := by exact prefixLift 7295889
  have htrace : WordTrace (prefixWord ++ tailWord_7295889) baseStart_7295889 baseEnd_7295889 := by
    simpa [prefixWord, tailWord_7295889, baseEnd_7295889] using wordTrace_append hprefix tailTrace_7295889
  have hstable : (prefixWord ++ tailWord_7295889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295889).length < 2 ^ (prefixWord ++ tailWord_7295889).sum := by decide
  have hdescent : baseEnd_7295889 < baseStart_7295889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295900 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_7295900 : Nat := 118140960795 + 7295900 * 2 ^ 59
def prefixEnd_7295900 : Nat := 4983230072969 + 3 ^ 40 * 7295900 * 2
def baseEnd_7295900 : Nat := 1248767835712703330465591

theorem tailTrace_7295900 : CollatzResearch.WordTrace tailWord_7295900 prefixEnd_7295900 1248767835712703330465591 := by
  unfold tailWord_7295900
  simp only [CollatzResearch.WordTrace]
  refine ⟨133051667134103907681378577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177402222845471876908504769 133051667134103907681378577)
  ·
    refine ⟨99788750350577930761033933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133051667134103907681378577 99788750350577930761033933)
    ·
      refine ⟨37420781381466724035387725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99788750350577930761033933 37420781381466724035387725)
      ·
        refine ⟨14032793018050021513270397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37420781381466724035387725 14032793018050021513270397)
        ·
          refine ⟨5262297381768758067476399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14032793018050021513270397 5262297381768758067476399)
          ·
            refine ⟨7893446072653137101214599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262297381768758067476399 7893446072653137101214599)
            ·
              refine ⟨11840169108979705651821899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893446072653137101214599 11840169108979705651821899)
              ·
                refine ⟨17760253663469558477732849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11840169108979705651821899 17760253663469558477732849)
                ·
                  refine ⟨13320190247602168858299637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17760253663469558477732849 13320190247602168858299637)
                  ·
                    refine ⟨1248767835712703330465591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13320190247602168858299637 1248767835712703330465591)
                    ·
                      rfl

theorem cell23_7295900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_7295900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295900 prefixEnd_7295900 := by exact prefixLift 7295900
  have htrace : WordTrace (prefixWord ++ tailWord_7295900) baseStart_7295900 baseEnd_7295900 := by
    simpa [prefixWord, tailWord_7295900, baseEnd_7295900] using wordTrace_append hprefix tailTrace_7295900
  have hstable : (prefixWord ++ tailWord_7295900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295900).length < 2 ^ (prefixWord ++ tailWord_7295900).sum := by decide
  have hdescent : baseEnd_7295900 < baseStart_7295900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295903 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7295903 : Nat := 118140960795 + 7295903 * 2 ^ 59
def prefixEnd_7295903 : Nat := 4983230072969 + 3 ^ 40 * 7295903 * 2
def baseEnd_7295903 : Nat := 3746305047580073479659259

theorem tailTrace_7295903 : CollatzResearch.WordTrace tailWord_7295903 prefixEnd_7295903 3746305047580073479659259 := by
  unfold tailWord_7295903
  simp only [CollatzResearch.WordTrace]
  refine ⟨266103443687196946875116363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177402295791464631250077575 266103443687196946875116363)
  ·
    refine ⟨399155165530795420312674545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266103443687196946875116363 399155165530795420312674545)
    ·
      refine ⟨299366374148096565234505909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399155165530795420312674545 299366374148096565234505909)
      ·
        refine ⟨28065597576384052990734929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299366374148096565234505909 28065597576384052990734929)
        ·
          refine ⟨21049198182288039743051197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28065597576384052990734929 21049198182288039743051197)
          ·
            refine ⟨7893449318358014903644199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21049198182288039743051197 7893449318358014903644199)
            ·
              refine ⟨11840173977537022355466299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893449318358014903644199 11840173977537022355466299)
              ·
                refine ⟨17760260966305533533199449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11840173977537022355466299 17760260966305533533199449)
                ·
                  refine ⟨13320195724729150149899587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17760260966305533533199449 13320195724729150149899587)
                  ·
                    refine ⟨19980293587093725224849381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13320195724729150149899587 19980293587093725224849381)
                    ·
                      refine ⟨3746305047580073479659259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19980293587093725224849381 3746305047580073479659259)
                      ·
                        rfl

theorem cell23_7295903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7295903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295903 prefixEnd_7295903 := by exact prefixLift 7295903
  have htrace : WordTrace (prefixWord ++ tailWord_7295903) baseStart_7295903 baseEnd_7295903 := by
    simpa [prefixWord, tailWord_7295903, baseEnd_7295903] using wordTrace_append hprefix tailTrace_7295903
  have hstable : (prefixWord ++ tailWord_7295903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295903).length < 2 ^ (prefixWord ++ tailWord_7295903).sum := by decide
  have hdescent : baseEnd_7295903 < baseStart_7295903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295913 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 1, 4]
def baseStart_7295913 : Nat := 118140960795 + 7295913 * 2 ^ 59
def prefixEnd_7295913 : Nat := 4983230072969 + 3 ^ 40 * 7295913 * 2
def baseEnd_7295913 : Nat := 1248770060795539480178071

theorem tailTrace_7295913 : CollatzResearch.WordTrace tailWord_7295913 prefixEnd_7295913 1248770060795539480178071 := by
  unfold tailWord_7295913
  simp only [CollatzResearch.WordTrace]
  refine ⟨266103808417160718582980393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177402538944773812388653595 266103808417160718582980393)
  ·
    refine ⟨199577856312870538937235295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266103808417160718582980393 199577856312870538937235295)
    ·
      refine ⟨299366784469305808405852943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199577856312870538937235295 299366784469305808405852943)
      ·
        refine ⟨449050176703958712608779415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299366784469305808405852943 449050176703958712608779415)
        ·
          refine ⟨673575265055938068913169123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449050176703958712608779415 673575265055938068913169123)
          ·
            refine ⟨1010362897583907103369753685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673575265055938068913169123 1010362897583907103369753685)
            ·
              refine ⟨11840190206061411367614301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1010362897583907103369753685 11840190206061411367614301)
              ·
                refine ⟨4440071327273029262855363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11840190206061411367614301 4440071327273029262855363)
                ·
                  refine ⟨6660106990909543894283045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440071327273029262855363 6660106990909543894283045)
                  ·
                    refine ⟨1248770060795539480178071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660106990909543894283045 1248770060795539480178071)
                    ·
                      rfl

theorem cell23_7295913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 4].length) (baseStart_7295913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295913 prefixEnd_7295913 := by exact prefixLift 7295913
  have htrace : WordTrace (prefixWord ++ tailWord_7295913) baseStart_7295913 baseEnd_7295913 := by
    simpa [prefixWord, tailWord_7295913, baseEnd_7295913] using wordTrace_append hprefix tailTrace_7295913
  have hstable : (prefixWord ++ tailWord_7295913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295913).length < 2 ^ (prefixWord ++ tailWord_7295913).sum := by decide
  have hdescent : baseEnd_7295913 < baseStart_7295913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295929 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7295929 : Nat := 118140960795 + 7295929 * 2 ^ 59
def prefixEnd_7295929 : Nat := 4983230072969 + 3 ^ 40 * 7295929 * 2
def baseEnd_7295929 : Nat := 3746318398077090377934139

theorem tailTrace_7295929 : CollatzResearch.WordTrace tailWord_7295929 prefixEnd_7295929 3746318398077090377934139 := by
  unfold tailWord_7295929
  simp only [CollatzResearch.WordTrace]
  refine ⟨266104391985102753315562841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177402927990068502210375227 266104391985102753315562841)
  ·
    refine ⟨199578293988827064986672131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266104391985102753315562841 199578293988827064986672131)
    ·
      refine ⟨299367440983240597480008197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199578293988827064986672131 299367440983240597480008197)
      ·
        refine ⟨56131395184357612027501537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299367440983240597480008197 56131395184357612027501537)
        ·
          refine ⟨42098546388268209020626153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56131395184357612027501537 42098546388268209020626153)
          ·
            refine ⟨31573909791201156765469615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42098546388268209020626153 31573909791201156765469615)
            ·
              refine ⟨47360864686801735148204423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31573909791201156765469615 47360864686801735148204423)
              ·
                refine ⟨71041297030202602722306635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47360864686801735148204423 71041297030202602722306635)
                ·
                  refine ⟨106561945545303904083459953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71041297030202602722306635 106561945545303904083459953)
                  ·
                    refine ⟨79921459158977928062594965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106561945545303904083459953 79921459158977928062594965)
                    ·
                      refine ⟨3746318398077090377934139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79921459158977928062594965 3746318398077090377934139)
                      ·
                        rfl

theorem cell23_7295929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7295929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295929 prefixEnd_7295929 := by exact prefixLift 7295929
  have htrace : WordTrace (prefixWord ++ tailWord_7295929) baseStart_7295929 baseEnd_7295929 := by
    simpa [prefixWord, tailWord_7295929, baseEnd_7295929] using wordTrace_append hprefix tailTrace_7295929
  have hstable : (prefixWord ++ tailWord_7295929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295929).length < 2 ^ (prefixWord ++ tailWord_7295929).sum := by decide
  have hdescent : baseEnd_7295929 < baseStart_7295929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295969 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_7295969 : Nat := 118140960795 + 7295969 * 2 ^ 59
def prefixEnd_7295969 : Nat := 4983230072969 + 3 ^ 40 * 7295969 * 2
def baseEnd_7295969 : Nat := 1248779645767756740477985

theorem tailTrace_7295969 : CollatzResearch.WordTrace tailWord_7295969 prefixEnd_7295969 1248779645767756740477985 := by
  unfold tailWord_7295969
  simp only [CollatzResearch.WordTrace]
  refine ⟨266105850904957840147018961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177403900603305226764679307 266105850904957840147018961)
  ·
    refine ⟨199579388178718380110264221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266105850904957840147018961 199579388178718380110264221)
    ·
      refine ⟨74842270567019392541349083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199579388178718380110264221 74842270567019392541349083)
      ·
        refine ⟨112263405850529088812023625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74842270567019392541349083 112263405850529088812023625)
        ·
          refine ⟨84197554387896816609017719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112263405850529088812023625 84197554387896816609017719)
          ·
            refine ⟨126296331581845224913526579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84197554387896816609017719 126296331581845224913526579)
            ·
              refine ⟨189444497372767837370289869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126296331581845224913526579 189444497372767837370289869)
              ·
                refine ⟨71041686514787939013858701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189444497372767837370289869 71041686514787939013858701)
                ·
                  refine ⟨26640632443045477130197013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71041686514787939013858701 26640632443045477130197013)
                  ·
                    refine ⟨1248779645767756740477985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26640632443045477130197013 1248779645767756740477985)
                    ·
                      rfl

theorem cell23_7295969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_7295969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295969 prefixEnd_7295969 := by exact prefixLift 7295969
  have htrace : WordTrace (prefixWord ++ tailWord_7295969) baseStart_7295969 baseEnd_7295969 := by
    simpa [prefixWord, tailWord_7295969, baseEnd_7295969] using wordTrace_append hprefix tailTrace_7295969
  have hstable : (prefixWord ++ tailWord_7295969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295969).length < 2 ^ (prefixWord ++ tailWord_7295969).sum := by decide
  have hdescent : baseEnd_7295969 < baseStart_7295969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7295996 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_7295996 : Nat := 118140960795 + 7295996 * 2 ^ 59
def prefixEnd_7295996 : Nat := 4983230072969 + 3 ^ 40 * 7295996 * 2
def baseEnd_7295996 : Nat := 3746352801280941615796331

theorem tailTrace_7295996 : CollatzResearch.WordTrace tailWord_7295996 prefixEnd_7295996 3746352801280941615796331 := by
  unfold tailWord_7295996
  simp only [CollatzResearch.WordTrace]
  refine ⟨133053417837930011879125921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177404557117240015838834561 133053417837930011879125921)
  ·
    refine ⟨99790063378447508909344441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133053417837930011879125921 99790063378447508909344441)
    ·
      refine ⟨74842547533835631682008331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99790063378447508909344441 74842547533835631682008331)
      ·
        refine ⟨112263821300753447523012497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74842547533835631682008331 112263821300753447523012497)
        ·
          refine ⟨84197865975565085642259373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112263821300753447523012497 84197865975565085642259373)
          ·
            refine ⟨31574199740836907115847265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84197865975565085642259373 31574199740836907115847265)
            ·
              refine ⟨23680649805627680336885449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31574199740836907115847265 23680649805627680336885449)
              ·
                refine ⟨17760487354220760252664087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23680649805627680336885449 17760487354220760252664087)
                ·
                  refine ⟨26640731031331140378996131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17760487354220760252664087 26640731031331140378996131)
                  ·
                    refine ⟨39961096546996710568494197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26640731031331140378996131 39961096546996710568494197)
                    ·
                      refine ⟨3746352801280941615796331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39961096546996710568494197 3746352801280941615796331)
                      ·
                        rfl

theorem cell23_7295996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_7295996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7295996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7295996 prefixEnd_7295996 := by exact prefixLift 7295996
  have htrace : WordTrace (prefixWord ++ tailWord_7295996) baseStart_7295996 baseEnd_7295996 := by
    simpa [prefixWord, tailWord_7295996, baseEnd_7295996] using wordTrace_append hprefix tailTrace_7295996
  have hstable : (prefixWord ++ tailWord_7295996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7295996).length < 2 ^ (prefixWord ++ tailWord_7295996).sum := by decide
  have hdescent : baseEnd_7295996 < baseStart_7295996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7295996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296010 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_7296010 : Nat := 118140960795 + 7296010 * 2 ^ 59
def prefixEnd_7296010 : Nat := 4983230072969 + 3 ^ 40 * 7296010 * 2
def baseEnd_7296010 : Nat := 3746359990010104561021267

theorem tailTrace_7296010 : CollatzResearch.WordTrace tailWord_7296010 prefixEnd_7296010 3746359990010104561021267 := by
  unfold tailWord_7296010
  simp only [CollatzResearch.WordTrace]
  refine ⟨66526836574452326037315371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177404897531872869432840989 66526836574452326037315371)
  ·
    refine ⟨99790254861678489055973057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66526836574452326037315371 99790254861678489055973057)
    ·
      refine ⟨74842691146258866791979793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99790254861678489055973057 74842691146258866791979793)
      ·
        refine ⟨56132018359694150093984845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74842691146258866791979793 56132018359694150093984845)
        ·
          refine ⟨21049506884885306285244317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56132018359694150093984845 21049506884885306285244317)
          ·
            refine ⟨7893565081831989856966619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21049506884885306285244317 7893565081831989856966619)
            ·
              refine ⟨11840347622747984785449929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893565081831989856966619 11840347622747984785449929)
              ·
                refine ⟨8880260717060988589087447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11840347622747984785449929 8880260717060988589087447)
                ·
                  refine ⟨13320391075591482883631171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8880260717060988589087447 13320391075591482883631171)
                  ·
                    refine ⟨19980586613387224325446757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13320391075591482883631171 19980586613387224325446757)
                    ·
                      refine ⟨3746359990010104561021267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19980586613387224325446757 3746359990010104561021267)
                      ·
                        rfl

theorem cell23_7296010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_7296010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296010 prefixEnd_7296010 := by exact prefixLift 7296010
  have htrace : WordTrace (prefixWord ++ tailWord_7296010) baseStart_7296010 baseEnd_7296010 := by
    simpa [prefixWord, tailWord_7296010, baseEnd_7296010] using wordTrace_append hprefix tailTrace_7296010
  have hstable : (prefixWord ++ tailWord_7296010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296010).length < 2 ^ (prefixWord ++ tailWord_7296010).sum := by decide
  have hdescent : baseEnd_7296010 < baseStart_7296010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296023 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7296023 : Nat := 118140960795 + 7296023 * 2 ^ 59
def prefixEnd_7296023 : Nat := 4983230072969 + 3 ^ 40 * 7296023 * 2
def baseEnd_7296023 : Nat := 3746366665258613010158707

theorem tailTrace_7296023 : CollatzResearch.WordTrace tailWord_7296023 prefixEnd_7296023 3746366665258613010158707 := by
  unfold tailWord_7296023
  simp only [CollatzResearch.WordTrace]
  refine ⟨266107820446762207369484723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177405213631174804912989815 266107820446762207369484723)
  ·
    refine ⟨399161730670143311054227085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266107820446762207369484723 399161730670143311054227085)
    ·
      refine ⟨149685649001303741645335157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399161730670143311054227085 149685649001303741645335157)
      ·
        refine ⟨14033029593872225779250171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149685649001303741645335157 14033029593872225779250171)
        ·
          refine ⟨21049544390808338668875257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14033029593872225779250171 21049544390808338668875257)
          ·
            refine ⟨15787158293106254001656443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21049544390808338668875257 15787158293106254001656443)
            ·
              refine ⟨23680737439659381002484665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15787158293106254001656443 23680737439659381002484665)
              ·
                refine ⟨17760553079744535751863499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23680737439659381002484665 17760553079744535751863499)
                ·
                  refine ⟨26640829619616803627795249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17760553079744535751863499 26640829619616803627795249)
                  ·
                    refine ⟨19980622214712602720846437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26640829619616803627795249 19980622214712602720846437)
                    ·
                      refine ⟨3746366665258613010158707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19980622214712602720846437 3746366665258613010158707)
                      ·
                        rfl

theorem cell23_7296023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7296023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296023 prefixEnd_7296023 := by exact prefixLift 7296023
  have htrace : WordTrace (prefixWord ++ tailWord_7296023) baseStart_7296023 baseEnd_7296023 := by
    simpa [prefixWord, tailWord_7296023, baseEnd_7296023] using wordTrace_append hprefix tailTrace_7296023
  have hstable : (prefixWord ++ tailWord_7296023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296023).length < 2 ^ (prefixWord ++ tailWord_7296023).sum := by decide
  have hdescent : baseEnd_7296023 < baseStart_7296023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296046 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7296046 : Nat := 118140960795 + 7296046 * 2 ^ 59
def prefixEnd_7296046 : Nat := 4983230072969 + 3 ^ 40 * 7296046 * 2
def baseEnd_7296046 : Nat := 1248792825104555473390367

theorem tailTrace_7296046 : CollatzResearch.WordTrace tailWord_7296046 prefixEnd_7296046 1248792825104555473390367 := by
  unfold tailWord_7296046
  simp only [CollatzResearch.WordTrace]
  refine ⟨33263582415709860287196499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177405772883785921531714661 33263582415709860287196499)
  ·
    refine ⟨49895373623564790430794749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33263582415709860287196499 49895373623564790430794749)
    ·
      refine ⟨18710765108836796411548031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49895373623564790430794749 18710765108836796411548031)
      ·
        refine ⟨28066147663255194617322047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18710765108836796411548031 28066147663255194617322047)
        ·
          refine ⟨42099221494882791925983071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28066147663255194617322047 42099221494882791925983071)
          ·
            refine ⟨63148832242324187888974607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42099221494882791925983071 63148832242324187888974607)
            ·
              refine ⟨94723248363486281833461911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63148832242324187888974607 94723248363486281833461911)
              ·
                refine ⟨142084872545229422750192867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94723248363486281833461911 142084872545229422750192867)
                ·
                  refine ⟨213127308817844134125289301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142084872545229422750192867 213127308817844134125289301)
                  ·
                    refine ⟨1248792825104555473390367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 213127308817844134125289301 1248792825104555473390367)
                    ·
                      rfl

theorem cell23_7296046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7296046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296046 prefixEnd_7296046 := by exact prefixLift 7296046
  have htrace : WordTrace (prefixWord ++ tailWord_7296046) baseStart_7296046 baseEnd_7296046 := by
    simpa [prefixWord, tailWord_7296046, baseEnd_7296046] using wordTrace_append hprefix tailTrace_7296046
  have hstable : (prefixWord ++ tailWord_7296046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296046).length < 2 ^ (prefixWord ++ tailWord_7296046).sum := by decide
  have hdescent : baseEnd_7296046 < baseStart_7296046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296060 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_7296060 : Nat := 118140960795 + 7296060 * 2 ^ 59
def prefixEnd_7296060 : Nat := 4983230072969 + 3 ^ 40 * 7296060 * 2
def baseEnd_7296060 : Nat := 3746385664042829365396037

theorem tailTrace_7296060 : CollatzResearch.WordTrace tailWord_7296060 prefixEnd_7296060 3746385664042829365396037 := by
  unfold tailWord_7296060
  simp only [CollatzResearch.WordTrace]
  refine ⟨133054584973814081344290817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177406113298418775125721089 133054584973814081344290817)
  ·
    refine ⟨99790938730360561008218113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133054584973814081344290817 99790938730360561008218113)
    ·
      refine ⟨74843204047770420756163585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99790938730360561008218113 74843204047770420756163585)
      ·
        refine ⟨56132403035827815567122689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74843204047770420756163585 56132403035827815567122689)
        ·
          refine ⟨42099302276870861675342017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56132403035827815567122689 42099302276870861675342017)
          ·
            refine ⟨31574476707653146256506513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42099302276870861675342017 31574476707653146256506513)
            ·
              refine ⟨23680857530739859692379885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31574476707653146256506513 23680857530739859692379885)
              ·
                refine ⟨8880321574027447384642457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23680857530739859692379885 8880321574027447384642457)
                ·
                  refine ⟨6660241180520585538481843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880321574027447384642457 6660241180520585538481843)
                  ·
                    refine ⟨9990361770780878307722765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6660241180520585538481843 9990361770780878307722765)
                    ·
                      refine ⟨3746385664042829365396037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990361770780878307722765 3746385664042829365396037)
                      ·
                        rfl

theorem cell23_7296060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_7296060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296060 prefixEnd_7296060 := by exact prefixLift 7296060
  have htrace : WordTrace (prefixWord ++ tailWord_7296060) baseStart_7296060 baseEnd_7296060 := by
    simpa [prefixWord, tailWord_7296060, baseEnd_7296060] using wordTrace_append hprefix tailTrace_7296060
  have hstable : (prefixWord ++ tailWord_7296060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296060).length < 2 ^ (prefixWord ++ tailWord_7296060).sum := by decide
  have hdescent : baseEnd_7296060 < baseStart_7296060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296094 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7296094 : Nat := 118140960795 + 7296094 * 2 ^ 59
def prefixEnd_7296094 : Nat := 4983230072969 + 3 ^ 40 * 7296094 * 2
def baseEnd_7296094 : Nat := 3746403122385082232370881

theorem tailTrace_7296094 : CollatzResearch.WordTrace tailWord_7296094 prefixEnd_7296094 3746403122385082232370881 := by
  unfold tailWord_7296094
  simp only [CollatzResearch.WordTrace]
  refine ⟨33263801253688123311914917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177406940019669990996879557 33263801253688123311914917)
  ·
    refine ⟨6236962735066523120984047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33263801253688123311914917 6236962735066523120984047)
    ·
      refine ⟨9355444102599784681476071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6236962735066523120984047 9355444102599784681476071)
      ·
        refine ⟨14033166153899677022214107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9355444102599784681476071 14033166153899677022214107)
        ·
          refine ⟨21049749230849515533321161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14033166153899677022214107 21049749230849515533321161)
          ·
            refine ⟨15787311923137136649990871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21049749230849515533321161 15787311923137136649990871)
            ·
              refine ⟨23680967884705704974986307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15787311923137136649990871 23680967884705704974986307)
              ·
                refine ⟨35521451827058557462479461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23680967884705704974986307 35521451827058557462479461)
                ·
                  refine ⟨6660272217573479524214899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35521451827058557462479461 6660272217573479524214899)
                  ·
                    refine ⟨9990408326360219286322349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6660272217573479524214899 9990408326360219286322349)
                    ·
                      refine ⟨3746403122385082232370881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990408326360219286322349 3746403122385082232370881)
                      ·
                        rfl

theorem cell23_7296094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7296094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296094 prefixEnd_7296094 := by exact prefixLift 7296094
  have htrace : WordTrace (prefixWord ++ tailWord_7296094) baseStart_7296094 baseEnd_7296094 := by
    simpa [prefixWord, tailWord_7296094, baseEnd_7296094] using wordTrace_append hprefix tailTrace_7296094
  have hstable : (prefixWord ++ tailWord_7296094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296094).length < 2 ^ (prefixWord ++ tailWord_7296094).sum := by decide
  have hdescent : baseEnd_7296094 < baseStart_7296094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296096 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_7296096 : Nat := 118140960795 + 7296096 * 2 ^ 59
def prefixEnd_7296096 : Nat := 4983230072969 + 3 ^ 40 * 7296096 * 2
def baseEnd_7296096 : Nat := 3746404149346391224545871

theorem tailTrace_7296096 : CollatzResearch.WordTrace tailWord_7296096 prefixEnd_7296096 3746404149346391224545871 := by
  unfold tailWord_7296096
  simp only [CollatzResearch.WordTrace]
  refine ⟨133055241487748870418446071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177406988650331827224594761 133055241487748870418446071)
  ·
    refine ⟨199582862231623305627669107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133055241487748870418446071 199582862231623305627669107)
    ·
      refine ⟨299374293347434958441503661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199582862231623305627669107 299374293347434958441503661)
      ·
        refine ⟨112265360005288109415563873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299374293347434958441503661 112265360005288109415563873)
        ·
          refine ⟨84199020003966082061672905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112265360005288109415563873 84199020003966082061672905)
          ·
            refine ⟨63149265002974561546254679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84199020003966082061672905 63149265002974561546254679)
            ·
              refine ⟨94723897504461842319382019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63149265002974561546254679 94723897504461842319382019)
              ·
                refine ⟨142085846256692763479073029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94723897504461842319382019 142085846256692763479073029)
                ·
                  refine ⟨26641096173129893152326193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142085846256692763479073029 26641096173129893152326193)
                  ·
                    refine ⟨19980822129847419864244645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26641096173129893152326193 19980822129847419864244645)
                    ·
                      refine ⟨3746404149346391224545871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19980822129847419864244645 3746404149346391224545871)
                      ·
                        rfl

theorem cell23_7296096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_7296096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296096 prefixEnd_7296096 := by exact prefixLift 7296096
  have htrace : WordTrace (prefixWord ++ tailWord_7296096) baseStart_7296096 baseEnd_7296096 := by
    simpa [prefixWord, tailWord_7296096, baseEnd_7296096] using wordTrace_append hprefix tailTrace_7296096
  have hstable : (prefixWord ++ tailWord_7296096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296096).length < 2 ^ (prefixWord ++ tailWord_7296096).sum := by decide
  have hdescent : baseEnd_7296096 < baseStart_7296096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296183 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 5, 4]
def baseStart_7296183 : Nat := 118140960795 + 7296183 * 2 ^ 59
def prefixEnd_7296183 : Nat := 4983230072969 + 3 ^ 40 * 7296183 * 2
def baseEnd_7296183 : Nat := 1248816274054444128052657

theorem tailTrace_7296183 : CollatzResearch.WordTrace tailWord_7296183 prefixEnd_7296183 1248816274054444128052657 := by
  unfold tailWord_7296183
  simp only [CollatzResearch.WordTrace]
  refine ⟨266113656126182554695309203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177409104084121703130206135 266113656126182554695309203)
  ·
    refine ⟨399170484189273832042963805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266113656126182554695309203 399170484189273832042963805)
    ·
      refine ⟨149688931570977687016111427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399170484189273832042963805 149688931570977687016111427)
      ·
        refine ⟨224533397356466530524167141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149688931570977687016111427 224533397356466530524167141)
        ·
          refine ⟨42100012004337474473281339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224533397356466530524167141 42100012004337474473281339)
          ·
            refine ⟨63150018006506211709922009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42100012004337474473281339 63150018006506211709922009)
            ·
              refine ⟨47362513504879658782441507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63150018006506211709922009 47362513504879658782441507)
              ·
                refine ⟨71043770257319488173662261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47362513504879658782441507 71043770257319488173662261)
                ·
                  refine ⟨6660353461623702016280837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71043770257319488173662261 6660353461623702016280837)
                  ·
                    refine ⟨1248816274054444128052657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660353461623702016280837 1248816274054444128052657)
                    ·
                      rfl

theorem cell23_7296183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_7296183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296183 prefixEnd_7296183 := by exact prefixLift 7296183
  have htrace : WordTrace (prefixWord ++ tailWord_7296183) baseStart_7296183 baseEnd_7296183 := by
    simpa [prefixWord, tailWord_7296183, baseEnd_7296183] using wordTrace_append hprefix tailTrace_7296183
  have hstable : (prefixWord ++ tailWord_7296183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296183).length < 2 ^ (prefixWord ++ tailWord_7296183).sum := by decide
  have hdescent : baseEnd_7296183 < baseStart_7296183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296186 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_7296186 : Nat := 118140960795 + 7296186 * 2 ^ 59
def prefixEnd_7296186 : Nat := 4983230072969 + 3 ^ 40 * 7296186 * 2
def baseEnd_7296186 : Nat := 3746450362605295872420457

theorem tailTrace_7296186 : CollatzResearch.WordTrace tailWord_7296186 prefixEnd_7296186 3746450362605295872420457 := by
  unfold tailWord_7296186
  simp only [CollatzResearch.WordTrace]
  refine ⟨66528441386292921551917103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177409177030114457471778941 66528441386292921551917103)
  ·
    refine ⟨99792662079439382327875655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66528441386292921551917103 99792662079439382327875655)
    ·
      refine ⟨149688993119159073491813483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99792662079439382327875655 149688993119159073491813483)
      ·
        refine ⟨224533489678738610237720225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149688993119159073491813483 224533489678738610237720225)
        ·
          refine ⟨168400117259053957678290169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224533489678738610237720225 168400117259053957678290169)
          ·
            refine ⟨126300087944290468258717627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168400117259053957678290169 126300087944290468258717627)
            ·
              refine ⟨189450131916435702388076441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126300087944290468258717627 189450131916435702388076441)
              ·
                refine ⟨142087598937326776791057331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189450131916435702388076441 142087598937326776791057331)
                ·
                  refine ⟨213131398405990165186585997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142087598937326776791057331 213131398405990165186585997)
                  ·
                    refine ⟨79924274402246311944969749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213131398405990165186585997 79924274402246311944969749)
                    ·
                      refine ⟨3746450362605295872420457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79924274402246311944969749 3746450362605295872420457)
                      ·
                        rfl

theorem cell23_7296186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_7296186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296186 prefixEnd_7296186 := by exact prefixLift 7296186
  have htrace : WordTrace (prefixWord ++ tailWord_7296186) baseStart_7296186 baseEnd_7296186 := by
    simpa [prefixWord, tailWord_7296186, baseEnd_7296186] using wordTrace_append hprefix tailTrace_7296186
  have hstable : (prefixWord ++ tailWord_7296186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296186).length < 2 ^ (prefixWord ++ tailWord_7296186).sum := by decide
  have hdescent : baseEnd_7296186 < baseStart_7296186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296190 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_7296190 : Nat := 118140960795 + 7296190 * 2 ^ 59
def prefixEnd_7296190 : Nat := 4983230072969 + 3 ^ 40 * 7296190 * 2
def baseEnd_7296190 : Nat := 3746452416527913856770439

theorem tailTrace_7296190 : CollatzResearch.WordTrace tailWord_7296190 prefixEnd_7296190 3746452416527913856770439 := by
  unfold tailWord_7296190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33264238929644649361351753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177409274291438129927209349 33264238929644649361351753)
  ·
    refine ⟨24948179197233487021013815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33264238929644649361351753 24948179197233487021013815)
    ·
      refine ⟨37422268795850230531520723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24948179197233487021013815 37422268795850230531520723)
      ·
        refine ⟨56133403193775345797281085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37422268795850230531520723 56133403193775345797281085)
        ·
          refine ⟨21050026197665754673980407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56133403193775345797281085 21050026197665754673980407)
          ·
            refine ⟨31575039296498632010970611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21050026197665754673980407 31575039296498632010970611)
            ·
              refine ⟨47362558944747948016455917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31575039296498632010970611 47362558944747948016455917)
              ·
                refine ⟨17760959604280480506170969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47362558944747948016455917 17760959604280480506170969)
                ·
                  refine ⟨13320719703210360379628227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17760959604280480506170969 13320719703210360379628227)
                  ·
                    refine ⟨19981079554815540569442341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13320719703210360379628227 19981079554815540569442341)
                    ·
                      refine ⟨3746452416527913856770439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19981079554815540569442341 3746452416527913856770439)
                      ·
                        rfl

theorem cell23_7296190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_7296190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296190 prefixEnd_7296190 := by exact prefixLift 7296190
  have htrace : WordTrace (prefixWord ++ tailWord_7296190) baseStart_7296190 baseEnd_7296190 := by
    simpa [prefixWord, tailWord_7296190, baseEnd_7296190] using wordTrace_append hprefix tailTrace_7296190
  have hstable : (prefixWord ++ tailWord_7296190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296190).length < 2 ^ (prefixWord ++ tailWord_7296190).sum := by decide
  have hdescent : baseEnd_7296190 < baseStart_7296190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296210 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7296210 : Nat := 118140960795 + 7296210 * 2 ^ 59
def prefixEnd_7296210 : Nat := 4983230072969 + 3 ^ 40 * 7296210 * 2
def baseEnd_7296210 : Nat := 3746462686141003778520347

theorem tailTrace_7296210 : CollatzResearch.WordTrace tailWord_7296210 prefixEnd_7296210 3746462686141003778520347 := by
  unfold tailWord_7296210
  simp only [CollatzResearch.WordTrace]
  refine ⟨66528660224271184576635521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177409760598056492204361389 66528660224271184576635521)
  ·
    refine ⟨49896495168203388432476641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66528660224271184576635521 49896495168203388432476641)
    ·
      refine ⟨37422371376152541324357481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49896495168203388432476641 37422371376152541324357481)
      ·
        refine ⟨28066778532114405993268111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37422371376152541324357481 28066778532114405993268111)
        ·
          refine ⟨42100167798171608989902167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28066778532114405993268111 42100167798171608989902167)
          ·
            refine ⟨63150251697257413484853251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42100167798171608989902167 63150251697257413484853251)
            ·
              refine ⟨94725377545886120227279877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63150251697257413484853251 94725377545886120227279877)
              ·
                refine ⟨17761008289853647542614977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94725377545886120227279877 17761008289853647542614977)
                ·
                  refine ⟨13320756217390235656961233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17761008289853647542614977 13320756217390235656961233)
                  ·
                    refine ⟨9990567163042676742720925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13320756217390235656961233 9990567163042676742720925)
                    ·
                      refine ⟨3746462686141003778520347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990567163042676742720925 3746462686141003778520347)
                      ·
                        rfl

theorem cell23_7296210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7296210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296210 prefixEnd_7296210 := by exact prefixLift 7296210
  have htrace : WordTrace (prefixWord ++ tailWord_7296210) baseStart_7296210 baseEnd_7296210 := by
    simpa [prefixWord, tailWord_7296210, baseEnd_7296210] using wordTrace_append hprefix tailTrace_7296210
  have hstable : (prefixWord ++ tailWord_7296210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296210).length < 2 ^ (prefixWord ++ tailWord_7296210).sum := by decide
  have hdescent : baseEnd_7296210 < baseStart_7296210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296243 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 3, 5]
def baseStart_7296243 : Nat := 118140960795 + 7296243 * 2 ^ 59
def prefixEnd_7296243 : Nat := 4983230072969 + 3 ^ 40 * 7296243 * 2
def baseEnd_7296243 : Nat := 1248826543667534049802565

theorem tailTrace_7296243 : CollatzResearch.WordTrace tailWord_7296243 prefixEnd_7296243 1248826543667534049802565 := by
  unfold tailWord_7296243
  simp only [CollatzResearch.WordTrace]
  refine ⟨266115844505965184942493383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177410563003976789961662255 266115844505965184942493383)
  ·
    refine ⟨399173766758947777413740075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266115844505965184942493383 399173766758947777413740075)
    ·
      refine ⟨598760650138421666120610113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399173766758947777413740075 598760650138421666120610113)
      ·
        refine ⟨449070487603816249590457585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598760650138421666120610113 449070487603816249590457585)
        ·
          refine ⟨336802865702862187192843189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449070487603816249590457585 336802865702862187192843189)
          ·
            refine ⟨31575268659643330049329049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 336802865702862187192843189 31575268659643330049329049)
            ·
              refine ⟨23681451494732497536996787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31575268659643330049329049 23681451494732497536996787)
              ·
                refine ⟨35522177242098746305495181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23681451494732497536996787 35522177242098746305495181)
                ·
                  refine ⟨13320816465787029864560693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35522177242098746305495181 13320816465787029864560693)
                  ·
                    refine ⟨1248826543667534049802565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13320816465787029864560693 1248826543667534049802565)
                    ·
                      rfl

theorem cell23_7296243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 5].length) (baseStart_7296243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296243 prefixEnd_7296243 := by exact prefixLift 7296243
  have htrace : WordTrace (prefixWord ++ tailWord_7296243) baseStart_7296243 baseEnd_7296243 := by
    simpa [prefixWord, tailWord_7296243, baseEnd_7296243] using wordTrace_append hprefix tailTrace_7296243
  have hstable : (prefixWord ++ tailWord_7296243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296243).length < 2 ^ (prefixWord ++ tailWord_7296243).sum := by decide
  have hdescent : baseEnd_7296243 < baseStart_7296243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296250 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2]
def baseStart_7296250 : Nat := 118140960795 + 7296250 * 2 ^ 59
def prefixEnd_7296250 : Nat := 4983230072969 + 3 ^ 40 * 7296250 * 2
def baseEnd_7296250 : Nat := 3746483225367183622020163

theorem tailTrace_7296250 : CollatzResearch.WordTrace tailWord_7296250 prefixEnd_7296250 3746483225367183622020163 := by
  unfold tailWord_7296250
  simp only [CollatzResearch.WordTrace]
  refine ⟨66529024954234956284499551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177410733211293216758665469 66529024954234956284499551)
  ·
    refine ⟨99793537431352434426749327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66529024954234956284499551 99793537431352434426749327)
    ·
      refine ⟨149690306147028651640123991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99793537431352434426749327 149690306147028651640123991)
      ·
        refine ⟨224535459220542977460185987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149690306147028651640123991 224535459220542977460185987)
        ·
          refine ⟨336803188830814466190278981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224535459220542977460185987 336803188830814466190278981)
          ·
            refine ⟨63150597905777712410677309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336803188830814466190278981 63150597905777712410677309)
            ·
              refine ⟨23681474214666642154003991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63150597905777712410677309 23681474214666642154003991)
              ·
                refine ⟨35522211321999963231005987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23681474214666642154003991 35522211321999963231005987)
                ·
                  refine ⟨53283316982999944846508981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35522211321999963231005987 53283316982999944846508981)
                  ·
                    refine ⟨4995310967156244829360217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53283316982999944846508981 4995310967156244829360217)
                    ·
                      refine ⟨3746483225367183622020163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995310967156244829360217 3746483225367183622020163)
                      ·
                        rfl

theorem cell23_7296250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_7296250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296250 prefixEnd_7296250 := by exact prefixLift 7296250
  have htrace : WordTrace (prefixWord ++ tailWord_7296250) baseStart_7296250 baseEnd_7296250 := by
    simpa [prefixWord, tailWord_7296250, baseEnd_7296250] using wordTrace_append hprefix tailTrace_7296250
  have hstable : (prefixWord ++ tailWord_7296250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296250).length < 2 ^ (prefixWord ++ tailWord_7296250).sum := by decide
  have hdescent : baseEnd_7296250 < baseStart_7296250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296357 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 3, 3, 2]
def baseStart_7296357 : Nat := 118140960795 + 7296357 * 2 ^ 59
def prefixEnd_7296357 : Nat := 4983230072969 + 3 ^ 40 * 7296357 * 2
def baseEnd_7296357 : Nat := 3746538167797214703382171

theorem tailTrace_7296357 : CollatzResearch.WordTrace tailWord_7296357 prefixEnd_7296357 3746538167797214703382171 := by
  unfold tailWord_7296357
  simp only [CollatzResearch.WordTrace]
  refine ⟨266120002427552182412143325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177413334951701454941428883 266120002427552182412143325)
  ·
    refine ⟨99795000910332068404553747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266120002427552182412143325 99795000910332068404553747)
    ·
      refine ⟨149692501365498102606830621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99795000910332068404553747 149692501365498102606830621)
      ·
        refine ⟨56134688012061788477561483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149692501365498102606830621 56134688012061788477561483)
        ·
          refine ⟨84202032018092682716342225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56134688012061788477561483 84202032018092682716342225)
          ·
            refine ⟨63151524013569512037256669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84202032018092682716342225 63151524013569512037256669)
            ·
              refine ⟨23681821505088567013971251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63151524013569512037256669 23681821505088567013971251)
              ·
                refine ⟨35522732257632850520956877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23681821505088567013971251 35522732257632850520956877)
                ·
                  refine ⟨13321024596612318945358829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35522732257632850520956877 13321024596612318945358829)
                  ·
                    refine ⟨4995384223729619604509561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13321024596612318945358829 4995384223729619604509561)
                    ·
                      refine ⟨3746538167797214703382171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995384223729619604509561 3746538167797214703382171)
                      ·
                        rfl

theorem cell23_7296357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_7296357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296357 prefixEnd_7296357 := by exact prefixLift 7296357
  have htrace : WordTrace (prefixWord ++ tailWord_7296357) baseStart_7296357 baseEnd_7296357 := by
    simpa [prefixWord, tailWord_7296357, baseEnd_7296357] using wordTrace_append hprefix tailTrace_7296357
  have hstable : (prefixWord ++ tailWord_7296357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296357).length < 2 ^ (prefixWord ++ tailWord_7296357).sum := by decide
  have hdescent : baseEnd_7296357 < baseStart_7296357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296404 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7296404 : Nat := 118140960795 + 7296404 * 2 ^ 59
def prefixEnd_7296404 : Nat := 4983230072969 + 3 ^ 40 * 7296404 * 2
def baseEnd_7296404 : Nat := 3746562301387976019494455

theorem tailTrace_7296404 : CollatzResearch.WordTrace tailWord_7296404 prefixEnd_7296404 3746562301387976019494455 := by
  unfold tailWord_7296404
  simp only [CollatzResearch.WordTrace]
  refine ⟨133060858329190954719552133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177414477772254606292736177 133060858329190954719552133)
  ·
    refine ⟨24948910936723304009916025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133060858329190954719552133 24948910936723304009916025)
    ·
      refine ⟨18711683202542478007437019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24948910936723304009916025 18711683202542478007437019)
      ·
        refine ⟨28067524803813717011155529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18711683202542478007437019 28067524803813717011155529)
        ·
          refine ⟨21050643602860287758366647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28067524803813717011155529 21050643602860287758366647)
          ·
            refine ⟨31575965404290431637549971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21050643602860287758366647 31575965404290431637549971)
            ·
              refine ⟨47363948106435647456324957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31575965404290431637549971 47363948106435647456324957)
              ·
                refine ⟨17761480539913367796121859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47363948106435647456324957 17761480539913367796121859)
                ·
                  refine ⟨26642220809870051694182789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17761480539913367796121859 26642220809870051694182789)
                  ·
                    refine ⟨4995416401850634692659273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26642220809870051694182789 4995416401850634692659273)
                    ·
                      refine ⟨3746562301387976019494455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995416401850634692659273 3746562301387976019494455)
                      ·
                        rfl

theorem cell23_7296404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7296404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296404 prefixEnd_7296404 := by exact prefixLift 7296404
  have htrace : WordTrace (prefixWord ++ tailWord_7296404) baseStart_7296404 baseEnd_7296404 := by
    simpa [prefixWord, tailWord_7296404, baseEnd_7296404] using wordTrace_append hprefix tailTrace_7296404
  have hstable : (prefixWord ++ tailWord_7296404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296404).length < 2 ^ (prefixWord ++ tailWord_7296404).sum := by decide
  have hdescent : baseEnd_7296404 < baseStart_7296404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296410 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_7296410 : Nat := 118140960795 + 7296410 * 2 ^ 59
def prefixEnd_7296410 : Nat := 4983230072969 + 3 ^ 40 * 7296410 * 2
def baseEnd_7296410 : Nat := 416285042474655888446603

theorem tailTrace_7296410 : CollatzResearch.WordTrace tailWord_7296410 prefixEnd_7296410 416285042474655888446603 := by
  unfold tailWord_7296410
  simp only [CollatzResearch.WordTrace]
  refine ⟨66530483874090043115955671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177414623664240114975881789 66530483874090043115955671)
  ·
    refine ⟨99795725811135064673933507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66530483874090043115955671 99795725811135064673933507)
    ·
      refine ⟨149693588716702597010900261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99795725811135064673933507 149693588716702597010900261)
      ·
        refine ⟨28067547884381736939543799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149693588716702597010900261 28067547884381736939543799)
        ·
          refine ⟨42101321826572605409315699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28067547884381736939543799 42101321826572605409315699)
          ·
            refine ⟨63151982739858908113973549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42101321826572605409315699 63151982739858908113973549)
            ·
              refine ⟨23681993527447090542740081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63151982739858908113973549 23681993527447090542740081)
              ·
                refine ⟨17761495145585317907055061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23681993527447090542740081 17761495145585317907055061)
                ·
                  refine ⟨416285042474655888446603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17761495145585317907055061 416285042474655888446603)
                  ·
                    rfl

theorem cell23_7296410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_7296410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296410 prefixEnd_7296410 := by exact prefixLift 7296410
  have htrace : WordTrace (prefixWord ++ tailWord_7296410) baseStart_7296410 baseEnd_7296410 := by
    simpa [prefixWord, tailWord_7296410, baseEnd_7296410] using wordTrace_append hprefix tailTrace_7296410
  have hstable : (prefixWord ++ tailWord_7296410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296410).length < 2 ^ (prefixWord ++ tailWord_7296410).sum := by decide
  have hdescent : baseEnd_7296410 < baseStart_7296410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296420 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_7296420 : Nat := 118140960795 + 7296420 * 2 ^ 59
def prefixEnd_7296420 : Nat := 4983230072969 + 3 ^ 40 * 7296420 * 2
def baseEnd_7296420 : Nat := 3746570517078447956894381

theorem tailTrace_7296420 : CollatzResearch.WordTrace tailWord_7296420 prefixEnd_7296420 3746570517078447956894381 := by
  unfold tailWord_7296420
  simp only [CollatzResearch.WordTrace]
  refine ⟨133061150113161972085843357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177414866817549296114457809 133061150113161972085843357)
  ·
    refine ⟨49897931292435739532191259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133061150113161972085843357 49897931292435739532191259)
    ·
      refine ⟨74846896938653609298286889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49897931292435739532191259 74846896938653609298286889)
      ·
        refine ⟨56135172703990206973715167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74846896938653609298286889 56135172703990206973715167)
        ·
          refine ⟨84202759055985310460572751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56135172703990206973715167 84202759055985310460572751)
          ·
            refine ⟨126304138583977965690859127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84202759055985310460572751 126304138583977965690859127)
            ·
              refine ⟨189456207875966948536288691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126304138583977965690859127 189456207875966948536288691)
              ·
                refine ⟨284184311813950422804433037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189456207875966948536288691 284184311813950422804433037)
                ·
                  refine ⟨106569116930231408551662389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284184311813950422804433037 106569116930231408551662389)
                  ·
                    refine ⟨9990854712209194551718349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106569116930231408551662389 9990854712209194551718349)
                    ·
                      refine ⟨3746570517078447956894381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990854712209194551718349 3746570517078447956894381)
                      ·
                        rfl

theorem cell23_7296420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_7296420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296420 prefixEnd_7296420 := by exact prefixLift 7296420
  have htrace : WordTrace (prefixWord ++ tailWord_7296420) baseStart_7296420 baseEnd_7296420 := by
    simpa [prefixWord, tailWord_7296420, baseEnd_7296420] using wordTrace_append hprefix tailTrace_7296420
  have hstable : (prefixWord ++ tailWord_7296420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296420).length < 2 ^ (prefixWord ++ tailWord_7296420).sum := by decide
  have hdescent : baseEnd_7296420 < baseStart_7296420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296437 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_7296437 : Nat := 118140960795 + 7296437 * 2 ^ 59
def prefixEnd_7296437 : Nat := 4983230072969 + 3 ^ 40 * 7296437 * 2
def baseEnd_7296437 : Nat := 3746579246249574390381803

theorem tailTrace_7296437 : CollatzResearch.WordTrace tailWord_7296437 prefixEnd_7296437 3746579246249574390381803 := by
  unfold tailWord_7296437
  simp only [CollatzResearch.WordTrace]
  refine ⟨266122920267262356075055565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177415280178174904050037043 266122920267262356075055565)
  ·
    refine ⟨99796095100223383528145837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266122920267262356075055565 99796095100223383528145837)
    ·
      refine ⟨37423535662583768823054689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99796095100223383528145837 37423535662583768823054689)
      ·
        refine ⟨28067651746937826617291017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37423535662583768823054689 28067651746937826617291017)
        ·
          refine ⟨21050738810203369962968263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28067651746937826617291017 21050738810203369962968263)
          ·
            refine ⟨31576108215305054944452395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21050738810203369962968263 31576108215305054944452395)
            ·
              refine ⟨47364162322957582416678593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31576108215305054944452395 47364162322957582416678593)
              ·
                refine ⟨35523121742218186812508945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47364162322957582416678593 35523121742218186812508945)
                ·
                  refine ⟨26642341306663640109381709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35523121742218186812508945 26642341306663640109381709)
                  ·
                    refine ⟨9990877989998865041018141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26642341306663640109381709 9990877989998865041018141)
                    ·
                      refine ⟨3746579246249574390381803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990877989998865041018141 3746579246249574390381803)
                      ·
                        rfl

theorem cell23_7296437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_7296437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296437 prefixEnd_7296437 := by exact prefixLift 7296437
  have htrace : WordTrace (prefixWord ++ tailWord_7296437) baseStart_7296437 baseEnd_7296437 := by
    simpa [prefixWord, tailWord_7296437, baseEnd_7296437] using wordTrace_append hprefix tailTrace_7296437
  have hstable : (prefixWord ++ tailWord_7296437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296437).length < 2 ^ (prefixWord ++ tailWord_7296437).sum := by decide
  have hdescent : baseEnd_7296437 < baseStart_7296437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296440 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_7296440 : Nat := 118140960795 + 7296440 * 2 ^ 59
def prefixEnd_7296440 : Nat := 4983230072969 + 3 ^ 40 * 7296440 * 2
def baseEnd_7296440 : Nat := 1248860262230512626214763

theorem tailTrace_7296440 : CollatzResearch.WordTrace tailWord_7296440 prefixEnd_7296440 1248860262230512626214763 := by
  unfold tailWord_7296440
  simp only [CollatzResearch.WordTrace]
  refine ⟨133061514843125743793707387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177415353124167658391609849 133061514843125743793707387)
  ·
    refine ⟨199592272264688615690561081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133061514843125743793707387 199592272264688615690561081)
    ·
      refine ⟨149694204198516461767920811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199592272264688615690561081 149694204198516461767920811)
      ·
        refine ⟨224541306297774692651881217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149694204198516461767920811 224541306297774692651881217)
        ·
          refine ⟨168405979723331019488910913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224541306297774692651881217 168405979723331019488910913)
          ·
            refine ⟨126304484792498264616683185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168405979723331019488910913 126304484792498264616683185)
            ·
              refine ⟨94728363594373698462512389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126304484792498264616683185 94728363594373698462512389)
              ·
                refine ⟨17761568173945068461721073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94728363594373698462512389 17761568173945068461721073)
                ·
                  refine ⟨13321176130458801346290805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17761568173945068461721073 13321176130458801346290805)
                  ·
                    refine ⟨1248860262230512626214763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13321176130458801346290805 1248860262230512626214763)
                    ·
                      rfl

theorem cell23_7296440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_7296440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296440 prefixEnd_7296440 := by exact prefixLift 7296440
  have htrace : WordTrace (prefixWord ++ tailWord_7296440) baseStart_7296440 baseEnd_7296440 := by
    simpa [prefixWord, tailWord_7296440, baseEnd_7296440] using wordTrace_append hprefix tailTrace_7296440
  have hstable : (prefixWord ++ tailWord_7296440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296440).length < 2 ^ (prefixWord ++ tailWord_7296440).sum := by decide
  have hdescent : baseEnd_7296440 < baseStart_7296440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296443 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_7296443 : Nat := 118140960795 + 7296443 * 2 ^ 59
def prefixEnd_7296443 : Nat := 4983230072969 + 3 ^ 40 * 7296443 * 2
def baseEnd_7296443 : Nat := 3746582327133501366906775

theorem tailTrace_7296443 : CollatzResearch.WordTrace tailWord_7296443 prefixEnd_7296443 3746582327133501366906775 := by
  unfold tailWord_7296443
  simp only [CollatzResearch.WordTrace]
  refine ⟨266123139105240619099773983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177415426070160412733182655 266123139105240619099773983)
  ·
    refine ⟨399184708657860928649660975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266123139105240619099773983 399184708657860928649660975)
    ·
      refine ⟨598777062986791392974491463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399184708657860928649660975 598777062986791392974491463)
      ·
        refine ⟨898165594480187089461737195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598777062986791392974491463 898165594480187089461737195)
        ·
          refine ⟨1347248391720280634192605793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898165594480187089461737195 1347248391720280634192605793)
          ·
            refine ⟨1010436293790210475644454345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347248391720280634192605793 1010436293790210475644454345)
            ·
              refine ⟨757827220342657856733340759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010436293790210475644454345 757827220342657856733340759)
              ·
                refine ⟨1136740830513986785100011139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757827220342657856733340759 1136740830513986785100011139)
                ·
                  refine ⟨1705111245770980177650016709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136740830513986785100011139 1705111245770980177650016709)
                  ·
                    refine ⟨319708358582058783309378133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1705111245770980177650016709 319708358582058783309378133)
                    ·
                      refine ⟨3746582327133501366906775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319708358582058783309378133 3746582327133501366906775)
                      ·
                        rfl

theorem cell23_7296443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_7296443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296443 prefixEnd_7296443 := by exact prefixLift 7296443
  have htrace : WordTrace (prefixWord ++ tailWord_7296443) baseStart_7296443 baseEnd_7296443 := by
    simpa [prefixWord, tailWord_7296443, baseEnd_7296443] using wordTrace_append hprefix tailTrace_7296443
  have hstable : (prefixWord ++ tailWord_7296443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296443).length < 2 ^ (prefixWord ++ tailWord_7296443).sum := by decide
  have hdescent : baseEnd_7296443 < baseStart_7296443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296477 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7296477 : Nat := 118140960795 + 7296477 * 2 ^ 59
def prefixEnd_7296477 : Nat := 4983230072969 + 3 ^ 40 * 7296477 * 2
def baseEnd_7296477 : Nat := 3746599785475754233881619

theorem tailTrace_7296477 : CollatzResearch.WordTrace tailWord_7296477 prefixEnd_7296477 3746599785475754233881619 := by
  unfold tailWord_7296477
  simp only [CollatzResearch.WordTrace]
  refine ⟨266124379187117442906511685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177416252791411628604341123 266124379187117442906511685)
  ·
    refine ⟨49898321097584520544970941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266124379187117442906511685 49898321097584520544970941)
    ·
      refine ⟨18711870411594195204364103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49898321097584520544970941 18711870411594195204364103)
      ·
        refine ⟨28067805617391292806546155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18711870411594195204364103 28067805617391292806546155)
        ·
          refine ⟨42101708426086939209819233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28067805617391292806546155 42101708426086939209819233)
          ·
            refine ⟨31576281319565204407364425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42101708426086939209819233 31576281319565204407364425)
            ·
              refine ⟨23682210989673903305523319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31576281319565204407364425 23682210989673903305523319)
              ·
                refine ⟨35523316484510854958284979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23682210989673903305523319 35523316484510854958284979)
                ·
                  refine ⟨53284974726766282437427469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35523316484510854958284979 53284974726766282437427469)
                  ·
                    refine ⟨19981865522537355914035301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53284974726766282437427469 19981865522537355914035301)
                    ·
                      refine ⟨3746599785475754233881619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19981865522537355914035301 3746599785475754233881619)
                      ·
                        rfl

theorem cell23_7296477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7296477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296477 prefixEnd_7296477 := by exact prefixLift 7296477
  have htrace : WordTrace (prefixWord ++ tailWord_7296477) baseStart_7296477 baseEnd_7296477 := by
    simpa [prefixWord, tailWord_7296477, baseEnd_7296477] using wordTrace_append hprefix tailTrace_7296477
  have hstable : (prefixWord ++ tailWord_7296477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296477).length < 2 ^ (prefixWord ++ tailWord_7296477).sum := by decide
  have hdescent : baseEnd_7296477 < baseStart_7296477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296497 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_7296497 : Nat := 118140960795 + 7296497 * 2 ^ 59
def prefixEnd_7296497 : Nat := 4983230072969 + 3 ^ 40 * 7296497 * 2
def baseEnd_7296497 : Nat := 3746610055088844155631527

theorem tailTrace_7296497 : CollatzResearch.WordTrace tailWord_7296497 prefixEnd_7296497 3746610055088844155631527 := by
  unfold tailWord_7296497
  simp only [CollatzResearch.WordTrace]
  refine ⟨266125108647044986322239745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177416739098029990881493163 266125108647044986322239745)
  ·
    refine ⟨199593831485283739741679809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266125108647044986322239745 199593831485283739741679809)
    ·
      refine ⟨149695373613962804806259857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199593831485283739741679809 149695373613962804806259857)
      ·
        refine ⟨112271530210472103604694893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149695373613962804806259857 112271530210472103604694893)
        ·
          refine ⟨42101823828927038851760585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112271530210472103604694893 42101823828927038851760585)
          ·
            refine ⟨31576367871695279138820439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42101823828927038851760585 31576367871695279138820439)
            ·
              refine ⟨47364551807542918708230659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31576367871695279138820439 47364551807542918708230659)
              ·
                refine ⟨71046827711314378062345989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47364551807542918708230659 71046827711314378062345989)
                ·
                  refine ⟨13321280195871445886689873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71046827711314378062345989 13321280195871445886689873)
                  ·
                    refine ⟨9990960146903584415017405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13321280195871445886689873 9990960146903584415017405)
                    ·
                      refine ⟨3746610055088844155631527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9990960146903584415017405 3746610055088844155631527)
                      ·
                        rfl

theorem cell23_7296497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_7296497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296497 prefixEnd_7296497 := by exact prefixLift 7296497
  have htrace : WordTrace (prefixWord ++ tailWord_7296497) baseStart_7296497 baseEnd_7296497 := by
    simpa [prefixWord, tailWord_7296497, baseEnd_7296497] using wordTrace_append hprefix tailTrace_7296497
  have hstable : (prefixWord ++ tailWord_7296497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296497).length < 2 ^ (prefixWord ++ tailWord_7296497).sum := by decide
  have hdescent : baseEnd_7296497 < baseStart_7296497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296504 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 3, 4]
def baseStart_7296504 : Nat := 118140960795 + 7296504 * 2 ^ 59
def prefixEnd_7296504 : Nat := 4983230072969 + 3 ^ 40 * 7296504 * 2
def baseEnd_7296504 : Nat := 1248871216484475209414665

theorem tailTrace_7296504 : CollatzResearch.WordTrace tailWord_7296504 prefixEnd_7296504 1248871216484475209414665 := by
  unfold tailWord_7296504
  simp only [CollatzResearch.WordTrace]
  refine ⟨133062681979009813258872283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177416909305346417678496377 133062681979009813258872283)
  ·
    refine ⟨199594022968514719888308425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133062681979009813258872283 199594022968514719888308425)
    ·
      refine ⟨149695517226386039916231319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199594022968514719888308425 149695517226386039916231319)
      ·
        refine ⟨224543275839579059874346979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149695517226386039916231319 224543275839579059874346979)
        ·
          refine ⟨336814913759368589811520469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224543275839579059874346979 336814913759368589811520469)
          ·
            refine ⟨7894099541235201323707511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 336814913759368589811520469 7894099541235201323707511)
            ·
              refine ⟨11841149311852801985561267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894099541235201323707511 11841149311852801985561267)
              ·
                refine ⟨17761723967779202978341901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11841149311852801985561267 17761723967779202978341901)
                ·
                  refine ⟨6660646487917201116878213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17761723967779202978341901 6660646487917201116878213)
                  ·
                    refine ⟨1248871216484475209414665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660646487917201116878213 1248871216484475209414665)
                    ·
                      rfl

theorem cell23_7296504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_7296504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296504 prefixEnd_7296504 := by exact prefixLift 7296504
  have htrace : WordTrace (prefixWord ++ tailWord_7296504) baseStart_7296504 baseEnd_7296504 := by
    simpa [prefixWord, tailWord_7296504, baseEnd_7296504] using wordTrace_append hprefix tailTrace_7296504
  have hstable : (prefixWord ++ tailWord_7296504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296504).length < 2 ^ (prefixWord ++ tailWord_7296504).sum := by decide
  have hdescent : baseEnd_7296504 < baseStart_7296504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296520 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7296520 : Nat := 118140960795 + 7296520 * 2 ^ 59
def prefixEnd_7296520 : Nat := 4983230072969 + 3 ^ 40 * 7296520 * 2
def baseEnd_7296520 : Nat := 3746621865143897565643921

theorem tailTrace_7296520 : CollatzResearch.WordTrace tailWord_7296520 prefixEnd_7296520 3746621865143897565643921 := by
  unfold tailWord_7296520
  simp only [CollatzResearch.WordTrace]
  refine ⟨133062973762980830625163507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177417298350641107500218009 133062973762980830625163507)
  ·
    refine ⟨199594460644471245937745261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133062973762980830625163507 199594460644471245937745261)
    ·
      refine ⟨74847922741676717226654473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199594460644471245937745261 74847922741676717226654473)
      ·
        refine ⟨56135942056257537919990855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74847922741676717226654473 56135942056257537919990855)
        ·
          refine ⟨84203913084386306879986283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56135942056257537919990855 84203913084386306879986283)
          ·
            refine ⟨126305869626579460319979425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84203913084386306879986283 126305869626579460319979425)
            ·
              refine ⟨94729402219934595239984569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126305869626579460319979425 94729402219934595239984569)
              ·
                refine ⟨71047051664950946429988427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94729402219934595239984569 71047051664950946429988427)
                ·
                  refine ⟨106570577497426419644982641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71047051664950946429988427 106570577497426419644982641)
                  ·
                    refine ⟨79927933123069814733736981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106570577497426419644982641 79927933123069814733736981)
                    ·
                      refine ⟨3746621865143897565643921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79927933123069814733736981 3746621865143897565643921)
                      ·
                        rfl

theorem cell23_7296520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7296520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296520 prefixEnd_7296520 := by exact prefixLift 7296520
  have htrace : WordTrace (prefixWord ++ tailWord_7296520) baseStart_7296520 baseEnd_7296520 := by
    simpa [prefixWord, tailWord_7296520, baseEnd_7296520] using wordTrace_append hprefix tailTrace_7296520
  have hstable : (prefixWord ++ tailWord_7296520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296520).length < 2 ^ (prefixWord ++ tailWord_7296520).sum := by decide
  have hdescent : baseEnd_7296520 < baseStart_7296520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296560 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_7296560 : Nat := 118140960795 + 7296560 * 2 ^ 59
def prefixEnd_7296560 : Nat := 4983230072969 + 3 ^ 40 * 7296560 * 2
def baseEnd_7296560 : Nat := 1248880801456692469714579

theorem tailTrace_7296560 : CollatzResearch.WordTrace tailWord_7296560 prefixEnd_7296560 1248880801456692469714579 := by
  unfold tailWord_7296560
  simp only [CollatzResearch.WordTrace]
  refine ⟨133063703222908374040891567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177418270963877832054522089 133063703222908374040891567)
  ·
    refine ⟨199595554834362561061337351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133063703222908374040891567 199595554834362561061337351)
    ·
      refine ⟨299393332251543841592006027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199595554834362561061337351 299393332251543841592006027)
      ·
        refine ⟨449089998377315762388009041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299393332251543841592006027 449089998377315762388009041)
        ·
          refine ⟨336817498782986821791006781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449089998377315762388009041 336817498782986821791006781)
          ·
            refine ⟨126306562043620058171627543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336817498782986821791006781 126306562043620058171627543)
            ·
              refine ⟨189459843065430087257441315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126306562043620058171627543 189459843065430087257441315)
              ·
                refine ⟨284189764598145130886161973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189459843065430087257441315 284189764598145130886161973)
                ·
                  refine ⟨26642790431076106020577685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284189764598145130886161973 26642790431076106020577685)
                  ·
                    refine ⟨1248880801456692469714579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26642790431076106020577685 1248880801456692469714579)
                    ·
                      rfl

theorem cell23_7296560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_7296560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296560 prefixEnd_7296560 := by exact prefixLift 7296560
  have htrace : WordTrace (prefixWord ++ tailWord_7296560) baseStart_7296560 baseEnd_7296560 := by
    simpa [prefixWord, tailWord_7296560, baseEnd_7296560] using wordTrace_append hprefix tailTrace_7296560
  have hstable : (prefixWord ++ tailWord_7296560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296560).length < 2 ^ (prefixWord ++ tailWord_7296560).sum := by decide
  have hdescent : baseEnd_7296560 < baseStart_7296560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296567 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_7296567 : Nat := 118140960795 + 7296567 * 2 ^ 59
def prefixEnd_7296567 : Nat := 4983230072969 + 3 ^ 40 * 7296567 * 2
def baseEnd_7296567 : Nat := 3746645998734658881756205

theorem tailTrace_7296567 : CollatzResearch.WordTrace tailWord_7296567 prefixEnd_7296567 3746645998734658881756205 := by
  unfold tailWord_7296567
  simp only [CollatzResearch.WordTrace]
  refine ⟨266127661756791388277287955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177418441171194258851525303 266127661756791388277287955)
  ·
    refine ⟨399191492635187082415931933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266127661756791388277287955 399191492635187082415931933)
    ·
      refine ⟨149696809738195155905974475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399191492635187082415931933 149696809738195155905974475)
      ·
        refine ⟨224545214607292733858961713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149696809738195155905974475 224545214607292733858961713)
        ·
          refine ⟨168408910955469550394221285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224545214607292733858961713 168408910955469550394221285)
          ·
            refine ⟨31576670804150540698916491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168408910955469550394221285 31576670804150540698916491)
            ·
              refine ⟨47365006206225811048374737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31576670804150540698916491 47365006206225811048374737)
              ·
                refine ⟨35523754654669358286281053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47365006206225811048374737 35523754654669358286281053)
                ·
                  refine ⟨13321407995501009357355395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35523754654669358286281053 13321407995501009357355395)
                  ·
                    refine ⟨19982111993251514036033093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13321407995501009357355395 19982111993251514036033093)
                    ·
                      refine ⟨3746645998734658881756205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19982111993251514036033093 3746645998734658881756205)
                      ·
                        rfl

theorem cell23_7296567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_7296567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296567 prefixEnd_7296567 := by exact prefixLift 7296567
  have htrace : WordTrace (prefixWord ++ tailWord_7296567) baseStart_7296567 baseEnd_7296567 := by
    simpa [prefixWord, tailWord_7296567, baseEnd_7296567] using wordTrace_append hprefix tailTrace_7296567
  have hstable : (prefixWord ++ tailWord_7296567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296567).length < 2 ^ (prefixWord ++ tailWord_7296567).sum := by decide
  have hdescent : baseEnd_7296567 < baseStart_7296567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296611 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 2, 4]
def baseStart_7296611 : Nat := 118140960795 + 7296611 * 2 ^ 59
def prefixEnd_7296611 : Nat := 4983230072969 + 3 ^ 40 * 7296611 * 2
def baseEnd_7296611 : Nat := 1248889530627818903202001

theorem tailTrace_7296611 : CollatzResearch.WordTrace tailWord_7296611 prefixEnd_7296611 1248889530627818903202001 := by
  unfold tailWord_7296611
  simp only [CollatzResearch.WordTrace]
  refine ⟨266129266568631983791889687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177419511045754655861259791 266129266568631983791889687)
  ·
    refine ⟨399193899852947975687834531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266129266568631983791889687 399193899852947975687834531)
    ·
      refine ⟨598790849779421963531751797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399193899852947975687834531 598790849779421963531751797)
      ·
        refine ⟨56136642166820809081101731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 598790849779421963531751797 56136642166820809081101731)
        ·
          refine ⟨84204963250231213621652597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56136642166820809081101731 84204963250231213621652597)
          ·
            refine ⟨7894215304709176277029931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84204963250231213621652597 7894215304709176277029931)
            ·
              refine ⟨11841322957063764415544897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894215304709176277029931 11841322957063764415544897)
              ·
                refine ⟨8880992217797823311658673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11841322957063764415544897 8880992217797823311658673)
                ·
                  refine ⟨6660744163348367483744005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880992217797823311658673 6660744163348367483744005)
                  ·
                    refine ⟨1248889530627818903202001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660744163348367483744005 1248889530627818903202001)
                    ·
                      rfl

theorem cell23_7296611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 4].length) (baseStart_7296611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296611 prefixEnd_7296611 := by exact prefixLift 7296611
  have htrace : WordTrace (prefixWord ++ tailWord_7296611) baseStart_7296611 baseEnd_7296611 := by
    simpa [prefixWord, tailWord_7296611, baseEnd_7296611] using wordTrace_append hprefix tailTrace_7296611
  have hstable : (prefixWord ++ tailWord_7296611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296611).length < 2 ^ (prefixWord ++ tailWord_7296611).sum := by decide
  have hdescent : baseEnd_7296611 < baseStart_7296611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296617 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_7296617 : Nat := 118140960795 + 7296617 * 2 ^ 59
def prefixEnd_7296617 : Nat := 4983230072969 + 3 ^ 40 * 7296617 * 2
def baseEnd_7296617 : Nat := 3746671672767383686130975

theorem tailTrace_7296617 : CollatzResearch.WordTrace tailWord_7296617 prefixEnd_7296617 3746671672767383686130975 := by
  unfold tailWord_7296617
  simp only [CollatzResearch.WordTrace]
  refine ⟨266129485406610246816608105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177419656937740164544405403 266129485406610246816608105)
  ·
    refine ⟨199597114054957685112456079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266129485406610246816608105 199597114054957685112456079)
    ·
      refine ⟨299395671082436527668684119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199597114054957685112456079 299395671082436527668684119)
      ·
        refine ⟨449093506623654791503026179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299395671082436527668684119 449093506623654791503026179)
        ·
          refine ⟨673640259935482187254539269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449093506623654791503026179 673640259935482187254539269)
          ·
            refine ⟨126307548737902910110226113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 673640259935482187254539269 126307548737902910110226113)
            ·
              refine ⟨94730661553427182582669585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126307548737902910110226113 94730661553427182582669585)
              ·
                refine ⟨71047996165070386937002189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94730661553427182582669585 71047996165070386937002189)
                ·
                  refine ⟨26642998561901395101375821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71047996165070386937002189 26642998561901395101375821)
                  ·
                    refine ⟨9991124460713023163015933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26642998561901395101375821 9991124460713023163015933)
                    ·
                      refine ⟨3746671672767383686130975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991124460713023163015933 3746671672767383686130975)
                      ·
                        rfl

theorem cell23_7296617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_7296617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296617 prefixEnd_7296617 := by exact prefixLift 7296617
  have htrace : WordTrace (prefixWord ++ tailWord_7296617) baseStart_7296617 baseEnd_7296617 := by
    simpa [prefixWord, tailWord_7296617, baseEnd_7296617] using wordTrace_append hprefix tailTrace_7296617
  have hstable : (prefixWord ++ tailWord_7296617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296617).length < 2 ^ (prefixWord ++ tailWord_7296617).sum := by decide
  have hdescent : baseEnd_7296617 < baseStart_7296617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296618 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_7296618 : Nat := 118140960795 + 7296618 * 2 ^ 59
def prefixEnd_7296618 : Nat := 4983230072969 + 3 ^ 40 * 7296618 * 2
def baseEnd_7296618 : Nat := 3746672186248038182218471

theorem tailTrace_7296618 : CollatzResearch.WordTrace tailWord_7296618 prefixEnd_7296618 3746672186248038182218471 := by
  unfold tailWord_7296618
  simp only [CollatzResearch.WordTrace]
  refine ⟨66532380469901655996848627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177419681253071082658263005 66532380469901655996848627)
  ·
    refine ⟨99798570704852483995272941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66532380469901655996848627 99798570704852483995272941)
    ·
      refine ⟨37424464014319681498227353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99798570704852483995272941 37424464014319681498227353)
      ·
        refine ⟨28068348010739761123670515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37424464014319681498227353 28068348010739761123670515)
        ·
          refine ⟨42102522016109641685505773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28068348010739761123670515 42102522016109641685505773)
          ·
            refine ⟨15788445756041115632064665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42102522016109641685505773 15788445756041115632064665)
            ·
              refine ⟨11841334317030836724048499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15788445756041115632064665 11841334317030836724048499)
              ·
                refine ⟨17762001475546255086072749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11841334317030836724048499 17762001475546255086072749)
                ·
                  refine ⟨6660750553329845657277281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17762001475546255086072749 6660750553329845657277281)
                  ·
                    refine ⟨4995562914997384242957961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6660750553329845657277281 4995562914997384242957961)
                    ·
                      refine ⟨3746672186248038182218471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995562914997384242957961 3746672186248038182218471)
                      ·
                        rfl

theorem cell23_7296618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_7296618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296618 prefixEnd_7296618 := by exact prefixLift 7296618
  have htrace : WordTrace (prefixWord ++ tailWord_7296618) baseStart_7296618 baseEnd_7296618 := by
    simpa [prefixWord, tailWord_7296618, baseEnd_7296618] using wordTrace_append hprefix tailTrace_7296618
  have hstable : (prefixWord ++ tailWord_7296618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296618).length < 2 ^ (prefixWord ++ tailWord_7296618).sum := by decide
  have hdescent : baseEnd_7296618 < baseStart_7296618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296647 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_7296647 : Nat := 118140960795 + 7296647 * 2 ^ 59
def prefixEnd_7296647 : Nat := 4983230072969 + 3 ^ 40 * 7296647 * 2
def baseEnd_7296647 : Nat := 3746687077187018568755837

theorem tailTrace_7296647 : CollatzResearch.WordTrace tailWord_7296647 prefixEnd_7296647 3746687077187018568755837 := by
  unfold tailWord_7296647
  simp only [CollatzResearch.WordTrace]
  refine ⟨266130579596501561940200195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177420386397667707960133463 266130579596501561940200195)
  ·
    refine ⟨399195869394752342910300293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266130579596501561940200195 399195869394752342910300293)
    ·
      refine ⟨74849225511516064295681305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399195869394752342910300293 74849225511516064295681305)
      ·
        refine ⟨56136919133637048221760979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74849225511516064295681305 56136919133637048221760979)
        ·
          refine ⟨84205378700455572332641469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56136919133637048221760979 84205378700455572332641469)
          ·
            refine ⟨31577017012670839624740551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84205378700455572332641469 31577017012670839624740551)
            ·
              refine ⟨47365525519006259437110827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31577017012670839624740551 47365525519006259437110827)
              ·
                refine ⟨71048288278509389155666241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47365525519006259437110827 71048288278509389155666241)
                ·
                  refine ⟨53286216208882041866749681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71048288278509389155666241 53286216208882041866749681)
                  ·
                    refine ⟨39964662156661531400062261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53286216208882041866749681 39964662156661531400062261)
                    ·
                      refine ⟨3746687077187018568755837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39964662156661531400062261 3746687077187018568755837)
                      ·
                        rfl

theorem cell23_7296647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_7296647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296647 prefixEnd_7296647 := by exact prefixLift 7296647
  have htrace : WordTrace (prefixWord ++ tailWord_7296647) baseStart_7296647 baseEnd_7296647 := by
    simpa [prefixWord, tailWord_7296647, baseEnd_7296647] using wordTrace_append hprefix tailTrace_7296647
  have hstable : (prefixWord ++ tailWord_7296647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296647).length < 2 ^ (prefixWord ++ tailWord_7296647).sum := by decide
  have hdescent : baseEnd_7296647 < baseStart_7296647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296687 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_7296687 : Nat := 118140960795 + 7296687 * 2 ^ 59
def prefixEnd_7296687 : Nat := 4983230072969 + 3 ^ 40 * 7296687 * 2
def baseEnd_7296687 : Nat := 3746707616413198412255653

theorem tailTrace_7296687 : CollatzResearch.WordTrace tailWord_7296687 prefixEnd_7296687 3746707616413198412255653 := by
  unfold tailWord_7296687
  simp only [CollatzResearch.WordTrace]
  refine ⟨266132038516356648771656315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177421359010904432514437543 266132038516356648771656315)
  ·
    refine ⟨399198057774534973157484473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266132038516356648771656315 399198057774534973157484473)
    ·
      refine ⟨299398543330901229868113355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399198057774534973157484473 299398543330901229868113355)
      ·
        refine ⟨449097814996351844802170033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299398543330901229868113355 449097814996351844802170033)
        ·
          refine ⟨336823361247263883601627525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449097814996351844802170033 336823361247263883601627525)
          ·
            refine ⟨63154380233861978175305161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336823361247263883601627525 63154380233861978175305161)
            ·
              refine ⟨47365785175396483631478871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63154380233861978175305161 47365785175396483631478871)
              ·
                refine ⟨71048677763094725447218307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47365785175396483631478871 71048677763094725447218307)
                ·
                  refine ⟨106573016644642088170827461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71048677763094725447218307 106573016644642088170827461)
                  ·
                    refine ⟨19982440620870391532030149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106573016644642088170827461 19982440620870391532030149)
                    ·
                      refine ⟨3746707616413198412255653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19982440620870391532030149 3746707616413198412255653)
                      ·
                        rfl

theorem cell23_7296687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_7296687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296687 prefixEnd_7296687 := by exact prefixLift 7296687
  have htrace : WordTrace (prefixWord ++ tailWord_7296687) baseStart_7296687 baseEnd_7296687 := by
    simpa [prefixWord, tailWord_7296687, baseEnd_7296687] using wordTrace_append hprefix tailTrace_7296687
  have hstable : (prefixWord ++ tailWord_7296687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296687).length < 2 ^ (prefixWord ++ tailWord_7296687).sum := by decide
  have hdescent : baseEnd_7296687 < baseStart_7296687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296697 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 7]
def baseStart_7296697 : Nat := 118140960795 + 7296697 * 2 ^ 59
def prefixEnd_7296697 : Nat := 4983230072969 + 3 ^ 40 * 7296697 * 2
def baseEnd_7296697 : Nat := 416301416802193708125623

theorem tailTrace_7296697 : CollatzResearch.WordTrace tailWord_7296697 prefixEnd_7296697 416301416802193708125623 := by
  unfold tailWord_7296697
  simp only [CollatzResearch.WordTrace]
  refine ⟨266132403246320420479520345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177421602164213613653013563 266132403246320420479520345)
  ·
    refine ⟨199599302434740315359640259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266132403246320420479520345 199599302434740315359640259)
    ·
      refine ⟨299398953652110473039460389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199599302434740315359640259 299398953652110473039460389)
      ·
        refine ⟨56137303809770713694898823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299398953652110473039460389 56137303809770713694898823)
        ·
          refine ⟨84205955714656070542348235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56137303809770713694898823 84205955714656070542348235)
          ·
            refine ⟨126308933571984105813522353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84205955714656070542348235 126308933571984105813522353)
            ·
              refine ⟨94731700178988079360141765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126308933571984105813522353 94731700178988079360141765)
              ·
                refine ⟨17762193783560264880026581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94731700178988079360141765 17762193783560264880026581)
                ·
                  refine ⟨416301416802193708125623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17762193783560264880026581 416301416802193708125623)
                  ·
                    rfl

theorem cell23_7296697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_7296697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296697 prefixEnd_7296697 := by exact prefixLift 7296697
  have htrace : WordTrace (prefixWord ++ tailWord_7296697) baseStart_7296697 baseEnd_7296697 := by
    simpa [prefixWord, tailWord_7296697, baseEnd_7296697] using wordTrace_append hprefix tailTrace_7296697
  have hstable : (prefixWord ++ tailWord_7296697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296697).length < 2 ^ (prefixWord ++ tailWord_7296697).sum := by decide
  have hdescent : baseEnd_7296697 < baseStart_7296697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296764 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_7296764 : Nat := 118140960795 + 7296764 * 2 ^ 59
def prefixEnd_7296764 : Nat := 4983230072969 + 3 ^ 40 * 7296764 * 2
def baseEnd_7296764 : Nat := 3746747154423594610992799

theorem tailTrace_7296764 : CollatzResearch.WordTrace tailWord_7296764 prefixEnd_7296764 3746747154423594610992799 := by
  unfold tailWord_7296764
  simp only [CollatzResearch.WordTrace]
  refine ⟨133067423468538845461104673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177423231291385127281472897 133067423468538845461104673)
  ·
    refine ⟨99800567601404134095828505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133067423468538845461104673 99800567601404134095828505)
    ·
      refine ⟨74850425701053100571871379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99800567601404134095828505 74850425701053100571871379)
      ·
        refine ⟨112275638551579650857807069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74850425701053100571871379 112275638551579650857807069)
        ·
          refine ⟨42103364456842369071677651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112275638551579650857807069 42103364456842369071677651)
          ·
            refine ⟨63155046685263553607516477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42103364456842369071677651 63155046685263553607516477)
            ·
              refine ⟨23683142506973832602818679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63155046685263553607516477 23683142506973832602818679)
              ·
                refine ⟨35524713760460748904228019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23683142506973832602818679 35524713760460748904228019)
                ·
                  refine ⟨53287070640691123356342029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35524713760460748904228019 53287070640691123356342029)
                  ·
                    refine ⟨19982651490259171258628261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53287070640691123356342029 19982651490259171258628261)
                    ·
                      refine ⟨3746747154423594610992799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19982651490259171258628261 3746747154423594610992799)
                      ·
                        rfl

theorem cell23_7296764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_7296764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296764 prefixEnd_7296764 := by exact prefixLift 7296764
  have htrace : WordTrace (prefixWord ++ tailWord_7296764) baseStart_7296764 baseEnd_7296764 := by
    simpa [prefixWord, tailWord_7296764, baseEnd_7296764] using wordTrace_append hprefix tailTrace_7296764
  have hstable : (prefixWord ++ tailWord_7296764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296764).length < 2 ^ (prefixWord ++ tailWord_7296764).sum := by decide
  have hdescent : baseEnd_7296764 < baseStart_7296764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296791 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 3, 4]
def baseStart_7296791 : Nat := 118140960795 + 7296791 * 2 ^ 59
def prefixEnd_7296791 : Nat := 4983230072969 + 3 ^ 40 * 7296791 * 2
def baseEnd_7296791 : Nat := 1248920339467088668451725

theorem tailTrace_7296791 : CollatzResearch.WordTrace tailWord_7296791 prefixEnd_7296791 1248920339467088668451725 := by
  unfold tailWord_7296791
  simp only [CollatzResearch.WordTrace]
  refine ⟨266135831707979874533442227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177423887805319916355628151 266135831707979874533442227)
  ·
    refine ⟨399203747561969811800163341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266135831707979874533442227 399203747561969811800163341)
    ·
      refine ⟨149701405335738679425061253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399203747561969811800163341 149701405335738679425061253)
      ·
        refine ⟨28069013500451002392198985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149701405335738679425061253 28069013500451002392198985)
        ·
          refine ⟨21051760125338251794149239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28069013500451002392198985 21051760125338251794149239)
          ·
            refine ⟨31577640188007377691223859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21051760125338251794149239 31577640188007377691223859)
            ·
              refine ⟨47366460282011066536835789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31577640188007377691223859 47366460282011066536835789)
              ·
                refine ⟨17762422605754149951313421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47366460282011066536835789 17762422605754149951313421)
                ·
                  refine ⟨6660908477157806231742533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17762422605754149951313421 6660908477157806231742533)
                  ·
                    refine ⟨1248920339467088668451725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660908477157806231742533 1248920339467088668451725)
                    ·
                      rfl

theorem cell23_7296791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_7296791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296791 prefixEnd_7296791 := by exact prefixLift 7296791
  have htrace : WordTrace (prefixWord ++ tailWord_7296791) baseStart_7296791 baseEnd_7296791 := by
    simpa [prefixWord, tailWord_7296791, baseEnd_7296791] using wordTrace_append hprefix tailTrace_7296791
  have hstable : (prefixWord ++ tailWord_7296791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296791).length < 2 ^ (prefixWord ++ tailWord_7296791).sum := by decide
  have hdescent : baseEnd_7296791 < baseStart_7296791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296838 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_7296838 : Nat := 118140960795 + 7296838 * 2 ^ 59
def prefixEnd_7296838 : Nat := 4983230072969 + 3 ^ 40 * 7296838 * 2
def baseEnd_7296838 : Nat := 416309461332447480163051

theorem tailTrace_7296838 : CollatzResearch.WordTrace tailWord_7296838 prefixEnd_7296838 416309461332447480163051 := by
  unfold tailWord_7296838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316798310587800048762599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177425030625873067706935445 8316798310587800048762599)
  ·
    refine ⟨12475197465881700073143899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316798310587800048762599 12475197465881700073143899)
    ·
      refine ⟨18712796198822550109715849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12475197465881700073143899 18712796198822550109715849)
      ·
        refine ⟨14034597149116912582286887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18712796198822550109715849 14034597149116912582286887)
        ·
          refine ⟨21051895723675368873430331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14034597149116912582286887 21051895723675368873430331)
          ·
            refine ⟨31577843585513053310145497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21051895723675368873430331 31577843585513053310145497)
            ·
              refine ⟨23683382689134789982609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31577843585513053310145497 23683382689134789982609123)
              ·
                refine ⟨35525074033702184973913685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23683382689134789982609123 35525074033702184973913685)
                ·
                  refine ⟨416309461332447480163051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35525074033702184973913685 416309461332447480163051)
                  ·
                    rfl

theorem cell23_7296838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_7296838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296838 prefixEnd_7296838 := by exact prefixLift 7296838
  have htrace : WordTrace (prefixWord ++ tailWord_7296838) baseStart_7296838 baseEnd_7296838 := by
    simpa [prefixWord, tailWord_7296838, baseEnd_7296838] using wordTrace_append hprefix tailTrace_7296838
  have hstable : (prefixWord ++ tailWord_7296838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296838).length < 2 ^ (prefixWord ++ tailWord_7296838).sum := by decide
  have hdescent : baseEnd_7296838 < baseStart_7296838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296855 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 6]
def baseStart_7296855 : Nat := 118140960795 + 7296855 * 2 ^ 59
def prefixEnd_7296855 : Nat := 4983230072969 + 3 ^ 40 * 7296855 * 2
def baseEnd_7296855 : Nat := 416310431240350417217209

theorem tailTrace_7296855 : CollatzResearch.WordTrace tailWord_7296855 prefixEnd_7296855 416310431240350417217209 := by
  unfold tailWord_7296855
  simp only [CollatzResearch.WordTrace]
  refine ⟨266138165979748013463772019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177425443986498675642514679 266138165979748013463772019)
  ·
    refine ⟨399207248969622020195658029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266138165979748013463772019 399207248969622020195658029)
    ·
      refine ⟨149702718363608257573371761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399207248969622020195658029 149702718363608257573371761)
      ·
        refine ⟨112277038772706193180028821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149702718363608257573371761 112277038772706193180028821)
        ·
          refine ⟨5262986192470602805313851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112277038772706193180028821 5262986192470602805313851)
          ·
            refine ⟨7894479288705904207970777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262986192470602805313851 7894479288705904207970777)
            ·
              refine ⟨5920859466529428155978083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7894479288705904207970777 5920859466529428155978083)
              ·
                refine ⟨8881289199794142233967125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920859466529428155978083 8881289199794142233967125)
                ·
                  refine ⟨416310431240350417217209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8881289199794142233967125 416310431240350417217209)
                  ·
                    rfl

theorem cell23_7296855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 6].length) (baseStart_7296855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296855 prefixEnd_7296855 := by exact prefixLift 7296855
  have htrace : WordTrace (prefixWord ++ tailWord_7296855) baseStart_7296855 baseEnd_7296855 := by
    simpa [prefixWord, tailWord_7296855, baseEnd_7296855] using wordTrace_append hprefix tailTrace_7296855
  have hstable : (prefixWord ++ tailWord_7296855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296855).length < 2 ^ (prefixWord ++ tailWord_7296855).sum := by decide
  have hdescent : baseEnd_7296855 < baseStart_7296855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296871 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_7296871 : Nat := 118140960795 + 7296871 * 2 ^ 59
def prefixEnd_7296871 : Nat := 4983230072969 + 3 ^ 40 * 7296871 * 2
def baseEnd_7296871 : Nat := 3746802096853625692354807

theorem tailTrace_7296871 : CollatzResearch.WordTrace tailWord_7296871 prefixEnd_7296871 3746802096853625692354807 := by
  unfold tailWord_7296871
  simp only [CollatzResearch.WordTrace]
  refine ⟨266138749547690048196354467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177425833031793365464236311 266138749547690048196354467)
  ·
    refine ⟨399208124321535072294531701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266138749547690048196354467 399208124321535072294531701)
    ·
      refine ⟨37425761655143913027612347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 399208124321535072294531701 37425761655143913027612347)
      ·
        refine ⟨56138642482715869541418521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37425761655143913027612347 56138642482715869541418521)
        ·
          refine ⟨42103981862036902156063891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56138642482715869541418521 42103981862036902156063891)
          ·
            refine ⟨63155972793055353234095837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42103981862036902156063891 63155972793055353234095837)
            ·
              refine ⟨23683489797395757462785939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63155972793055353234095837 23683489797395757462785939)
              ·
                refine ⟨35525234696093636194178909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23683489797395757462785939 35525234696093636194178909)
                ·
                  refine ⟨13321963011035113572817091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35525234696093636194178909 13321963011035113572817091)
                  ·
                    refine ⟨19982944516552670359225637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13321963011035113572817091 19982944516552670359225637)
                    ·
                      refine ⟨3746802096853625692354807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19982944516552670359225637 3746802096853625692354807)
                      ·
                        rfl

theorem cell23_7296871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_7296871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296871 prefixEnd_7296871 := by exact prefixLift 7296871
  have htrace : WordTrace (prefixWord ++ tailWord_7296871) baseStart_7296871 baseEnd_7296871 := by
    simpa [prefixWord, tailWord_7296871, baseEnd_7296871] using wordTrace_append hprefix tailTrace_7296871
  have hstable : (prefixWord ++ tailWord_7296871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296871).length < 2 ^ (prefixWord ++ tailWord_7296871).sum := by decide
  have hdescent : baseEnd_7296871 < baseStart_7296871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296921 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_7296921 : Nat := 118140960795 + 7296921 * 2 ^ 59
def prefixEnd_7296921 : Nat := 4983230072969 + 3 ^ 40 * 7296921 * 2
def baseEnd_7296921 : Nat := 3746827770886350496729577

theorem tailTrace_7296921 : CollatzResearch.WordTrace tailWord_7296921 prefixEnd_7296921 3746827770886350496729577 := by
  unfold tailWord_7296921
  simp only [CollatzResearch.WordTrace]
  refine ⟨266140573197508906735674617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177427048798339271157116411 266140573197508906735674617)
  ·
    refine ⟨199605429898131680051755963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266140573197508906735674617 199605429898131680051755963)
    ·
      refine ⟨299408144847197520077633945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199605429898131680051755963 299408144847197520077633945)
      ·
        refine ⟨224556108635398140058225459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299408144847197520077633945 224556108635398140058225459)
        ·
          refine ⟨336834162953097210087338189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224556108635398140058225459 336834162953097210087338189)
          ·
            refine ⟨126312811107411453782751821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336834162953097210087338189 126312811107411453782751821)
            ·
              refine ⟨47367304165279295168531933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126312811107411453782751821 47367304165279295168531933)
              ·
                refine ⟨17762739061979735688199475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47367304165279295168531933 17762739061979735688199475)
                ·
                  refine ⟨26644108592969603532299213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17762739061979735688199475 26644108592969603532299213)
                  ·
                    refine ⟨9991540722363601324612205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26644108592969603532299213 9991540722363601324612205)
                    ·
                      refine ⟨3746827770886350496729577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991540722363601324612205 3746827770886350496729577)
                      ·
                        rfl

theorem cell23_7296921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_7296921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296921 prefixEnd_7296921 := by exact prefixLift 7296921
  have htrace : WordTrace (prefixWord ++ tailWord_7296921) baseStart_7296921 baseEnd_7296921 := by
    simpa [prefixWord, tailWord_7296921, baseEnd_7296921] using wordTrace_append hprefix tailTrace_7296921
  have hstable : (prefixWord ++ tailWord_7296921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296921).length < 2 ^ (prefixWord ++ tailWord_7296921).sum := by decide
  have hdescent : baseEnd_7296921 < baseStart_7296921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296926 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7296926 : Nat := 118140960795 + 7296926 * 2 ^ 59
def prefixEnd_7296926 : Nat := 4983230072969 + 3 ^ 40 * 7296926 * 2
def baseEnd_7296926 : Nat := 3746830338289622977167055

theorem tailTrace_7296926 : CollatzResearch.WordTrace tailWord_7296926 prefixEnd_7296926 3746830338289622977167055 := by
  unfold tailWord_7296926
  simp only [CollatzResearch.WordTrace]
  refine ⟨33267594445311349073700829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177427170374993861726404421 33267594445311349073700829)
  ·
    refine ⟨12475347916991755902637811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33267594445311349073700829 12475347916991755902637811)
    ·
      refine ⟨18713021875487633853956717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12475347916991755902637811 18713021875487633853956717)
      ·
        refine ⟨7017383203307862695233769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18713021875487633853956717 7017383203307862695233769)
        ·
          refine ⟨5263037402480897021425327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7017383203307862695233769 5263037402480897021425327)
          ·
            refine ⟨7894556103721345532137991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263037402480897021425327 7894556103721345532137991)
            ·
              refine ⟨11841834155582018298206987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894556103721345532137991 11841834155582018298206987)
              ·
                refine ⟨17762751233373027447310481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11841834155582018298206987 17762751233373027447310481)
                ·
                  refine ⟨13322063425029770585482861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17762751233373027447310481 13322063425029770585482861)
                  ·
                    refine ⟨4995773784386163969556073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13322063425029770585482861 4995773784386163969556073)
                    ·
                      refine ⟨3746830338289622977167055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995773784386163969556073 3746830338289622977167055)
                      ·
                        rfl

theorem cell23_7296926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7296926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296926 prefixEnd_7296926 := by exact prefixLift 7296926
  have htrace : WordTrace (prefixWord ++ tailWord_7296926) baseStart_7296926 baseEnd_7296926 := by
    simpa [prefixWord, tailWord_7296926, baseEnd_7296926] using wordTrace_append hprefix tailTrace_7296926
  have hstable : (prefixWord ++ tailWord_7296926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296926).length < 2 ^ (prefixWord ++ tailWord_7296926).sum := by decide
  have hdescent : baseEnd_7296926 < baseStart_7296926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296972 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7296972 : Nat := 118140960795 + 7296972 * 2 ^ 59
def prefixEnd_7296972 : Nat := 4983230072969 + 3 ^ 40 * 7296972 * 2
def baseEnd_7296972 : Nat := 3746853958399729797191843

theorem tailTrace_7296972 : CollatzResearch.WordTrace tailWord_7296972 prefixEnd_7296972 3746853958399729797191843 := by
  unfold tailWord_7296972
  simp only [CollatzResearch.WordTrace]
  refine ⟨133071216660162071222890585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177428288880216094963854113 133071216660162071222890585)
  ·
    refine ⟨99803412495121553417167939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133071216660162071222890585 99803412495121553417167939)
    ·
      refine ⟨149705118742682330125751909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99803412495121553417167939 149705118742682330125751909)
      ·
        refine ⟨28069709764252936898578483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149705118742682330125751909 28069709764252936898578483)
        ·
          refine ⟨42104564646379405347867725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28069709764252936898578483 42104564646379405347867725)
          ·
            refine ⟨15789211742392277005450397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42104564646379405347867725 15789211742392277005450397)
            ·
              refine ⟨5920954403397103877043899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15789211742392277005450397 5920954403397103877043899)
              ·
                refine ⟨8881431605095655815565849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920954403397103877043899 8881431605095655815565849)
                ·
                  refine ⟨6661073703821741861674387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8881431605095655815565849 6661073703821741861674387)
                  ·
                    refine ⟨9991610555732612792511581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661073703821741861674387 9991610555732612792511581)
                    ·
                      refine ⟨3746853958399729797191843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991610555732612792511581 3746853958399729797191843)
                      ·
                        rfl

theorem cell23_7296972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7296972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296972 prefixEnd_7296972 := by exact prefixLift 7296972
  have htrace : WordTrace (prefixWord ++ tailWord_7296972) baseStart_7296972 baseEnd_7296972 := by
    simpa [prefixWord, tailWord_7296972, baseEnd_7296972] using wordTrace_append hprefix tailTrace_7296972
  have hstable : (prefixWord ++ tailWord_7296972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296972).length < 2 ^ (prefixWord ++ tailWord_7296972).sum := by decide
  have hdescent : baseEnd_7296972 < baseStart_7296972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7296995 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 4, 2, 2]
def baseStart_7296995 : Nat := 118140960795 + 7296995 * 2 ^ 59
def prefixEnd_7296995 : Nat := 4983230072969 + 3 ^ 40 * 7296995 * 2
def baseEnd_7296995 : Nat := 3746865768454783207204237

theorem tailTrace_7296995 : CollatzResearch.WordTrace tailWord_7296995 prefixEnd_7296995 3746865768454783207204237 := by
  unfold tailWord_7296995
  simp only [CollatzResearch.WordTrace]
  refine ⟨266143272199240817373868439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177428848132827211582578959 266143272199240817373868439)
  ·
    refine ⟨399214908298861226060802659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266143272199240817373868439 399214908298861226060802659)
    ·
      refine ⟨598822362448291839091203989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399214908298861226060802659 598822362448291839091203989)
      ·
        refine ⟨28069798239763679957400187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 598822362448291839091203989 28069798239763679957400187)
        ·
          refine ⟨42104697359645519936100281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28069798239763679957400187 42104697359645519936100281)
          ·
            refine ⟨31578523019734139952075211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42104697359645519936100281 31578523019734139952075211)
            ·
              refine ⟨47367784529601209928112817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31578523019734139952075211 47367784529601209928112817)
              ·
                refine ⟨35525838397200907446084613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47367784529601209928112817 35525838397200907446084613)
                ·
                  refine ⟨6661094699475170146140865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35525838397200907446084613 6661094699475170146140865)
                  ·
                    refine ⟨4995821024606377609605649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6661094699475170146140865 4995821024606377609605649)
                    ·
                      refine ⟨3746865768454783207204237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995821024606377609605649 3746865768454783207204237)
                      ·
                        rfl

theorem cell23_7296995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_7296995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7296995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7296995 prefixEnd_7296995 := by exact prefixLift 7296995
  have htrace : WordTrace (prefixWord ++ tailWord_7296995) baseStart_7296995 baseEnd_7296995 := by
    simpa [prefixWord, tailWord_7296995, baseEnd_7296995] using wordTrace_append hprefix tailTrace_7296995
  have hstable : (prefixWord ++ tailWord_7296995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7296995).length < 2 ^ (prefixWord ++ tailWord_7296995).sum := by decide
  have hdescent : baseEnd_7296995 < baseStart_7296995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7296995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297011 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 3]
def baseStart_7297011 : Nat := 118140960795 + 7297011 * 2 ^ 59
def prefixEnd_7297011 : Nat := 4983230072969 + 3 ^ 40 * 7297011 * 2
def baseEnd_7297011 : Nat := 3746873984145255144604163

theorem tailTrace_7297011 : CollatzResearch.WordTrace tailWord_7297011 prefixEnd_7297011 3746873984145255144604163 := by
  unfold tailWord_7297011
  simp only [CollatzResearch.WordTrace]
  refine ⟨266143855767182852106450887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177429237178121901404300591 266143855767182852106450887)
  ·
    refine ⟨399215783650774278159676331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266143855767182852106450887 399215783650774278159676331)
    ·
      refine ⟨598823675476161417239514497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399215783650774278159676331 598823675476161417239514497)
      ·
        refine ⟨449117756607121062929635873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598823675476161417239514497 449117756607121062929635873)
        ·
          refine ⟨336838317455340797197226905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449117756607121062929635873 336838317455340797197226905)
          ·
            refine ⟨252628738091505597897920179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336838317455340797197226905 252628738091505597897920179)
            ·
              refine ⟨378943107137258396846880269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252628738091505597897920179 378943107137258396846880269)
              ·
                refine ⟨142103665176471898817580101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378943107137258396846880269 142103665176471898817580101)
                ·
                  refine ⟨26644437220588481028296269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142103665176471898817580101 26644437220588481028296269)
                  ·
                    refine ⟨9991663957720680385611101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26644437220588481028296269 9991663957720680385611101)
                    ·
                      refine ⟨3746873984145255144604163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991663957720680385611101 3746873984145255144604163)
                      ·
                        rfl

theorem cell23_7297011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_7297011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297011 prefixEnd_7297011 := by exact prefixLift 7297011
  have htrace : WordTrace (prefixWord ++ tailWord_7297011) baseStart_7297011 baseEnd_7297011 := by
    simpa [prefixWord, tailWord_7297011, baseEnd_7297011] using wordTrace_append hprefix tailTrace_7297011
  have hstable : (prefixWord ++ tailWord_7297011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297011).length < 2 ^ (prefixWord ++ tailWord_7297011).sum := by decide
  have hdescent : baseEnd_7297011 < baseStart_7297011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297029 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 2, 2, 2]
def baseStart_7297029 : Nat := 118140960795 + 7297029 * 2 ^ 59
def prefixEnd_7297029 : Nat := 4983230072969 + 3 ^ 40 * 7297029 * 2
def baseEnd_7297029 : Nat := 3746883226797036074179081

theorem tailTrace_7297029 : CollatzResearch.WordTrace tailWord_7297029 prefixEnd_7297029 3746883226797036074179081 := by
  unfold tailWord_7297029
  simp only [CollatzResearch.WordTrace]
  refine ⟨266144512281117641180606141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177429674854078427453737427 266144512281117641180606141)
  ·
    refine ⟨99804192105419115442727303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266144512281117641180606141 99804192105419115442727303)
    ·
      refine ⟨149706288158128673164090955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99804192105419115442727303 149706288158128673164090955)
      ·
        refine ⟨224559432237193009746136433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149706288158128673164090955 224559432237193009746136433)
        ·
          refine ⟨168419574177894757309602325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224559432237193009746136433 168419574177894757309602325)
          ·
            refine ⟨7894667539588816748887609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168419574177894757309602325 7894667539588816748887609)
            ·
              refine ⟨5921000654691612561665707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7894667539588816748887609 5921000654691612561665707)
              ·
                refine ⟨8881500982037418842498561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921000654691612561665707 8881500982037418842498561)
                ·
                  refine ⟨6661125736528064131873921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8881500982037418842498561 6661125736528064131873921)
                  ·
                    refine ⟨4995844302396048098905441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6661125736528064131873921 4995844302396048098905441)
                    ·
                      refine ⟨3746883226797036074179081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995844302396048098905441 3746883226797036074179081)
                      ·
                        rfl

theorem cell23_7297029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_7297029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297029 prefixEnd_7297029 := by exact prefixLift 7297029
  have htrace : WordTrace (prefixWord ++ tailWord_7297029) baseStart_7297029 baseEnd_7297029 := by
    simpa [prefixWord, tailWord_7297029, baseEnd_7297029] using wordTrace_append hprefix tailTrace_7297029
  have hstable : (prefixWord ++ tailWord_7297029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297029).length < 2 ^ (prefixWord ++ tailWord_7297029).sum := by decide
  have hdescent : baseEnd_7297029 < baseStart_7297029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297048 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 2, 5]
def baseStart_7297048 : Nat := 118140960795 + 7297048 * 2 ^ 59
def prefixEnd_7297048 : Nat := 4983230072969 + 3 ^ 40 * 7297048 * 2
def baseEnd_7297048 : Nat := 1248964327643157166613831

theorem tailTrace_7297048 : CollatzResearch.WordTrace tailWord_7297048 prefixEnd_7297048 1248964327643157166613831 := by
  unfold tailWord_7297048
  simp only [CollatzResearch.WordTrace]
  refine ⟨133072602634024403712773899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177430136845365871617031865 133072602634024403712773899)
  ·
    refine ⟨199608903951036605569160849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133072602634024403712773899 199608903951036605569160849)
    ·
      refine ⟨149706677963277454176870637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199608903951036605569160849 149706677963277454176870637)
      ·
        refine ⟨56140004236229045316326489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149706677963277454176870637 56140004236229045316326489)
        ·
          refine ⟨42105003177171783987244867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56140004236229045316326489 42105003177171783987244867)
          ·
            refine ⟨63157504765757675980867301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42105003177171783987244867 63157504765757675980867301)
            ·
              refine ⟨11842032143579564246412619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63157504765757675980867301 11842032143579564246412619)
              ·
                refine ⟨17763048215369346369618929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11842032143579564246412619 17763048215369346369618929)
                ·
                  refine ⟨13322286161527009777214197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17763048215369346369618929 13322286161527009777214197)
                  ·
                    refine ⟨1248964327643157166613831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13322286161527009777214197 1248964327643157166613831)
                    ·
                      rfl

theorem cell23_7297048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_7297048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297048 prefixEnd_7297048 := by exact prefixLift 7297048
  have htrace : WordTrace (prefixWord ++ tailWord_7297048) baseStart_7297048 baseEnd_7297048 := by
    simpa [prefixWord, tailWord_7297048, baseEnd_7297048] using wordTrace_append hprefix tailTrace_7297048
  have hstable : (prefixWord ++ tailWord_7297048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297048).length < 2 ^ (prefixWord ++ tailWord_7297048).sum := by decide
  have hdescent : baseEnd_7297048 < baseStart_7297048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297085 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_7297085 : Nat := 118140960795 + 7297085 * 2 ^ 59
def prefixEnd_7297085 : Nat := 4983230072969 + 3 ^ 40 * 7297085 * 2
def baseEnd_7297085 : Nat := 3746911981713687855078823

theorem tailTrace_7297085 : CollatzResearch.WordTrace tailWord_7297085 prefixEnd_7297085 3746911981713687855078823 := by
  unfold tailWord_7297085
  simp only [CollatzResearch.WordTrace]
  refine ⟨266146554768914762744644709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177431036512609841829763139 266146554768914762744644709)
  ·
    refine ⟨49902479019171518014620883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266146554768914762744644709 49902479019171518014620883)
    ·
      refine ⟨74853718528757277021931325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49902479019171518014620883 74853718528757277021931325)
      ·
        refine ⟨28070144448283978883224247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74853718528757277021931325 28070144448283978883224247)
        ·
          refine ⟨42105216672425968324836371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28070144448283978883224247 42105216672425968324836371)
          ·
            refine ⟨63157825008638952487254557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42105216672425968324836371 63157825008638952487254557)
            ·
              refine ⟨23684184378239607182720459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63157825008638952487254557 23684184378239607182720459)
              ·
                refine ⟨35526276567359410774080689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23684184378239607182720459 35526276567359410774080689)
                ·
                  refine ⟨26644707425519558080560517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35526276567359410774080689 26644707425519558080560517)
                  ·
                    refine ⟨4995882642284917140105097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26644707425519558080560517 4995882642284917140105097)
                    ·
                      refine ⟨3746911981713687855078823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995882642284917140105097 3746911981713687855078823)
                      ·
                        rfl

theorem cell23_7297085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_7297085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297085 prefixEnd_7297085 := by exact prefixLift 7297085
  have htrace : WordTrace (prefixWord ++ tailWord_7297085) baseStart_7297085 baseEnd_7297085 := by
    simpa [prefixWord, tailWord_7297085, baseEnd_7297085] using wordTrace_append hprefix tailTrace_7297085
  have hstable : (prefixWord ++ tailWord_7297085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297085).length < 2 ^ (prefixWord ++ tailWord_7297085).sum := by decide
  have hdescent : baseEnd_7297085 < baseStart_7297085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297112 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 1, 4]
def baseStart_7297112 : Nat := 118140960795 + 7297112 * 2 ^ 59
def prefixEnd_7297112 : Nat := 4983230072969 + 3 ^ 40 * 7297112 * 2
def baseEnd_7297112 : Nat := 1248975281897119749813733

theorem tailTrace_7297112 : CollatzResearch.WordTrace tailWord_7297112 prefixEnd_7297112 1248975281897119749813733 := by
  unfold tailWord_7297112
  simp only [CollatzResearch.WordTrace]
  refine ⟨133073769769908473177938795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177431693026544630903918393 133073769769908473177938795)
  ·
    refine ⟨199610654654862709766908193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133073769769908473177938795 199610654654862709766908193)
    ·
      refine ⟨149707990991147032325181145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199610654654862709766908193 149707990991147032325181145)
      ·
        refine ⟨112280993243360274243885859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149707990991147032325181145 112280993243360274243885859)
        ·
          refine ⟨168421489865040411365828789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112280993243360274243885859 168421489865040411365828789)
          ·
            refine ⟨15789514674847538565546449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168421489865040411365828789 15789514674847538565546449)
            ·
              refine ⟨11842136006135653924159837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15789514674847538565546449 11842136006135653924159837)
              ·
                refine ⟨4440801002300870221559939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11842136006135653924159837 4440801002300870221559939)
                ·
                  refine ⟨6661201503451305332339909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440801002300870221559939 6661201503451305332339909)
                  ·
                    refine ⟨1248975281897119749813733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661201503451305332339909 1248975281897119749813733)
                    ·
                      rfl

theorem cell23_7297112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_7297112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297112 prefixEnd_7297112 := by exact prefixLift 7297112
  have htrace : WordTrace (prefixWord ++ tailWord_7297112) baseStart_7297112 baseEnd_7297112 := by
    simpa [prefixWord, tailWord_7297112, baseEnd_7297112] using wordTrace_append hprefix tailTrace_7297112
  have hstable : (prefixWord ++ tailWord_7297112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297112).length < 2 ^ (prefixWord ++ tailWord_7297112).sum := by decide
  have hdescent : baseEnd_7297112 < baseStart_7297112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297125 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 6]
def baseStart_7297125 : Nat := 118140960795 + 7297125 * 2 ^ 59
def prefixEnd_7297125 : Nat := 4983230072969 + 3 ^ 40 * 7297125 * 2
def baseEnd_7297125 : Nat := 416325835659985299842071

theorem tailTrace_7297125 : CollatzResearch.WordTrace tailWord_7297125 prefixEnd_7297125 416325835659985299842071 := by
  unfold tailWord_7297125
  simp only [CollatzResearch.WordTrace]
  refine ⟨266148013688769849576100829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177432009125846566384067219 266148013688769849576100829)
  ·
    refine ⟨99805505133288693591037811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266148013688769849576100829 99805505133288693591037811)
    ·
      refine ⟨149708257699933040386556717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99805505133288693591037811 149708257699933040386556717)
      ·
        refine ⟨56140596637474890144958769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149708257699933040386556717 56140596637474890144958769)
        ·
          refine ⟨42105447478106167608719077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56140596637474890144958769 42105447478106167608719077)
          ·
            refine ⟨7894771402144906426634827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42105447478106167608719077 7894771402144906426634827)
            ·
              refine ⟨11842157103217359639952241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894771402144906426634827 11842157103217359639952241)
              ·
                refine ⟨8881617827413019729964181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11842157103217359639952241 8881617827413019729964181)
                ·
                  refine ⟨416325835659985299842071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8881617827413019729964181 416325835659985299842071)
                  ·
                    rfl

theorem cell23_7297125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_7297125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297125 prefixEnd_7297125 := by exact prefixLift 7297125
  have htrace : WordTrace (prefixWord ++ tailWord_7297125) baseStart_7297125 baseEnd_7297125 := by
    simpa [prefixWord, tailWord_7297125, baseEnd_7297125] using wordTrace_append hprefix tailTrace_7297125
  have hstable : (prefixWord ++ tailWord_7297125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297125).length < 2 ^ (prefixWord ++ tailWord_7297125).sum := by decide
  have hdescent : baseEnd_7297125 < baseStart_7297125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297135 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 3]
def baseStart_7297135 : Nat := 118140960795 + 7297135 * 2 ^ 59
def prefixEnd_7297135 : Nat := 4983230072969 + 3 ^ 40 * 7297135 * 2
def baseEnd_7297135 : Nat := 3746937655746412659453593

theorem tailTrace_7297135 : CollatzResearch.WordTrace tailWord_7297135 prefixEnd_7297135 3746937655746412659453593 := by
  unfold tailWord_7297135
  simp only [CollatzResearch.WordTrace]
  refine ⟨266148378418733621283964859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177432252279155747522643239 266148378418733621283964859)
  ·
    refine ⟨399222567628100431925947289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266148378418733621283964859 399222567628100431925947289)
    ·
      refine ⟨299416925721075323944460467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399222567628100431925947289 299416925721075323944460467)
      ·
        refine ⟨449125388581612985916690701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299416925721075323944460467 449125388581612985916690701)
        ·
          refine ⟨168422020718104869718759013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449125388581612985916690701 168422020718104869718759013)
          ·
            refine ⟨31579128884644663072267315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168422020718104869718759013 31579128884644663072267315)
            ·
              refine ⟨47368693326966994608400973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31579128884644663072267315 47368693326966994608400973)
              ·
                refine ⟨17763259997612622978150365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47368693326966994608400973 17763259997612622978150365)
                ·
                  refine ⟨6661222499104733616806387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17763259997612622978150365 6661222499104733616806387)
                  ·
                    refine ⟨9991833748657100425209581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661222499104733616806387 9991833748657100425209581)
                    ·
                      refine ⟨3746937655746412659453593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991833748657100425209581 3746937655746412659453593)
                      ·
                        rfl

theorem cell23_7297135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_7297135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297135 prefixEnd_7297135 := by exact prefixLift 7297135
  have htrace : WordTrace (prefixWord ++ tailWord_7297135) baseStart_7297135 baseEnd_7297135 := by
    simpa [prefixWord, tailWord_7297135, baseEnd_7297135] using wordTrace_append hprefix tailTrace_7297135
  have hstable : (prefixWord ++ tailWord_7297135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297135).length < 2 ^ (prefixWord ++ tailWord_7297135).sum := by decide
  have hdescent : baseEnd_7297135 < baseStart_7297135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297142 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_7297142 : Nat := 118140960795 + 7297142 * 2 ^ 59
def prefixEnd_7297142 : Nat := 4983230072969 + 3 ^ 40 * 7297142 * 2
def baseEnd_7297142 : Nat := 416326805567888236896229

theorem tailTrace_7297142 : CollatzResearch.WordTrace tailWord_7297142 prefixEnd_7297142 416326805567888236896229 := by
  unfold tailWord_7297142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634289608106766342466855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177432422486472174319646453 16634289608106766342466855)
  ·
    refine ⟨24951434412160149513700283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16634289608106766342466855 24951434412160149513700283)
    ·
      refine ⟨37427151618240224270550425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24951434412160149513700283 37427151618240224270550425)
      ·
        refine ⟨28070363713680168202912819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37427151618240224270550425 28070363713680168202912819)
        ·
          refine ⟨42105545570520252304369229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28070363713680168202912819 42105545570520252304369229)
          ·
            refine ⟨15789579588945094614138461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42105545570520252304369229 15789579588945094614138461)
            ·
              refine ⟨5921092345854410480301923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15789579588945094614138461 5921092345854410480301923)
              ·
                refine ⟨8881638518781615720452885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921092345854410480301923 8881638518781615720452885)
                ·
                  refine ⟨416326805567888236896229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8881638518781615720452885 416326805567888236896229)
                  ·
                    rfl

theorem cell23_7297142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_7297142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297142 prefixEnd_7297142 := by exact prefixLift 7297142
  have htrace : WordTrace (prefixWord ++ tailWord_7297142) baseStart_7297142 baseEnd_7297142 := by
    simpa [prefixWord, tailWord_7297142, baseEnd_7297142] using wordTrace_append hprefix tailTrace_7297142
  have hstable : (prefixWord ++ tailWord_7297142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297142).length < 2 ^ (prefixWord ++ tailWord_7297142).sum := by decide
  have hdescent : baseEnd_7297142 < baseStart_7297142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297145 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 1, 5, 2]
def baseStart_7297145 : Nat := 118140960795 + 7297145 * 2 ^ 59
def prefixEnd_7297145 : Nat := 4983230072969 + 3 ^ 40 * 7297145 * 2
def baseEnd_7297145 : Nat := 3746942790552957620328547

theorem tailTrace_7297145 : CollatzResearch.WordTrace tailWord_7297145 prefixEnd_7297145 3746942790552957620328547 := by
  unfold tailWord_7297145
  simp only [CollatzResearch.WordTrace]
  refine ⟨266148743148697392991828889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177432495432464928661219259 266148743148697392991828889)
  ·
    refine ⟨199611557361523044743871667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266148743148697392991828889 199611557361523044743871667)
    ·
      refine ⟨299417336042284567115807501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199611557361523044743871667 299417336042284567115807501)
      ·
        refine ⟨112281501015856712668427813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299417336042284567115807501 112281501015856712668427813)
        ·
          refine ⟨21052781440473133625330215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112281501015856712668427813 21052781440473133625330215)
          ·
            refine ⟨31579172160709700437995323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21052781440473133625330215 31579172160709700437995323)
            ·
              refine ⟨47368758241064550656992985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31579172160709700437995323 47368758241064550656992985)
              ·
                refine ⟨35526568680798412992744739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47368758241064550656992985 35526568680798412992744739)
                ·
                  refine ⟨53289853021197619489117109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35526568680798412992744739 53289853021197619489117109)
                  ·
                    refine ⟨4995923720737276827104729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53289853021197619489117109 4995923720737276827104729)
                    ·
                      refine ⟨3746942790552957620328547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995923720737276827104729 3746942790552957620328547)
                      ·
                        rfl

theorem cell23_7297145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_7297145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297145 prefixEnd_7297145 := by exact prefixLift 7297145
  have htrace : WordTrace (prefixWord ++ tailWord_7297145) baseStart_7297145 baseEnd_7297145 := by
    simpa [prefixWord, tailWord_7297145, baseEnd_7297145] using wordTrace_append hprefix tailTrace_7297145
  have hstable : (prefixWord ++ tailWord_7297145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297145).length < 2 ^ (prefixWord ++ tailWord_7297145).sum := by decide
  have hdescent : baseEnd_7297145 < baseStart_7297145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297155 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 1, 5]
def baseStart_7297155 : Nat := 118140960795 + 7297155 * 2 ^ 59
def prefixEnd_7297155 : Nat := 4983230072969 + 3 ^ 40 * 7297155 * 2
def baseEnd_7297155 : Nat := 1248982641786500860401167

theorem tailTrace_7297155 : CollatzResearch.WordTrace tailWord_7297155 prefixEnd_7297155 1248982641786500860401167 := by
  unfold tailWord_7297155
  simp only [CollatzResearch.WordTrace]
  refine ⟨266149107878661164699692919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177432738585774109799795279 266149107878661164699692919)
  ·
    refine ⟨399223661817991747049539379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266149107878661164699692919 399223661817991747049539379)
    ·
      refine ⟨598835492726987620574309069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399223661817991747049539379 598835492726987620574309069)
      ·
        refine ⟨224563309772620357715365901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598835492726987620574309069 224563309772620357715365901)
        ·
          refine ⟨84211241164732634143262213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224563309772620357715365901 84211241164732634143262213)
          ·
            refine ⟨15789607718387368901861665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84211241164732634143262213 15789607718387368901861665)
            ·
              refine ⟨11842205788790526676396249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15789607718387368901861665 11842205788790526676396249)
              ·
                refine ⟨8881654341592895007297187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11842205788790526676396249 8881654341592895007297187)
                ·
                  refine ⟨13322481512389342510945781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8881654341592895007297187 13322481512389342510945781)
                  ·
                    refine ⟨1248982641786500860401167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13322481512389342510945781 1248982641786500860401167)
                    ·
                      rfl

theorem cell23_7297155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 5].length) (baseStart_7297155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297155 prefixEnd_7297155 := by exact prefixLift 7297155
  have htrace : WordTrace (prefixWord ++ tailWord_7297155) baseStart_7297155 baseEnd_7297155 := by
    simpa [prefixWord, tailWord_7297155, baseEnd_7297155] using wordTrace_append hprefix tailTrace_7297155
  have hstable : (prefixWord ++ tailWord_7297155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297155).length < 2 ^ (prefixWord ++ tailWord_7297155).sum := by decide
  have hdescent : baseEnd_7297155 < baseStart_7297155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297168 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 6, 4]
def baseStart_7297168 : Nat := 118140960795 + 7297168 * 2 ^ 59
def prefixEnd_7297168 : Nat := 4983230072969 + 3 ^ 40 * 7297168 * 2
def baseEnd_7297168 : Nat := 1248984866869337010113647

theorem tailTrace_7297168 : CollatzResearch.WordTrace tailWord_7297168 prefixEnd_7297168 1248984866869337010113647 := by
  unfold tailWord_7297168
  simp only [CollatzResearch.WordTrace]
  refine ⟨133074791013807033959958079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177433054685076045279944105 133074791013807033959958079)
  ·
    refine ⟨199612186520710550939937119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133074791013807033959958079 199612186520710550939937119)
    ·
      refine ⟨299418279781065826409905679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199612186520710550939937119 299418279781065826409905679)
      ·
        refine ⟨449127419671598739614858519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299418279781065826409905679 449127419671598739614858519)
        ·
          refine ⟨673691129507398109422287779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449127419671598739614858519 673691129507398109422287779)
          ·
            refine ⟨1010536694261097164133431669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673691129507398109422287779 1010536694261097164133431669)
            ·
              refine ⟨94737815086977859137509219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1010536694261097164133431669 94737815086977859137509219)
              ·
                refine ⟨142106722630466788706263829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94737815086977859137509219 142106722630466788706263829)
                ·
                  refine ⟨6661252623303130720606117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142106722630466788706263829 6661252623303130720606117)
                  ·
                    refine ⟨1248984866869337010113647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661252623303130720606117 1248984866869337010113647)
                    ·
                      rfl

theorem cell23_7297168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_7297168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297168 prefixEnd_7297168 := by exact prefixLift 7297168
  have htrace : WordTrace (prefixWord ++ tailWord_7297168) baseStart_7297168 baseEnd_7297168 := by
    simpa [prefixWord, tailWord_7297168, baseEnd_7297168] using wordTrace_append hprefix tailTrace_7297168
  have hstable : (prefixWord ++ tailWord_7297168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297168).length < 2 ^ (prefixWord ++ tailWord_7297168).sum := by decide
  have hdescent : baseEnd_7297168 < baseStart_7297168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297185 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 4, 4]
def baseStart_7297185 : Nat := 118140960795 + 7297185 * 2 ^ 59
def prefixEnd_7297185 : Nat := 4983230072969 + 3 ^ 40 * 7297185 * 2
def baseEnd_7297185 : Nat := 1248987776593045821276121

theorem tailTrace_7297185 : CollatzResearch.WordTrace tailWord_7297185 prefixEnd_7297185 1248987776593045821276121 := by
  unfold tailWord_7297185
  simp only [CollatzResearch.WordTrace]
  refine ⟨266150202068552479823285009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177433468045701653215523339 266150202068552479823285009)
  ·
    refine ⟨199612651551414359867463757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266150202068552479823285009 199612651551414359867463757)
    ·
      refine ⟨74854744331780384950298909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199612651551414359867463757 74854744331780384950298909)
      ·
        refine ⟨28070529124417644356362091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74854744331780384950298909 28070529124417644356362091)
        ·
          refine ⟨42105793686626466534543137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28070529124417644356362091 42105793686626466534543137)
          ·
            refine ⟨31579345264969849900907353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42105793686626466534543137 31579345264969849900907353)
            ·
              refine ⟨23684508948727387425680515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31579345264969849900907353 23684508948727387425680515)
              ·
                refine ⟨35526763423091081138520773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23684508948727387425680515 35526763423091081138520773)
                ·
                  refine ⟨6661268141829577713472645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35526763423091081138520773 6661268141829577713472645)
                  ·
                    refine ⟨1248987776593045821276121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661268141829577713472645 1248987776593045821276121)
                    ·
                      rfl

theorem cell23_7297185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_7297185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297185 prefixEnd_7297185 := by exact prefixLift 7297185
  have htrace : WordTrace (prefixWord ++ tailWord_7297185) baseStart_7297185 baseEnd_7297185 := by
    simpa [prefixWord, tailWord_7297185, baseEnd_7297185] using wordTrace_append hprefix tailTrace_7297185
  have hstable : (prefixWord ++ tailWord_7297185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297185).length < 2 ^ (prefixWord ++ tailWord_7297185).sum := by decide
  have hdescent : baseEnd_7297185 < baseStart_7297185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297212 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_7297212 : Nat := 118140960795 + 7297212 * 2 ^ 59
def prefixEnd_7297212 : Nat := 4983230072969 + 3 ^ 40 * 7297212 * 2
def baseEnd_7297212 : Nat := 3746977193756808858190739

theorem tailTrace_7297212 : CollatzResearch.WordTrace tailWord_7297212 prefixEnd_7297212 3746977193756808858190739 := by
  unfold tailWord_7297212
  simp only [CollatzResearch.WordTrace]
  refine ⟨133075593419727331717258945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177434124559636442289678593 133075593419727331717258945)
  ·
    refine ⟨99806695064795498787944209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133075593419727331717258945 99806695064795498787944209)
    ·
      refine ⟨74855021298596624090958157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99806695064795498787944209 74855021298596624090958157)
      ·
        refine ⟨28070632986973734034109309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74855021298596624090958157 28070632986973734034109309)
        ·
          refine ⟨10526487370115150262790991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28070632986973734034109309 10526487370115150262790991)
          ·
            refine ⟨15789731055172725394186487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10526487370115150262790991 15789731055172725394186487)
            ·
              refine ⟨23684596582759088091279731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789731055172725394186487 23684596582759088091279731)
              ·
                refine ⟨35526894874138632136919597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23684596582759088091279731 35526894874138632136919597)
                ·
                  refine ⟨13322585577801987051344849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35526894874138632136919597 13322585577801987051344849)
                  ·
                    refine ⟨9991939183351490288508637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13322585577801987051344849 9991939183351490288508637)
                    ·
                      refine ⟨3746977193756808858190739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991939183351490288508637 3746977193756808858190739)
                      ·
                        rfl

theorem cell23_7297212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_7297212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297212 prefixEnd_7297212 := by exact prefixLift 7297212
  have htrace : WordTrace (prefixWord ++ tailWord_7297212) baseStart_7297212 baseEnd_7297212 := by
    simpa [prefixWord, tailWord_7297212, baseEnd_7297212] using wordTrace_append hprefix tailTrace_7297212
  have hstable : (prefixWord ++ tailWord_7297212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297212).length < 2 ^ (prefixWord ++ tailWord_7297212).sum := by decide
  have hdescent : baseEnd_7297212 < baseStart_7297212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297225 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 3]
def baseStart_7297225 : Nat := 118140960795 + 7297225 * 2 ^ 59
def prefixEnd_7297225 : Nat := 4983230072969 + 3 ^ 40 * 7297225 * 2
def baseEnd_7297225 : Nat := 3746983869005317307328179

theorem tailTrace_7297225 : CollatzResearch.WordTrace tailWord_7297225 prefixEnd_7297225 3746983869005317307328179 := by
  unfold tailWord_7297225
  simp only [CollatzResearch.WordTrace]
  refine ⟨266151660988407566654741129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177434440658938377769827419 266151660988407566654741129)
  ·
    refine ⟨199613745741305674991055847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266151660988407566654741129 199613745741305674991055847)
    ·
      refine ⟨299420618611958512486583771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199613745741305674991055847 299420618611958512486583771)
      ·
        refine ⟨449130927917937768729875657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299420618611958512486583771 449130927917937768729875657)
        ·
          refine ⟨336848195938453326547406743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449130927917937768729875657 336848195938453326547406743)
          ·
            refine ⟨505272293907679989821110115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336848195938453326547406743 505272293907679989821110115)
            ·
              refine ⟨757908440861519984731665173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505272293907679989821110115 757908440861519984731665173)
              ·
                refine ⟨35526958165383749284296805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 757908440861519984731665173 35526958165383749284296805)
                ·
                  refine ⟨6661304656009452990805651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35526958165383749284296805 6661304656009452990805651)
                  ·
                    refine ⟨9991956984014179486208477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661304656009452990805651 9991956984014179486208477)
                    ·
                      refine ⟨3746983869005317307328179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991956984014179486208477 3746983869005317307328179)
                      ·
                        rfl

theorem cell23_7297225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_7297225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297225 prefixEnd_7297225 := by exact prefixLift 7297225
  have htrace : WordTrace (prefixWord ++ tailWord_7297225) baseStart_7297225 baseEnd_7297225 := by
    simpa [prefixWord, tailWord_7297225, baseEnd_7297225] using wordTrace_append hprefix tailTrace_7297225
  have hstable : (prefixWord ++ tailWord_7297225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297225).length < 2 ^ (prefixWord ++ tailWord_7297225).sum := by decide
  have hdescent : baseEnd_7297225 < baseStart_7297225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297235 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 7, 3, 2]
def baseStart_7297235 : Nat := 118140960795 + 7297235 * 2 ^ 59
def prefixEnd_7297235 : Nat := 4983230072969 + 3 ^ 40 * 7297235 * 2
def baseEnd_7297235 : Nat := 3746989003811862268203133

theorem tailTrace_7297235 : CollatzResearch.WordTrace tailWord_7297235 prefixEnd_7297235 3746989003811862268203133 := by
  unfold tailWord_7297235
  simp only [CollatzResearch.WordTrace]
  refine ⟨266152025718371338362605159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177434683812247558908403439 266152025718371338362605159)
  ·
    refine ⟨399228038577557007543907739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266152025718371338362605159 399228038577557007543907739)
    ·
      refine ⟨598842057866335511315861609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399228038577557007543907739 598842057866335511315861609)
      ·
        refine ⟨449131543399751633486896207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598842057866335511315861609 449131543399751633486896207)
        ·
          refine ⟨673697315099627450230344311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449131543399751633486896207 673697315099627450230344311)
          ·
            refine ⟨1010545972649441175345516467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673697315099627450230344311 1010545972649441175345516467)
            ·
              refine ⟨1515818958974161763018274701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010545972649441175345516467 1515818958974161763018274701)
              ·
                refine ⟨568432109615310661131853013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1515818958974161763018274701 568432109615310661131853013)
                ·
                  refine ⟨13322627569108843620277805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 568432109615310661131853013 13322627569108843620277805)
                  ·
                    refine ⟨4995985338415816357604177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13322627569108843620277805 4995985338415816357604177)
                    ·
                      refine ⟨3746989003811862268203133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4995985338415816357604177 3746989003811862268203133)
                      ·
                        rfl

theorem cell23_7297235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3, 2].length) (baseStart_7297235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297235 prefixEnd_7297235 := by exact prefixLift 7297235
  have htrace : WordTrace (prefixWord ++ tailWord_7297235) baseStart_7297235 baseEnd_7297235 := by
    simpa [prefixWord, tailWord_7297235, baseEnd_7297235] using wordTrace_append hprefix tailTrace_7297235
  have hstable : (prefixWord ++ tailWord_7297235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297235).length < 2 ^ (prefixWord ++ tailWord_7297235).sum := by decide
  have hdescent : baseEnd_7297235 < baseStart_7297235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297242 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_7297242 : Nat := 118140960795 + 7297242 * 2 ^ 59
def prefixEnd_7297242 : Nat := 4983230072969 + 3 ^ 40 * 7297242 * 2
def baseEnd_7297242 : Nat := 3746992598176443740815601

theorem tailTrace_7297242 : CollatzResearch.WordTrace tailWord_7297242 prefixEnd_7297242 3746992598176443740815601 := by
  unfold tailWord_7297242
  simp only [CollatzResearch.WordTrace]
  refine ⟨66538070257336494639527495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177434854019563985705406653 66538070257336494639527495)
  ·
    refine ⟨99807105386004741959291243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66538070257336494639527495 99807105386004741959291243)
    ·
      refine ⟨149710658079007112938936865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99807105386004741959291243 149710658079007112938936865)
      ·
        refine ⟨112282993559255334704202649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149710658079007112938936865 112282993559255334704202649)
        ·
          refine ⟨84212245169441501028151987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112282993559255334704202649 84212245169441501028151987)
          ·
            refine ⟨126318367754162251542227981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84212245169441501028151987 126318367754162251542227981)
            ·
              refine ⟨47369387907810844328335493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126318367754162251542227981 47369387907810844328335493)
              ·
                refine ⟨8881760232714533311562905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47369387907810844328335493 8881760232714533311562905)
                ·
                  refine ⟨6661320174535899983672179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8881760232714533311562905 6661320174535899983672179)
                  ·
                    refine ⟨9991980261803849975508269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661320174535899983672179 9991980261803849975508269)
                    ·
                      refine ⟨3746992598176443740815601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9991980261803849975508269 3746992598176443740815601)
                      ·
                        rfl

theorem cell23_7297242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_7297242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297242 prefixEnd_7297242 := by exact prefixLift 7297242
  have htrace : WordTrace (prefixWord ++ tailWord_7297242) baseStart_7297242 baseEnd_7297242 := by
    simpa [prefixWord, tailWord_7297242, baseEnd_7297242] using wordTrace_append hprefix tailTrace_7297242
  have hstable : (prefixWord ++ tailWord_7297242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297242).length < 2 ^ (prefixWord ++ tailWord_7297242).sum := by decide
  have hdescent : baseEnd_7297242 < baseStart_7297242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297245 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7297245 : Nat := 118140960795 + 7297245 * 2 ^ 59
def prefixEnd_7297245 : Nat := 4983230072969 + 3 ^ 40 * 7297245 * 2
def baseEnd_7297245 : Nat := 1248998046206135743026029

theorem tailTrace_7297245 : CollatzResearch.WordTrace tailWord_7297245 prefixEnd_7297245 1248998046206135743026029 := by
  unfold tailWord_7297245
  simp only [CollatzResearch.WordTrace]
  refine ⟨266152390448335110070469189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177434926965556740046979459 266152390448335110070469189)
  ·
    refine ⟨49903573209062833138212973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266152390448335110070469189 49903573209062833138212973)
    ·
      refine ⟨18713839953398562426829865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49903573209062833138212973 18713839953398562426829865)
      ·
        refine ⟨14035379965048921820122399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18713839953398562426829865 14035379965048921820122399)
        ·
          refine ⟨21053069947573382730183599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14035379965048921820122399 21053069947573382730183599)
          ·
            refine ⟨31579604921360074095275399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21053069947573382730183599 31579604921360074095275399)
            ·
              refine ⟨47369407382040111142913099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31579604921360074095275399 47369407382040111142913099)
              ·
                refine ⟨71054111073060166714369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47369407382040111142913099 71054111073060166714369649)
                ·
                  refine ⟨53290583304795125035777237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71054111073060166714369649 53290583304795125035777237)
                  ·
                    refine ⟨1248998046206135743026029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53290583304795125035777237 1248998046206135743026029)
                    ·
                      rfl

theorem cell23_7297245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7297245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297245 prefixEnd_7297245 := by exact prefixLift 7297245
  have htrace : WordTrace (prefixWord ++ tailWord_7297245) baseStart_7297245 baseEnd_7297245 := by
    simpa [prefixWord, tailWord_7297245, baseEnd_7297245] using wordTrace_append hprefix tailTrace_7297245
  have hstable : (prefixWord ++ tailWord_7297245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297245).length < 2 ^ (prefixWord ++ tailWord_7297245).sum := by decide
  have hdescent : baseEnd_7297245 < baseStart_7297245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297248 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_7297248 : Nat := 118140960795 + 7297248 * 2 ^ 59
def prefixEnd_7297248 : Nat := 4983230072969 + 3 ^ 40 * 7297248 * 2
def baseEnd_7297248 : Nat := 3746995679060370717340573

theorem tailTrace_7297248 : CollatzResearch.WordTrace tailWord_7297248 prefixEnd_7297248 3746995679060370717340573 := by
  unfold tailWord_7297248
  simp only [CollatzResearch.WordTrace]
  refine ⟨133076249933662120791414199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177434999911549494388552265 133076249933662120791414199)
  ·
    refine ⟨199614374900493181187121299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133076249933662120791414199 199614374900493181187121299)
    ·
      refine ⟨299421562350739771780681949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199614374900493181187121299 299421562350739771780681949)
      ·
        refine ⟨112283085881527414417755731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299421562350739771780681949 112283085881527414417755731)
        ·
          refine ⟨168424628822291121626633597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112283085881527414417755731 168424628822291121626633597)
          ·
            refine ⟨63159235808359170609987599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168424628822291121626633597 63159235808359170609987599)
            ·
              refine ⟨94738853712538755914981399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63159235808359170609987599 94738853712538755914981399)
              ·
                refine ⟨142108280568808133872472099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94738853712538755914981399 142108280568808133872472099)
                ·
                  refine ⟨213162420853212200808708149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142108280568808133872472099 213162420853212200808708149)
                  ·
                    refine ⟨19983976954988643825816389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 213162420853212200808708149 19983976954988643825816389)
                    ·
                      refine ⟨3746995679060370717340573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19983976954988643825816389 3746995679060370717340573)
                      ·
                        rfl

theorem cell23_7297248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_7297248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297248 prefixEnd_7297248 := by exact prefixLift 7297248
  have htrace : WordTrace (prefixWord ++ tailWord_7297248) baseStart_7297248 baseEnd_7297248 := by
    simpa [prefixWord, tailWord_7297248, baseEnd_7297248] using wordTrace_append hprefix tailTrace_7297248
  have hstable : (prefixWord ++ tailWord_7297248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297248).length < 2 ^ (prefixWord ++ tailWord_7297248).sum := by decide
  have hdescent : baseEnd_7297248 < baseStart_7297248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297315 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 3]
def baseStart_7297315 : Nat := 118140960795 + 7297315 * 2 ^ 59
def prefixEnd_7297315 : Nat := 4983230072969 + 3 ^ 40 * 7297315 * 2
def baseEnd_7297315 : Nat := 3747030082264221955202765

theorem tailTrace_7297315 : CollatzResearch.WordTrace tailWord_7297315 prefixEnd_7297315 3747030082264221955202765 := by
  unfold tailWord_7297315
  simp only [CollatzResearch.WordTrace]
  refine ⟨266154943558081512025517399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177436629038721008017011599 266154943558081512025517399)
  ·
    refine ⟨399232415337122268038276099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266154943558081512025517399 399232415337122268038276099)
    ·
      refine ⟨598848623005683402057414149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399232415337122268038276099 598848623005683402057414149)
      ·
        refine ⟨112284116813565637885765153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598848623005683402057414149 112284116813565637885765153)
        ·
          refine ⟨84213087610174228414323865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112284116813565637885765153 84213087610174228414323865)
          ·
            refine ⟨63159815707630671310742899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84213087610174228414323865 63159815707630671310742899)
            ·
              refine ⟨94739723561446006966114349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63159815707630671310742899 94739723561446006966114349)
              ·
                refine ⟨35527396335542252612292881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94739723561446006966114349 35527396335542252612292881)
                ·
                  refine ⟨26645547251656689459219661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35527396335542252612292881 26645547251656689459219661)
                  ·
                    refine ⟨9992080219371258547207373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26645547251656689459219661 9992080219371258547207373)
                    ·
                      refine ⟨3747030082264221955202765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992080219371258547207373 3747030082264221955202765)
                      ·
                        rfl

theorem cell23_7297315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_7297315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297315 prefixEnd_7297315 := by exact prefixLift 7297315
  have htrace : WordTrace (prefixWord ++ tailWord_7297315) baseStart_7297315 baseEnd_7297315 := by
    simpa [prefixWord, tailWord_7297315, baseEnd_7297315] using wordTrace_append hprefix tailTrace_7297315
  have hstable : (prefixWord ++ tailWord_7297315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297315).length < 2 ^ (prefixWord ++ tailWord_7297315).sum := by decide
  have hdescent : baseEnd_7297315 < baseStart_7297315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297328 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_7297328 : Nat := 118140960795 + 7297328 * 2 ^ 59
def prefixEnd_7297328 : Nat := 4983230072969 + 3 ^ 40 * 7297328 * 2
def baseEnd_7297328 : Nat := 3747036757512730404340205

theorem tailTrace_7297328 : CollatzResearch.WordTrace tailWord_7297328 prefixEnd_7297328 3747036757512730404340205 := by
  unfold tailWord_7297328
  simp only [CollatzResearch.WordTrace]
  refine ⟨133077708853517207622870319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177436945138022943497160425 133077708853517207622870319)
  ·
    refine ⟨199616563280275811434305479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133077708853517207622870319 199616563280275811434305479)
    ·
      refine ⟨299424844920413717151458219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199616563280275811434305479 299424844920413717151458219)
      ·
        refine ⟨449137267380620575727187329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299424844920413717151458219 449137267380620575727187329)
        ·
          refine ⟨336852950535465431795390497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449137267380620575727187329 336852950535465431795390497)
          ·
            refine ⟨252639712901599073846542873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336852950535465431795390497 252639712901599073846542873)
            ·
              refine ⟨189479784676199305384907155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252639712901599073846542873 189479784676199305384907155)
              ·
                refine ⟨284219677014298958077360733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189479784676199305384907155 284219677014298958077360733)
                ·
                  refine ⟨106582378880362109279010275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284219677014298958077360733 106582378880362109279010275)
                  ·
                    refine ⟨159873568320543163918515413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106582378880362109279010275 159873568320543163918515413)
                    ·
                      refine ⟨3747036757512730404340205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159873568320543163918515413 3747036757512730404340205)
                      ·
                        rfl

theorem cell23_7297328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_7297328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297328 prefixEnd_7297328 := by exact prefixLift 7297328
  have htrace : WordTrace (prefixWord ++ tailWord_7297328) baseStart_7297328 baseEnd_7297328 := by
    simpa [prefixWord, tailWord_7297328, baseEnd_7297328] using wordTrace_append hprefix tailTrace_7297328
  have hstable : (prefixWord ++ tailWord_7297328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297328).length < 2 ^ (prefixWord ++ tailWord_7297328).sum := by decide
  have hdescent : baseEnd_7297328 < baseStart_7297328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297375 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_7297375 : Nat := 118140960795 + 7297375 * 2 ^ 59
def prefixEnd_7297375 : Nat := 4983230072969 + 3 ^ 40 * 7297375 * 2
def baseEnd_7297375 : Nat := 3747060891103491720452489

theorem tailTrace_7297375 : CollatzResearch.WordTrace tailWord_7297375 prefixEnd_7297375 3747060891103491720452489 := by
  unfold tailWord_7297375
  simp only [CollatzResearch.WordTrace]
  refine ⟨266157131937864142272701579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177438087958576094848467719 266157131937864142272701579)
  ·
    refine ⟨399235697906796213409052369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266157131937864142272701579 399235697906796213409052369)
    ·
      refine ⟨299426773430097160056789277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399235697906796213409052369 299426773430097160056789277)
      ·
        refine ⟨112285040036286435021295979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299426773430097160056789277 112285040036286435021295979)
        ·
          refine ⟨168427560054429652531943969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112285040036286435021295979 168427560054429652531943969)
          ·
            refine ⟨126320670040822239398957977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168427560054429652531943969 126320670040822239398957977)
            ·
              refine ⟨94740502530616679549218483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126320670040822239398957977 94740502530616679549218483)
              ·
                refine ⟨142110753795925019323827725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94740502530616679549218483 142110753795925019323827725)
                ·
                  refine ⟨53291532673471882246435397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142110753795925019323827725 53291532673471882246435397)
                  ·
                    refine ⟨9992162376275977921206637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53291532673471882246435397 9992162376275977921206637)
                    ·
                      refine ⟨3747060891103491720452489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992162376275977921206637 3747060891103491720452489)
                      ·
                        rfl

theorem cell23_7297375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_7297375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297375 prefixEnd_7297375 := by exact prefixLift 7297375
  have htrace : WordTrace (prefixWord ++ tailWord_7297375) baseStart_7297375 baseEnd_7297375 := by
    simpa [prefixWord, tailWord_7297375, baseEnd_7297375] using wordTrace_append hprefix tailTrace_7297375
  have hstable : (prefixWord ++ tailWord_7297375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297375).length < 2 ^ (prefixWord ++ tailWord_7297375).sum := by decide
  have hdescent : baseEnd_7297375 < baseStart_7297375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297392 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_7297392 : Nat := 118140960795 + 7297392 * 2 ^ 59
def prefixEnd_7297392 : Nat := 4983230072969 + 3 ^ 40 * 7297392 * 2
def baseEnd_7297392 : Nat := 3747069620274618153939911

theorem tailTrace_7297392 : CollatzResearch.WordTrace tailWord_7297392 prefixEnd_7297392 3747069620274618153939911 := by
  unfold tailWord_7297392
  simp only [CollatzResearch.WordTrace]
  refine ⟨133078875989401277088035215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177438501319201702784046953 133078875989401277088035215)
  ·
    refine ⟨199618313984101915632052823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133078875989401277088035215 199618313984101915632052823)
    ·
      refine ⟨299427470976152873448079235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199618313984101915632052823 299427470976152873448079235)
      ·
        refine ⟨449141206464229310172118853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299427470976152873448079235 449141206464229310172118853)
        ·
          refine ⟨84213976212042995657272285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 449141206464229310172118853 84213976212042995657272285)
          ·
            refine ⟨31580241079516123371477107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84213976212042995657272285 31580241079516123371477107)
            ·
              refine ⟨47370361619274185057215661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31580241079516123371477107 47370361619274185057215661)
              ·
                refine ⟨17763885607227819396455873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47370361619274185057215661 17763885607227819396455873)
                ·
                  refine ⟨13322914205420864547341905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17763885607227819396455873 13322914205420864547341905)
                  ·
                    refine ⟨9992185654065648410506429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13322914205420864547341905 9992185654065648410506429)
                    ·
                      refine ⟨3747069620274618153939911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992185654065648410506429 3747069620274618153939911)
                      ·
                        rfl

theorem cell23_7297392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_7297392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297392 prefixEnd_7297392 := by exact prefixLift 7297392
  have htrace : WordTrace (prefixWord ++ tailWord_7297392) baseStart_7297392 baseEnd_7297392 := by
    simpa [prefixWord, tailWord_7297392, baseEnd_7297392] using wordTrace_append hprefix tailTrace_7297392
  have hstable : (prefixWord ++ tailWord_7297392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297392).length < 2 ^ (prefixWord ++ tailWord_7297392).sum := by decide
  have hdescent : baseEnd_7297392 < baseStart_7297392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297409 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_7297409 : Nat := 118140960795 + 7297409 * 2 ^ 59
def prefixEnd_7297409 : Nat := 4983230072969 + 3 ^ 40 * 7297409 * 2
def baseEnd_7297409 : Nat := 3747078349445744587427333

theorem tailTrace_7297409 : CollatzResearch.WordTrace tailWord_7297409 prefixEnd_7297409 3747078349445744587427333 := by
  unfold tailWord_7297409
  simp only [CollatzResearch.WordTrace]
  refine ⟨266158372019740966079439281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177438914679827310719626187 266158372019740966079439281)
  ·
    refine ⟨199618779014805724559579461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266158372019740966079439281 199618779014805724559579461)
    ·
      refine ⟨37428521065276073354921149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199618779014805724559579461 37428521065276073354921149)
      ·
        refine ⟨14035695399478527508095431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37428521065276073354921149 14035695399478527508095431)
        ·
          refine ⟨21053543099217791262143147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14035695399478527508095431 21053543099217791262143147)
          ·
            refine ⟨31580314648826686893214721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21053543099217791262143147 31580314648826686893214721)
            ·
              refine ⟨23685235986620015169911041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31580314648826686893214721 23685235986620015169911041)
              ·
                refine ⟨17763926989965011377433281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23685235986620015169911041 17763926989965011377433281)
                ·
                  refine ⟨13322945242473758533074961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17763926989965011377433281 13322945242473758533074961)
                  ·
                    refine ⟨9992208931855318899806221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13322945242473758533074961 9992208931855318899806221)
                    ·
                      refine ⟨3747078349445744587427333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992208931855318899806221 3747078349445744587427333)
                      ·
                        rfl

theorem cell23_7297409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_7297409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297409 prefixEnd_7297409 := by exact prefixLift 7297409
  have htrace : WordTrace (prefixWord ++ tailWord_7297409) baseStart_7297409 baseEnd_7297409 := by
    simpa [prefixWord, tailWord_7297409, baseEnd_7297409] using wordTrace_append hprefix tailTrace_7297409
  have hstable : (prefixWord ++ tailWord_7297409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297409).length < 2 ^ (prefixWord ++ tailWord_7297409).sum := by decide
  have hdescent : baseEnd_7297409 < baseStart_7297409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297412 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 6]
def baseStart_7297412 : Nat := 118140960795 + 7297412 * 2 ^ 59
def prefixEnd_7297412 : Nat := 4983230072969 + 3 ^ 40 * 7297412 * 2
def baseEnd_7297412 : Nat := 416342209987523119521091

theorem tailTrace_7297412 : CollatzResearch.WordTrace tailWord_7297412 prefixEnd_7297412 416342209987523119521091 := by
  unfold tailWord_7297412
  simp only [CollatzResearch.WordTrace]
  refine ⟨133079240719365048795899245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177438987625820065061198993 133079240719365048795899245)
  ·
    refine ⟨49904715269761893298462217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133079240719365048795899245 49904715269761893298462217)
    ·
      refine ⟨37428536452321419973846663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49904715269761893298462217 37428536452321419973846663)
      ·
        refine ⟨56142804678482129960769995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37428536452321419973846663 56142804678482129960769995)
        ·
          refine ⟨84214207017723194941154993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56142804678482129960769995 84214207017723194941154993)
          ·
            refine ⟨63160655263292396205866245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84214207017723194941154993 63160655263292396205866245)
            ·
              refine ⟨11842622861867324288599921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63160655263292396205866245 11842622861867324288599921)
              ·
                refine ⟨8881967146400493216449941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11842622861867324288599921 8881967146400493216449941)
                ·
                  refine ⟨416342209987523119521091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8881967146400493216449941 416342209987523119521091)
                  ·
                    rfl

theorem cell23_7297412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_7297412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297412 prefixEnd_7297412 := by exact prefixLift 7297412
  have htrace : WordTrace (prefixWord ++ tailWord_7297412) baseStart_7297412 baseEnd_7297412 := by
    simpa [prefixWord, tailWord_7297412, baseEnd_7297412] using wordTrace_append hprefix tailTrace_7297412
  have hstable : (prefixWord ++ tailWord_7297412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297412).length < 2 ^ (prefixWord ++ tailWord_7297412).sum := by decide
  have hdescent : baseEnd_7297412 < baseStart_7297412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297415 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_7297415 : Nat := 118140960795 + 7297415 * 2 ^ 59
def prefixEnd_7297415 : Nat := 4983230072969 + 3 ^ 40 * 7297415 * 2
def baseEnd_7297415 : Nat := 3747081430329671563952305

theorem tailTrace_7297415 : CollatzResearch.WordTrace tailWord_7297415 prefixEnd_7297415 3747081430329671563952305 := by
  unfold tailWord_7297415
  simp only [CollatzResearch.WordTrace]
  refine ⟨266158590857719229104157699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177439060571812819402771799 266158590857719229104157699)
  ·
    refine ⟨399237886286578843656236549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266158590857719229104157699 399237886286578843656236549)
    ·
      refine ⟨74857103678733533185544353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399237886286578843656236549 74857103678733533185544353)
      ·
        refine ⟨56142827759050149889158265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74857103678733533185544353 56142827759050149889158265)
        ·
          refine ⟨42107120819287612416868699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56142827759050149889158265 42107120819287612416868699)
          ·
            refine ⟨63160681228931418625303049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42107120819287612416868699 63160681228931418625303049)
            ·
              refine ⟨47370510921698563968977287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63160681228931418625303049 47370510921698563968977287)
              ·
                refine ⟨71055766382547845953465931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47370510921698563968977287 71055766382547845953465931)
                ·
                  refine ⟨106583649573821768930198897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71055766382547845953465931 106583649573821768930198897)
                  ·
                    refine ⟨79937737180366326697649173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106583649573821768930198897 79937737180366326697649173)
                    ·
                      refine ⟨3747081430329671563952305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79937737180366326697649173 3747081430329671563952305)
                      ·
                        rfl

theorem cell23_7297415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_7297415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297415 prefixEnd_7297415 := by exact prefixLift 7297415
  have htrace : WordTrace (prefixWord ++ tailWord_7297415) baseStart_7297415 baseEnd_7297415 := by
    simpa [prefixWord, tailWord_7297415, baseEnd_7297415] using wordTrace_append hprefix tailTrace_7297415
  have hstable : (prefixWord ++ tailWord_7297415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297415).length < 2 ^ (prefixWord ++ tailWord_7297415).sum := by decide
  have hdescent : baseEnd_7297415 < baseStart_7297415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297439 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7297439 : Nat := 118140960795 + 7297439 * 2 ^ 59
def prefixEnd_7297439 : Nat := 4983230072969 + 3 ^ 40 * 7297439 * 2
def baseEnd_7297439 : Nat := 3747093753865379470052195

theorem tailTrace_7297439 : CollatzResearch.WordTrace tailWord_7297439 prefixEnd_7297439 3747093753865379470052195 := by
  unfold tailWord_7297439
  simp only [CollatzResearch.WordTrace]
  refine ⟨266159466209632281203031371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177439644139754854135354247 266159466209632281203031371)
  ·
    refine ⟨399239199314448421804547057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266159466209632281203031371 399239199314448421804547057)
    ·
      refine ⟨299429399485836316353410293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399239199314448421804547057 299429399485836316353410293)
      ·
        refine ⟨28071506201797154658132215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299429399485836316353410293 28071506201797154658132215)
        ·
          refine ⟨42107259302695731987198323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28071506201797154658132215 42107259302695731987198323)
          ·
            refine ⟨63160888954043597980797485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42107259302695731987198323 63160888954043597980797485)
            ·
              refine ⟨23685333357766349242799057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63160888954043597980797485 23685333357766349242799057)
              ·
                refine ⟨17764000018324761932099293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23685333357766349242799057 17764000018324761932099293)
                ·
                  refine ⟨6661500006871785724537235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17764000018324761932099293 6661500006871785724537235)
                  ·
                    refine ⟨9992250010307678586805853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661500006871785724537235 9992250010307678586805853)
                    ·
                      refine ⟨3747093753865379470052195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992250010307678586805853 3747093753865379470052195)
                      ·
                        rfl

theorem cell23_7297439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7297439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297439 prefixEnd_7297439 := by exact prefixLift 7297439
  have htrace : WordTrace (prefixWord ++ tailWord_7297439) baseStart_7297439 baseEnd_7297439 := by
    simpa [prefixWord, tailWord_7297439, baseEnd_7297439] using wordTrace_append hprefix tailTrace_7297439
  have hstable : (prefixWord ++ tailWord_7297439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297439).length < 2 ^ (prefixWord ++ tailWord_7297439).sum := by decide
  have hdescent : baseEnd_7297439 < baseStart_7297439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297442 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7297442 : Nat := 118140960795 + 7297442 * 2 ^ 59
def prefixEnd_7297442 : Nat := 4983230072969 + 3 ^ 40 * 7297442 * 2
def baseEnd_7297442 : Nat := 1249031764769114319438227

theorem tailTrace_7297442 : CollatzResearch.WordTrace tailWord_7297442 prefixEnd_7297442 1249031764769114319438227 := by
  unfold tailWord_7297442
  simp only [CollatzResearch.WordTrace]
  refine ⟨66539893907155353178847645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177439717085747608476927053 66539893907155353178847645)
  ·
    refine ⟨24952460215183257442067867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66539893907155353178847645 24952460215183257442067867)
    ·
      refine ⟨37428690322774886163101801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24952460215183257442067867 37428690322774886163101801)
      ·
        refine ⟨28071517742081164622326351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37428690322774886163101801 28071517742081164622326351)
        ·
          refine ⟨42107276613121746933489527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28071517742081164622326351 42107276613121746933489527)
          ·
            refine ⟨63160914919682620400234291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42107276613121746933489527 63160914919682620400234291)
            ·
              refine ⟨94741372379523930600351437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63160914919682620400234291 94741372379523930600351437)
              ·
                refine ⟨35528014642321473975131789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94741372379523930600351437 35528014642321473975131789)
                ·
                  refine ⟨13323005490870552740674421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35528014642321473975131789 13323005490870552740674421)
                  ·
                    refine ⟨1249031764769114319438227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13323005490870552740674421 1249031764769114319438227)
                    ·
                      rfl

theorem cell23_7297442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7297442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297442 prefixEnd_7297442 := by exact prefixLift 7297442
  have htrace : WordTrace (prefixWord ++ tailWord_7297442) baseStart_7297442 baseEnd_7297442 := by
    simpa [prefixWord, tailWord_7297442, baseEnd_7297442] using wordTrace_append hprefix tailTrace_7297442
  have hstable : (prefixWord ++ tailWord_7297442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297442).length < 2 ^ (prefixWord ++ tailWord_7297442).sum := by decide
  have hdescent : baseEnd_7297442 < baseStart_7297442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297475 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6]
def baseStart_7297475 : Nat := 118140960795 + 7297475 * 2 ^ 59
def prefixEnd_7297475 : Nat := 4983230072969 + 3 ^ 40 * 7297475 * 2
def baseEnd_7297475 : Nat := 3747112239168941329202029

theorem tailTrace_7297475 : CollatzResearch.WordTrace tailWord_7297475 prefixEnd_7297475 3747112239168941329202029 := by
  unfold tailWord_7297475
  simp only [CollatzResearch.WordTrace]
  refine ⟨266160779237501859351341879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177440519491667906234227919 266160779237501859351341879)
  ·
    refine ⟨399241168856252789027012819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266160779237501859351341879 399241168856252789027012819)
    ·
      refine ⟨598861753284379183540519229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399241168856252789027012819 598861753284379183540519229)
      ·
        refine ⟨224573157481642193827694711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598861753284379183540519229 224573157481642193827694711)
        ·
          refine ⟨336859736222463290741542067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224573157481642193827694711 336859736222463290741542067)
          ·
            refine ⟨505289604333694936112313101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336859736222463290741542067 505289604333694936112313101)
            ·
              refine ⟨189483601625135601042117413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505289604333694936112313101 189483601625135601042117413)
              ·
                refine ⟨35528175304712925195397015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189483601625135601042117413 35528175304712925195397015)
                ·
                  refine ⟨53292262957069387793095523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35528175304712925195397015 53292262957069387793095523)
                  ·
                    refine ⟨79938394435604081689643285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53292262957069387793095523 79938394435604081689643285)
                    ·
                      refine ⟨3747112239168941329202029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79938394435604081689643285 3747112239168941329202029)
                      ·
                        rfl

theorem cell23_7297475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_7297475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297475 prefixEnd_7297475 := by exact prefixLift 7297475
  have htrace : WordTrace (prefixWord ++ tailWord_7297475) baseStart_7297475 baseEnd_7297475 := by
    simpa [prefixWord, tailWord_7297475, baseEnd_7297475] using wordTrace_append hprefix tailTrace_7297475
  have hstable : (prefixWord ++ tailWord_7297475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297475).length < 2 ^ (prefixWord ++ tailWord_7297475).sum := by decide
  have hdescent : baseEnd_7297475 < baseStart_7297475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297482 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_7297482 : Nat := 118140960795 + 7297482 * 2 ^ 59
def prefixEnd_7297482 : Nat := 4983230072969 + 3 ^ 40 * 7297482 * 2
def baseEnd_7297482 : Nat := 3747115833533522801814497

theorem tailTrace_7297482 : CollatzResearch.WordTrace tailWord_7297482 prefixEnd_7297482 3747115833533522801814497 := by
  unfold tailWord_7297482
  simp only [CollatzResearch.WordTrace]
  refine ⟨66540258637119124886711675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177440689698984333031231133 66540258637119124886711675)
  ·
    refine ⟨99810387955678687330067513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66540258637119124886711675 99810387955678687330067513)
    ·
      refine ⟨74857790966759015497550635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99810387955678687330067513 74857790966759015497550635)
      ·
        refine ⟨112286686450138523246325953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74857790966759015497550635 112286686450138523246325953)
        ·
          refine ⟨84215014837603892434744465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112286686450138523246325953 84215014837603892434744465)
          ·
            refine ⟨63161261128202919326058349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84215014837603892434744465 63161261128202919326058349)
            ·
              refine ⟨23685472923076094747271881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63161261128202919326058349 23685472923076094747271881)
              ·
                refine ⟨17764104692307071060453911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23685472923076094747271881 17764104692307071060453911)
                ·
                  refine ⟨26646157038460606590680867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17764104692307071060453911 26646157038460606590680867)
                  ·
                    refine ⟨39969235557690909886021301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26646157038460606590680867 39969235557690909886021301)
                    ·
                      refine ⟨3747115833533522801814497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39969235557690909886021301 3747115833533522801814497)
                      ·
                        rfl

theorem cell23_7297482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_7297482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297482 prefixEnd_7297482 := by exact prefixLift 7297482
  have htrace : WordTrace (prefixWord ++ tailWord_7297482) baseStart_7297482 baseEnd_7297482 := by
    simpa [prefixWord, tailWord_7297482, baseEnd_7297482] using wordTrace_append hprefix tailTrace_7297482
  have hstable : (prefixWord ++ tailWord_7297482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297482).length < 2 ^ (prefixWord ++ tailWord_7297482).sum := by decide
  have hdescent : baseEnd_7297482 < baseStart_7297482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297529 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 3]
def baseStart_7297529 : Nat := 118140960795 + 7297529 * 2 ^ 59
def prefixEnd_7297529 : Nat := 4983230072969 + 3 ^ 40 * 7297529 * 2
def baseEnd_7297529 : Nat := 3747139967124284117926781

theorem tailTrace_7297529 : CollatzResearch.WordTrace tailWord_7297529 prefixEnd_7297529 3747139967124284117926781 := by
  unfold tailWord_7297529
  simp only [CollatzResearch.WordTrace]
  refine ⟨266162748779306226573807641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177441832519537484382538427 266162748779306226573807641)
  ·
    refine ⟨199622061584479669930355731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266162748779306226573807641 199622061584479669930355731)
    ·
      refine ⟨299433092376719504895533597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199622061584479669930355731 299433092376719504895533597)
      ·
        refine ⟨112287409641269814335825099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299433092376719504895533597 112287409641269814335825099)
        ·
          refine ⟨168431114461904721503737649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112287409641269814335825099 168431114461904721503737649)
          ·
            refine ⟨126323335846428541127803237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168431114461904721503737649 126323335846428541127803237)
            ·
              refine ⟨23685625471205351461463107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126323335846428541127803237 23685625471205351461463107)
              ·
                refine ⟨35528438206808027192194661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23685625471205351461463107 35528438206808027192194661)
                ·
                  refine ⟨6661582163776505098536499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35528438206808027192194661 6661582163776505098536499)
                  ·
                    refine ⟨9992373245664757647804749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661582163776505098536499 9992373245664757647804749)
                    ·
                      refine ⟨3747139967124284117926781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992373245664757647804749 3747139967124284117926781)
                      ·
                        rfl

theorem cell23_7297529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_7297529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297529 prefixEnd_7297529 := by exact prefixLift 7297529
  have htrace : WordTrace (prefixWord ++ tailWord_7297529) baseStart_7297529 baseEnd_7297529 := by
    simpa [prefixWord, tailWord_7297529, baseEnd_7297529] using wordTrace_append hprefix tailTrace_7297529
  have hstable : (prefixWord ++ tailWord_7297529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297529).length < 2 ^ (prefixWord ++ tailWord_7297529).sum := by decide
  have hdescent : baseEnd_7297529 < baseStart_7297529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297539 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 3, 3, 2]
def baseStart_7297539 : Nat := 118140960795 + 7297539 * 2 ^ 59
def prefixEnd_7297539 : Nat := 4983230072969 + 3 ^ 40 * 7297539 * 2
def baseEnd_7297539 : Nat := 3747145101930829078801735

theorem tailTrace_7297539 : CollatzResearch.WordTrace tailWord_7297539 prefixEnd_7297539 3747145101930829078801735 := by
  unfold tailWord_7297539
  simp only [CollatzResearch.WordTrace]
  refine ⟨266163113509269998281671671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177442075672846665521114447 266163113509269998281671671)
  ·
    refine ⟨399244670263904997422507507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266163113509269998281671671 399244670263904997422507507)
    ·
      refine ⟨598867005395857496133761261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399244670263904997422507507 598867005395857496133761261)
      ·
        refine ⟨224575127023446561050160473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598867005395857496133761261 224575127023446561050160473)
        ·
          refine ⟨168431345267584920787620355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224575127023446561050160473 168431345267584920787620355)
          ·
            refine ⟨252647017901377381181430533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168431345267584920787620355 252647017901377381181430533)
            ·
              refine ⟨47371315856508258971518225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252647017901377381181430533 47371315856508258971518225)
              ·
                refine ⟨35528486892381194228638669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47371315856508258971518225 35528486892381194228638669)
                ·
                  refine ⟨13323182584642947835739501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35528486892381194228638669 13323182584642947835739501)
                  ·
                    refine ⟨4996193469241105438402313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13323182584642947835739501 4996193469241105438402313)
                    ·
                      refine ⟨3747145101930829078801735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996193469241105438402313 3747145101930829078801735)
                      ·
                        rfl

theorem cell23_7297539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_7297539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297539 prefixEnd_7297539 := by exact prefixLift 7297539
  have htrace : WordTrace (prefixWord ++ tailWord_7297539) baseStart_7297539 baseEnd_7297539 := by
    simpa [prefixWord, tailWord_7297539, baseEnd_7297539] using wordTrace_append hprefix tailTrace_7297539
  have hstable : (prefixWord ++ tailWord_7297539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297539).length < 2 ^ (prefixWord ++ tailWord_7297539).sum := by decide
  have hdescent : baseEnd_7297539 < baseStart_7297539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297546 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_7297546 : Nat := 118140960795 + 7297546 * 2 ^ 59
def prefixEnd_7297546 : Nat := 4983230072969 + 3 ^ 40 * 7297546 * 2
def baseEnd_7297546 : Nat := 3747148696295410551414203

theorem tailTrace_7297546 : CollatzResearch.WordTrace tailWord_7297546 prefixEnd_7297546 3747148696295410551414203 := by
  unfold tailWord_7297546
  simp only [CollatzResearch.WordTrace]
  refine ⟨66540842205061159619294123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177442245880163092318117661 66540842205061159619294123)
  ·
    refine ⟨99811263307591739428941185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66540842205061159619294123 99811263307591739428941185)
    ·
      refine ⟨74858447480693804571705889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99811263307591739428941185 74858447480693804571705889)
      ·
        refine ⟨56143835610520353428779417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74858447480693804571705889 56143835610520353428779417)
        ·
          refine ⟨42107876707890265071584563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56143835610520353428779417 42107876707890265071584563)
          ·
            refine ⟨63161815061835397607376845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42107876707890265071584563 63161815061835397607376845)
            ·
              refine ⟨23685680648188274102766317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63161815061835397607376845 23685680648188274102766317)
              ·
                refine ⟨8882130243070602788537369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23685680648188274102766317 8882130243070602788537369)
                ·
                  refine ⟨6661597682302952091403027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882130243070602788537369 6661597682302952091403027)
                  ·
                    refine ⟨9992396523454428137104541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661597682302952091403027 9992396523454428137104541)
                    ·
                      refine ⟨3747148696295410551414203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992396523454428137104541 3747148696295410551414203)
                      ·
                        rfl

theorem cell23_7297546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_7297546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297546 prefixEnd_7297546 := by exact prefixLift 7297546
  have htrace : WordTrace (prefixWord ++ tailWord_7297546) baseStart_7297546 baseEnd_7297546 := by
    simpa [prefixWord, tailWord_7297546, baseEnd_7297546] using wordTrace_append hprefix tailTrace_7297546
  have hstable : (prefixWord ++ tailWord_7297546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297546).length < 2 ^ (prefixWord ++ tailWord_7297546).sum := by decide
  have hdescent : baseEnd_7297546 < baseStart_7297546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297586 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_7297586 : Nat := 118140960795 + 7297586 * 2 ^ 59
def prefixEnd_7297586 : Nat := 4983230072969 + 3 ^ 40 * 7297586 * 2
def baseEnd_7297586 : Nat := 3747169235521590394914019

theorem tailTrace_7297586 : CollatzResearch.WordTrace tailWord_7297586 prefixEnd_7297586 3747169235521590394914019 := by
  unfold tailWord_7297586
  simp only [CollatzResearch.WordTrace]
  refine ⟨66541206935024931327158153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177443218493399816872421741 66541206935024931327158153)
  ·
    refine ⟨49905905201268698495368615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66541206935024931327158153 49905905201268698495368615)
    ·
      refine ⟨74858857801903047743052923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49905905201268698495368615 74858857801903047743052923)
      ·
        refine ⟨112288286702854571614579385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74858857801903047743052923 112288286702854571614579385)
        ·
          refine ⟨84216215027140928710934539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112288286702854571614579385 84216215027140928710934539)
          ·
            refine ⟨126324322540711393066401809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84216215027140928710934539 126324322540711393066401809)
            ·
              refine ⟨94743241905533544799801357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126324322540711393066401809 94743241905533544799801357)
              ·
                refine ⟨35528715714575079299925509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94743241905533544799801357 35528715714575079299925509)
                ·
                  refine ⟨6661634196482827368736033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35528715714575079299925509 6661634196482827368736033)
                  ·
                    refine ⟨4996225647362120526552025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6661634196482827368736033 4996225647362120526552025)
                    ·
                      refine ⟨3747169235521590394914019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996225647362120526552025 3747169235521590394914019)
                      ·
                        rfl

theorem cell23_7297586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_7297586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297586 prefixEnd_7297586 := by exact prefixLift 7297586
  have htrace : WordTrace (prefixWord ++ tailWord_7297586) baseStart_7297586 baseEnd_7297586 := by
    simpa [prefixWord, tailWord_7297586, baseEnd_7297586] using wordTrace_append hprefix tailTrace_7297586
  have hstable : (prefixWord ++ tailWord_7297586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297586).length < 2 ^ (prefixWord ++ tailWord_7297586).sum := by decide
  have hdescent : baseEnd_7297586 < baseStart_7297586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297592 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 7]
def baseStart_7297592 : Nat := 118140960795 + 7297592 * 2 ^ 59
def prefixEnd_7297592 : Nat := 4983230072969 + 3 ^ 40 * 7297592 * 2
def baseEnd_7297592 : Nat := 416352479600613041270999

theorem tailTrace_7297592 : CollatzResearch.WordTrace tailWord_7297592 prefixEnd_7297592 416352479600613041270999 := by
  unfold tailWord_7297592
  simp only [CollatzResearch.WordTrace]
  refine ⟨133082523289038994166675515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177443364385385325555567353 133082523289038994166675515)
  ·
    refine ⟨199623784933558491250013273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133082523289038994166675515 199623784933558491250013273)
    ·
      refine ⟨149717838700168868437509955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199623784933558491250013273 149717838700168868437509955)
      ·
        refine ⟨224576758050253302656264933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149717838700168868437509955 224576758050253302656264933)
        ·
          refine ⟨42108142134422494248049675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224576758050253302656264933 42108142134422494248049675)
          ·
            refine ⟨63162213201633741372074513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42108142134422494248049675 63162213201633741372074513)
            ·
              refine ⟨47371659901225306029055885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63162213201633741372074513 47371659901225306029055885)
              ·
                refine ⟨17764372462959489760895957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47371659901225306029055885 17764372462959489760895957)
                ·
                  refine ⟨416352479600613041270999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17764372462959489760895957 416352479600613041270999)
                  ·
                    rfl

theorem cell23_7297592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_7297592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297592 prefixEnd_7297592 := by exact prefixLift 7297592
  have htrace : WordTrace (prefixWord ++ tailWord_7297592) baseStart_7297592 baseEnd_7297592 := by
    simpa [prefixWord, tailWord_7297592, baseEnd_7297592] using wordTrace_append hprefix tailTrace_7297592
  have hstable : (prefixWord ++ tailWord_7297592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297592).length < 2 ^ (prefixWord ++ tailWord_7297592).sum := by decide
  have hdescent : baseEnd_7297592 < baseStart_7297592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297632 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_7297632 : Nat := 118140960795 + 7297632 * 2 ^ 59
def prefixEnd_7297632 : Nat := 4983230072969 + 3 ^ 40 * 7297632 * 2
def baseEnd_7297632 : Nat := 3747192855631697214938807

theorem tailTrace_7297632 : CollatzResearch.WordTrace tailWord_7297632 prefixEnd_7297632 3747192855631697214938807 := by
  unfold tailWord_7297632
  simp only [CollatzResearch.WordTrace]
  refine ⟨133083252748966537582403575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177444336998622050109871433 133083252748966537582403575)
  ·
    refine ⟨199624879123449806373605363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133083252748966537582403575 199624879123449806373605363)
    ·
      refine ⟨299437318685174709560408045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199624879123449806373605363 299437318685174709560408045)
      ·
        refine ⟨112288994506940516085153017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299437318685174709560408045 112288994506940516085153017)
        ·
          refine ⟨84216745880205387063864763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112288994506940516085153017 84216745880205387063864763)
          ·
            refine ⟨126325118820308080595797145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84216745880205387063864763 126325118820308080595797145)
            ·
              refine ⟨94743839115231060446847859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126325118820308080595797145 94743839115231060446847859)
              ·
                refine ⟨142115758672846590670271789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94743839115231060446847859 142115758672846590670271789)
                ·
                  refine ⟨53293409502317471501351921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142115758672846590670271789 53293409502317471501351921)
                  ·
                    refine ⟨39970057126738103626013941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53293409502317471501351921 39970057126738103626013941)
                    ·
                      refine ⟨3747192855631697214938807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39970057126738103626013941 3747192855631697214938807)
                      ·
                        rfl

theorem cell23_7297632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_7297632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297632 prefixEnd_7297632 := by exact prefixLift 7297632
  have htrace : WordTrace (prefixWord ++ tailWord_7297632) baseStart_7297632 baseEnd_7297632 := by
    simpa [prefixWord, tailWord_7297632, baseEnd_7297632] using wordTrace_append hprefix tailTrace_7297632
  have hstable : (prefixWord ++ tailWord_7297632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297632).length < 2 ^ (prefixWord ++ tailWord_7297632).sum := by decide
  have hdescent : baseEnd_7297632 < baseStart_7297632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297637 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 2, 2, 2]
def baseStart_7297637 : Nat := 118140960795 + 7297637 * 2 ^ 59
def prefixEnd_7297637 : Nat := 4983230072969 + 3 ^ 40 * 7297637 * 2
def baseEnd_7297637 : Nat := 3747195423034969695376285

theorem tailTrace_7297637 : CollatzResearch.WordTrace tailWord_7297637 prefixEnd_7297637 3747195423034969695376285 := by
  unfold tailWord_7297637
  simp only [CollatzResearch.WordTrace]
  refine ⟨266166687862914961018739165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177444458575276640679159443 266166687862914961018739165)
  ·
    refine ⟨99812507948593110382027187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266166687862914961018739165 99812507948593110382027187)
    ·
      refine ⟨149718761922889665573040781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99812507948593110382027187 149718761922889665573040781)
      ·
        refine ⟨56144535721083624589890293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149718761922889665573040781 56144535721083624589890293)
        ·
          refine ⟨5263550223851589805302215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56144535721083624589890293 5263550223851589805302215)
          ·
            refine ⟨7895325335777384707953323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263550223851589805302215 7895325335777384707953323)
            ·
              refine ⟨11842988003666077061929985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895325335777384707953323 11842988003666077061929985)
              ·
                refine ⟨8882241002749557796447489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11842988003666077061929985 8882241002749557796447489)
                ·
                  refine ⟨6661680752062168347335617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882241002749557796447489 6661680752062168347335617)
                  ·
                    refine ⟨4996260564046626260501713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6661680752062168347335617 4996260564046626260501713)
                    ·
                      refine ⟨3747195423034969695376285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996260564046626260501713 3747195423034969695376285)
                      ·
                        rfl

theorem cell23_7297637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_7297637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297637 prefixEnd_7297637 := by exact prefixLift 7297637
  have htrace : WordTrace (prefixWord ++ tailWord_7297637) baseStart_7297637 baseEnd_7297637 := by
    simpa [prefixWord, tailWord_7297637, baseEnd_7297637] using wordTrace_append hprefix tailTrace_7297637
  have hstable : (prefixWord ++ tailWord_7297637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297637).length < 2 ^ (prefixWord ++ tailWord_7297637).sum := by decide
  have hdescent : baseEnd_7297637 < baseStart_7297637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297659 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 6, 2]
def baseStart_7297659 : Nat := 118140960795 + 7297659 * 2 ^ 59
def prefixEnd_7297659 : Nat := 4983230072969 + 3 ^ 40 * 7297659 * 2
def baseEnd_7297659 : Nat := 3747206719609368609301183

theorem tailTrace_7297659 : CollatzResearch.WordTrace tailWord_7297659 prefixEnd_7297659 3747206719609368609301183 := by
  unfold tailWord_7297659
  simp only [CollatzResearch.WordTrace]
  refine ⟨266167490268835258776040031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177444993512556839184026687 266167490268835258776040031)
  ·
    refine ⟨399251235403252888164060047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266167490268835258776040031 399251235403252888164060047)
    ·
      refine ⟨598876853104879332246090071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399251235403252888164060047 598876853104879332246090071)
      ·
        refine ⟨898315279657318998369135107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598876853104879332246090071 898315279657318998369135107)
        ·
          refine ⟨1347472919485978497553702661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898315279657318998369135107 1347472919485978497553702661)
          ·
            refine ⟨252651172403620968291319249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1347472919485978497553702661 252651172403620968291319249)
            ·
              refine ⟨189488379302715726218489437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252651172403620968291319249 189488379302715726218489437)
              ·
                refine ⟨71058142238518397331933539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189488379302715726218489437 71058142238518397331933539)
                ·
                  refine ⟨106587213357777595997900309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71058142238518397331933539 106587213357777595997900309)
                  ·
                    refine ⟨4996275626145824812401577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106587213357777595997900309 4996275626145824812401577)
                    ·
                      refine ⟨3747206719609368609301183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996275626145824812401577 3747206719609368609301183)
                      ·
                        rfl

theorem cell23_7297659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6, 2].length) (baseStart_7297659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297659 prefixEnd_7297659 := by exact prefixLift 7297659
  have htrace : WordTrace (prefixWord ++ tailWord_7297659) baseStart_7297659 baseEnd_7297659 := by
    simpa [prefixWord, tailWord_7297659, baseEnd_7297659] using wordTrace_append hprefix tailTrace_7297659
  have hstable : (prefixWord ++ tailWord_7297659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297659).length < 2 ^ (prefixWord ++ tailWord_7297659).sum := by decide
  have hdescent : baseEnd_7297659 < baseStart_7297659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297712 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_7297712 : Nat := 118140960795 + 7297712 * 2 ^ 59
def prefixEnd_7297712 : Nat := 4983230072969 + 3 ^ 40 * 7297712 * 2
def baseEnd_7297712 : Nat := 1249077978028018967312813

theorem tailTrace_7297712 : CollatzResearch.WordTrace tailWord_7297712 prefixEnd_7297712 1249077978028018967312813 := by
  unfold tailWord_7297712
  simp only [CollatzResearch.WordTrace]
  refine ⟨133084711668821624413859695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177446282225095499218479593 133084711668821624413859695)
  ·
    refine ⟨199627067503232436620789543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133084711668821624413859695 199627067503232436620789543)
    ·
      refine ⟨299440601254848654931184315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199627067503232436620789543 299440601254848654931184315)
      ·
        refine ⟨449160901882272982396776473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299440601254848654931184315 449160901882272982396776473)
        ·
          refine ⟨336870676411704736797582355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449160901882272982396776473 336870676411704736797582355)
          ·
            refine ⟨505306014617557105196373533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336870676411704736797582355 505306014617557105196373533)
            ·
              refine ⟨189489755481583914448640075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505306014617557105196373533 189489755481583914448640075)
              ·
                refine ⟨284234633222375871672960113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189489755481583914448640075 284234633222375871672960113)
                ·
                  refine ⟨213175974916781903754720085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284234633222375871672960113 213175974916781903754720085)
                  ·
                    refine ⟨1249077978028018967312813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 213175974916781903754720085 1249077978028018967312813)
                    ·
                      rfl

theorem cell23_7297712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_7297712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297712 prefixEnd_7297712 := by exact prefixLift 7297712
  have htrace : WordTrace (prefixWord ++ tailWord_7297712) baseStart_7297712 baseEnd_7297712 := by
    simpa [prefixWord, tailWord_7297712, baseEnd_7297712] using wordTrace_append hprefix tailTrace_7297712
  have hstable : (prefixWord ++ tailWord_7297712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297712).length < 2 ^ (prefixWord ++ tailWord_7297712).sum := by decide
  have hdescent : baseEnd_7297712 < baseStart_7297712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297769 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_7297769 : Nat := 118140960795 + 7297769 * 2 ^ 59
def prefixEnd_7297769 : Nat := 4983230072969 + 3 ^ 40 * 7297769 * 2
def baseEnd_7297769 : Nat := 3747263202481363178925677

theorem tailTrace_7297769 : CollatzResearch.WordTrace tailWord_7297769 prefixEnd_7297769 3747263202481363178925677 := by
  unfold tailWord_7297769
  simp only [CollatzResearch.WordTrace]
  refine ⟨266171502298436747562544361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177447668198957831708362907 266171502298436747562544361)
  ·
    refine ⟨199628626723827560671908271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266171502298436747562544361 199628626723827560671908271)
    ·
      refine ⟨299442940085741341007862407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199628626723827560671908271 299442940085741341007862407)
      ·
        refine ⟨449164410128612011511793611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299442940085741341007862407 449164410128612011511793611)
        ·
          refine ⟨673746615192918017267690417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449164410128612011511793611 673746615192918017267690417)
          ·
            refine ⟨505309961394688512950767813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673746615192918017267690417 505309961394688512950767813)
            ·
              refine ⟨94745617761504096178268965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 505309961394688512950767813 94745617761504096178268965)
              ·
                refine ⟨17764803330282018033425431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94745617761504096178268965 17764803330282018033425431)
                ·
                  refine ⟨26647204995423027050138147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17764803330282018033425431 26647204995423027050138147)
                  ·
                    refine ⟨39970807493134540575207221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26647204995423027050138147 39970807493134540575207221)
                    ·
                      refine ⟨3747263202481363178925677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39970807493134540575207221 3747263202481363178925677)
                      ·
                        rfl

theorem cell23_7297769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_7297769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297769 prefixEnd_7297769 := by exact prefixLift 7297769
  have htrace : WordTrace (prefixWord ++ tailWord_7297769) baseStart_7297769 baseEnd_7297769 := by
    simpa [prefixWord, tailWord_7297769, baseEnd_7297769] using wordTrace_append hprefix tailTrace_7297769
  have hstable : (prefixWord ++ tailWord_7297769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297769).length < 2 ^ (prefixWord ++ tailWord_7297769).sum := by decide
  have hdescent : baseEnd_7297769 < baseStart_7297769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297776 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 2, 4]
def baseStart_7297776 : Nat := 118140960795 + 7297776 * 2 ^ 59
def prefixEnd_7297776 : Nat := 4983230072969 + 3 ^ 40 * 7297776 * 2
def baseEnd_7297776 : Nat := 1249088932281981550512715

theorem tailTrace_7297776 : CollatzResearch.WordTrace tailWord_7297776 prefixEnd_7297776 1249088932281981550512715 := by
  unfold tailWord_7297776
  simp only [CollatzResearch.WordTrace]
  refine ⟨133085878804705693879024591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177447838406274258505366121 133085878804705693879024591)
  ·
    refine ⟨199628818207058540818536887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133085878804705693879024591 199628818207058540818536887)
    ·
      refine ⟨299443227310587811227805331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199628818207058540818536887 299443227310587811227805331)
      ·
        refine ⟨449164840965881716841707997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299443227310587811227805331 449164840965881716841707997)
        ·
          refine ⟨168436815362205643815640499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449164840965881716841707997 168436815362205643815640499)
          ·
            refine ⟨252655223043308465723460749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168436815362205643815640499 252655223043308465723460749)
            ·
              refine ⟨94745708641240674646297781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252655223043308465723460749 94745708641240674646297781)
              ·
                refine ⟨8882410185116313248090417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94745708641240674646297781 8882410185116313248090417)
                ·
                  refine ⟨6661807638837234936067813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882410185116313248090417 6661807638837234936067813)
                  ·
                    refine ⟨1249088932281981550512715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661807638837234936067813 1249088932281981550512715)
                    ·
                      rfl

theorem cell23_7297776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_7297776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297776 prefixEnd_7297776 := by exact prefixLift 7297776
  have htrace : WordTrace (prefixWord ++ tailWord_7297776) baseStart_7297776 baseEnd_7297776 := by
    simpa [prefixWord, tailWord_7297776, baseEnd_7297776] using wordTrace_append hprefix tailTrace_7297776
  have hstable : (prefixWord ++ tailWord_7297776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297776).length < 2 ^ (prefixWord ++ tailWord_7297776).sum := by decide
  have hdescent : baseEnd_7297776 < baseStart_7297776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297786 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_7297786 : Nat := 118140960795 + 7297786 * 2 ^ 59
def prefixEnd_7297786 : Nat := 4983230072969 + 3 ^ 40 * 7297786 * 2
def baseEnd_7297786 : Nat := 3747271931652489612413099

theorem tailTrace_7297786 : CollatzResearch.WordTrace tailWord_7297786 prefixEnd_7297786 3747271931652489612413099 := by
  unfold tailWord_7297786
  simp only [CollatzResearch.WordTrace]
  refine ⟨66543030584843789866478303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177448081559583439643942141 66543030584843789866478303)
  ·
    refine ⟨99814545877265684799717455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66543030584843789866478303 99814545877265684799717455)
    ·
      refine ⟨149721818815898527199576183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99814545877265684799717455 149721818815898527199576183)
      ·
        refine ⟨224582728223847790799364275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149721818815898527199576183 224582728223847790799364275)
        ·
          refine ⟨336874092335771686199046413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224582728223847790799364275 336874092335771686199046413)
          ·
            refine ⟨126327784625914382324642405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336874092335771686199046413 126327784625914382324642405)
            ·
              refine ⟨23686459617358946685870451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126327784625914382324642405 23686459617358946685870451)
              ·
                refine ⟨35529689426038420028805677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23686459617358946685870451 35529689426038420028805677)
                ·
                  refine ⟨13323633534764407510802129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35529689426038420028805677 13323633534764407510802129)
                  ·
                    refine ⟨9992725151073305633101597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13323633534764407510802129 9992725151073305633101597)
                    ·
                      refine ⟨3747271931652489612413099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992725151073305633101597 3747271931652489612413099)
                      ·
                        rfl

theorem cell23_7297786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_7297786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297786 prefixEnd_7297786 := by exact prefixLift 7297786
  have htrace : WordTrace (prefixWord ++ tailWord_7297786) baseStart_7297786 baseEnd_7297786 := by
    simpa [prefixWord, tailWord_7297786, baseEnd_7297786] using wordTrace_append hprefix tailTrace_7297786
  have hstable : (prefixWord ++ tailWord_7297786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297786).length < 2 ^ (prefixWord ++ tailWord_7297786).sum := by decide
  have hdescent : baseEnd_7297786 < baseStart_7297786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297796 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7297796 : Nat := 118140960795 + 7297796 * 2 ^ 59
def prefixEnd_7297796 : Nat := 4983230072969 + 3 ^ 40 * 7297796 * 2
def baseEnd_7297796 : Nat := 3747277066459034573288053

theorem tailTrace_7297796 : CollatzResearch.WordTrace tailWord_7297796 prefixEnd_7297796 3747277066459034573288053 := by
  unfold tailWord_7297796
  simp only [CollatzResearch.WordTrace]
  refine ⟨133086243534669465586888621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177448324712892620782518161 133086243534669465586888621)
  ·
    refine ⟨49907341325501049595083233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133086243534669465586888621 49907341325501049595083233)
    ·
      refine ⟨37430505994125787196312425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49907341325501049595083233 37430505994125787196312425)
      ·
        refine ⟨28072879495594340397234319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37430505994125787196312425 28072879495594340397234319)
        ·
          refine ⟨42109319243391510595851479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28072879495594340397234319 42109319243391510595851479)
          ·
            refine ⟨63163978865087265893777219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42109319243391510595851479 63163978865087265893777219)
            ·
              refine ⟨94745968297630898840665829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63163978865087265893777219 94745968297630898840665829)
              ·
                refine ⟨17764869055805793532624843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94745968297630898840665829 17764869055805793532624843)
                ·
                  refine ⟨26647303583708690298937265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17764869055805793532624843 26647303583708690298937265)
                  ·
                    refine ⟨19985477687781517724202949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26647303583708690298937265 19985477687781517724202949)
                    ·
                      refine ⟨3747277066459034573288053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19985477687781517724202949 3747277066459034573288053)
                      ·
                        rfl

theorem cell23_7297796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7297796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297796 prefixEnd_7297796 := by exact prefixLift 7297796
  have htrace : WordTrace (prefixWord ++ tailWord_7297796) baseStart_7297796 baseEnd_7297796 := by
    simpa [prefixWord, tailWord_7297796, baseEnd_7297796] using wordTrace_append hprefix tailTrace_7297796
  have hstable : (prefixWord ++ tailWord_7297796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297796).length < 2 ^ (prefixWord ++ tailWord_7297796).sum := by decide
  have hdescent : baseEnd_7297796 < baseStart_7297796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297800 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_7297800 : Nat := 118140960795 + 7297800 * 2 ^ 59
def prefixEnd_7297800 : Nat := 4983230072969 + 3 ^ 40 * 7297800 * 2
def baseEnd_7297800 : Nat := 3747279120381652557638035

theorem tailTrace_7297800 : CollatzResearch.WordTrace tailWord_7297800 prefixEnd_7297800 3747279120381652557638035 := by
  unfold tailWord_7297800
  simp only [CollatzResearch.WordTrace]
  refine ⟨133086316480662219928461427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177448421974216293237948569 133086316480662219928461427)
  ·
    refine ⟨199629474720993329892692141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133086316480662219928461427 199629474720993329892692141)
    ·
      refine ⟨74861053020372498709759553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199629474720993329892692141 74861053020372498709759553)
      ·
        refine ⟨56145789765279374032319665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74861053020372498709759553 56145789765279374032319665)
        ·
          refine ⟨42109342323959530524239749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56145789765279374032319665 42109342323959530524239749)
          ·
            refine ⟨7895501685742411973294953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42109342323959530524239749 7895501685742411973294953)
            ·
              refine ⟨5921626264306808979971215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895501685742411973294953 5921626264306808979971215)
              ·
                refine ⟨8882439396460213469956823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921626264306808979971215 8882439396460213469956823)
                ·
                  refine ⟨13323659094690320204935235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8882439396460213469956823 13323659094690320204935235)
                  ·
                    refine ⟨19985488642035480307402853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13323659094690320204935235 19985488642035480307402853)
                    ·
                      refine ⟨3747279120381652557638035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19985488642035480307402853 3747279120381652557638035)
                      ·
                        rfl

theorem cell23_7297800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_7297800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297800 prefixEnd_7297800 := by exact prefixLift 7297800
  have htrace : WordTrace (prefixWord ++ tailWord_7297800) baseStart_7297800 baseEnd_7297800 := by
    simpa [prefixWord, tailWord_7297800, baseEnd_7297800] using wordTrace_append hprefix tailTrace_7297800
  have hstable : (prefixWord ++ tailWord_7297800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297800).length < 2 ^ (prefixWord ++ tailWord_7297800).sum := by decide
  have hdescent : baseEnd_7297800 < baseStart_7297800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297810 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7297810 : Nat := 118140960795 + 7297810 * 2 ^ 59
def prefixEnd_7297810 : Nat := 4983230072969 + 3 ^ 40 * 7297810 * 2
def baseEnd_7297810 : Nat := 1249094751729399172837663

theorem tailTrace_7297810 : CollatzResearch.WordTrace tailWord_7297810 prefixEnd_7297810 1249094751729399172837663 := by
  unfold tailWord_7297810
  simp only [CollatzResearch.WordTrace]
  refine ⟨66543249422822052891196721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177448665127525474376524589 66543249422822052891196721)
  ·
    refine ⟨49907437067116539668397541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66543249422822052891196721 49907437067116539668397541)
    ·
      refine ⟨9357644450084351187824539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49907437067116539668397541 9357644450084351187824539)
      ·
        refine ⟨14036466675126526781736809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9357644450084351187824539 14036466675126526781736809)
        ·
          refine ⟨10527350006344895086302607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14036466675126526781736809 10527350006344895086302607)
          ·
            refine ⟨15791025009517342629453911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10527350006344895086302607 15791025009517342629453911)
            ·
              refine ⟨23686537514276013944180867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15791025009517342629453911 23686537514276013944180867)
              ·
                refine ⟨35529806271414020916271301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23686537514276013944180867 35529806271414020916271301)
                ·
                  refine ⟨6661838675890128921800869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35529806271414020916271301 6661838675890128921800869)
                  ·
                    refine ⟨1249094751729399172837663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661838675890128921800869 1249094751729399172837663)
                    ·
                      rfl

theorem cell23_7297810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7297810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297810 prefixEnd_7297810 := by exact prefixLift 7297810
  have htrace : WordTrace (prefixWord ++ tailWord_7297810) baseStart_7297810 baseEnd_7297810 := by
    simpa [prefixWord, tailWord_7297810, baseEnd_7297810] using wordTrace_append hprefix tailTrace_7297810
  have hstable : (prefixWord ++ tailWord_7297810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297810).length < 2 ^ (prefixWord ++ tailWord_7297810).sum := by decide
  have hdescent : baseEnd_7297810 < baseStart_7297810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297884 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7297884 : Nat := 118140960795 + 7297884 * 2 ^ 59
def prefixEnd_7297884 : Nat := 4983230072969 + 3 ^ 40 * 7297884 * 2
def baseEnd_7297884 : Nat := 3747322252756630228987649

theorem tailTrace_7297884 : CollatzResearch.WordTrace tailWord_7297884 prefixEnd_7297884 3747322252756630228987649 := by
  unfold tailWord_7297884
  simp only [CollatzResearch.WordTrace]
  refine ⟨133087848346510061101490353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177450464462013414801987137 133087848346510061101490353)
  ·
    refine ⟨99815886259882545826117765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133087848346510061101490353 99815886259882545826117765)
    ·
      refine ⟨18715478673727977342397081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99815886259882545826117765 18715478673727977342397081)
      ·
        refine ⟨14036609005295983006797811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18715478673727977342397081 14036609005295983006797811)
        ·
          refine ⟨21054913507943974510196717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14036609005295983006797811 21054913507943974510196717)
          ·
            refine ⟨7895592565478990441323769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21054913507943974510196717 7895592565478990441323769)
            ·
              refine ⟨5921694424109242830992827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895592565478990441323769 5921694424109242830992827)
              ·
                refine ⟨8882541636163864246489241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921694424109242830992827 8882541636163864246489241)
                ·
                  refine ⟨6661906227122898184866931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882541636163864246489241 6661906227122898184866931)
                  ·
                    refine ⟨9992859340684347277300397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661906227122898184866931 9992859340684347277300397)
                    ·
                      refine ⟨3747322252756630228987649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9992859340684347277300397 3747322252756630228987649)
                      ·
                        rfl

theorem cell23_7297884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7297884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297884 prefixEnd_7297884 := by exact prefixLift 7297884
  have htrace : WordTrace (prefixWord ++ tailWord_7297884) baseStart_7297884 baseEnd_7297884 := by
    simpa [prefixWord, tailWord_7297884, baseEnd_7297884] using wordTrace_append hprefix tailTrace_7297884
  have hstable : (prefixWord ++ tailWord_7297884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297884).length < 2 ^ (prefixWord ++ tailWord_7297884).sum := by decide
  have hdescent : baseEnd_7297884 < baseStart_7297884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297930 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_7297930 : Nat := 118140960795 + 7297930 * 2 ^ 59
def prefixEnd_7297930 : Nat := 4983230072969 + 3 ^ 40 * 7297930 * 2
def baseEnd_7297930 : Nat := 416371763651859672112493

theorem tailTrace_7297930 : CollatzResearch.WordTrace tailWord_7297930 prefixEnd_7297930 416371763651859672112493 := by
  unfold tailWord_7297930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66544343612713368014788811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177451582967235648039436829 66544343612713368014788811)
  ·
    refine ⟨99816515419070052022183217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66544343612713368014788811 99816515419070052022183217)
    ·
      refine ⟨74862386564302539016637413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99816515419070052022183217 74862386564302539016637413)
      ·
        refine ⟨14036697480806726065619515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74862386564302539016637413 14036697480806726065619515)
        ·
          refine ⟨21055046221210089098429273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14036697480806726065619515 21055046221210089098429273)
          ·
            refine ⟨15791284665907566823821955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21055046221210089098429273 15791284665907566823821955)
            ·
              refine ⟨23686926998861350235732933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15791284665907566823821955 23686926998861350235732933)
              ·
                refine ⟨4441298812286503169199925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23686926998861350235732933 4441298812286503169199925)
                ·
                  refine ⟨416371763651859672112493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4441298812286503169199925 416371763651859672112493)
                  ·
                    rfl

theorem cell23_7297930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_7297930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297930 prefixEnd_7297930 := by exact prefixLift 7297930
  have htrace : WordTrace (prefixWord ++ tailWord_7297930) baseStart_7297930 baseEnd_7297930 := by
    simpa [prefixWord, tailWord_7297930, baseEnd_7297930] using wordTrace_append hprefix tailTrace_7297930
  have hstable : (prefixWord ++ tailWord_7297930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297930).length < 2 ^ (prefixWord ++ tailWord_7297930).sum := by decide
  have hdescent : baseEnd_7297930 < baseStart_7297930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297973 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_7297973 : Nat := 118140960795 + 7297973 * 2 ^ 59
def prefixEnd_7297973 : Nat := 4983230072969 + 3 ^ 40 * 7297973 * 2
def baseEnd_7297973 : Nat := 1249122650844960126924913

theorem tailTrace_7297973 : CollatzResearch.WordTrace tailWord_7297973 prefixEnd_7297973 1249122650844960126924913 := by
  unfold tailWord_7297973
  simp only [CollatzResearch.WordTrace]
  refine ⟨266178942789697690402970573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177452628526465126935313715 266178942789697690402970573)
  ·
    refine ⟨99817103546136633901113965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266178942789697690402970573 99817103546136633901113965)
    ·
      refine ⟨37431413829801237712917737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99817103546136633901113965 37431413829801237712917737)
      ·
        refine ⟨28073560372350928284688303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37431413829801237712917737 28073560372350928284688303)
        ·
          refine ⟨42110340558526392427032455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28073560372350928284688303 42110340558526392427032455)
          ·
            refine ⟨63165510837789588640548683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42110340558526392427032455 63165510837789588640548683)
            ·
              refine ⟨94748266256684382960823025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63165510837789588640548683 94748266256684382960823025)
              ·
                refine ⟨71061199692513287220617269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94748266256684382960823025 71061199692513287220617269)
                ·
                  refine ⟨6661987471173120676932869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71061199692513287220617269 6661987471173120676932869)
                  ·
                    refine ⟨1249122650844960126924913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661987471173120676932869 1249122650844960126924913)
                    ·
                      rfl

theorem cell23_7297973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_7297973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297973 prefixEnd_7297973 := by exact prefixLift 7297973
  have htrace : WordTrace (prefixWord ++ tailWord_7297973) baseStart_7297973 baseEnd_7297973 := by
    simpa [prefixWord, tailWord_7297973, baseEnd_7297973] using wordTrace_append hprefix tailTrace_7297973
  have hstable : (prefixWord ++ tailWord_7297973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297973).length < 2 ^ (prefixWord ++ tailWord_7297973).sum := by decide
  have hdescent : baseEnd_7297973 < baseStart_7297973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297976 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_7297976 : Nat := 118140960795 + 7297976 * 2 ^ 59
def prefixEnd_7297976 : Nat := 4983230072969 + 3 ^ 40 * 7297976 * 2
def baseEnd_7297976 : Nat := 3747369492976843869037225

theorem tailTrace_7297976 : CollatzResearch.WordTrace tailWord_7297976 prefixEnd_7297976 3747369492976843869037225 := by
  unfold tailWord_7297976
  simp only [CollatzResearch.WordTrace]
  refine ⟨133089526104343410957664891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177452701472457881276886521 133089526104343410957664891)
  ·
    refine ⟨199634289156515116436497337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133089526104343410957664891 199634289156515116436497337)
    ·
      refine ⟨149725716867386337327373003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199634289156515116436497337 149725716867386337327373003)
      ·
        refine ⟨224588575301079505991059505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149725716867386337327373003 224588575301079505991059505)
        ·
          refine ⟨168441431475809629493294629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224588575301079505991059505 168441431475809629493294629)
          ·
            refine ⟨31582768401714305529992743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168441431475809629493294629 31582768401714305529992743)
            ·
              refine ⟨47374152602571458294989115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31582768401714305529992743 47374152602571458294989115)
              ·
                refine ⟨71061228903857187442483673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47374152602571458294989115 71061228903857187442483673)
                ·
                  refine ⟨53295921677892890581862755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71061228903857187442483673 53295921677892890581862755)
                  ·
                    refine ⟨79943882516839335872794133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53295921677892890581862755 79943882516839335872794133)
                    ·
                      refine ⟨3747369492976843869037225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79943882516839335872794133 3747369492976843869037225)
                      ·
                        rfl

theorem cell23_7297976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_7297976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7297976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7297976 prefixEnd_7297976 := by exact prefixLift 7297976
  have htrace : WordTrace (prefixWord ++ tailWord_7297976) baseStart_7297976 baseEnd_7297976 := by
    simpa [prefixWord, tailWord_7297976, baseEnd_7297976] using wordTrace_append hprefix tailTrace_7297976
  have hstable : (prefixWord ++ tailWord_7297976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297976).length < 2 ^ (prefixWord ++ tailWord_7297976).sum := by decide
  have hdescent : baseEnd_7297976 < baseStart_7297976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298053 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_7298053 : Nat := 118140960795 + 7298053 * 2 ^ 59
def prefixEnd_7298053 : Nat := 4983230072969 + 3 ^ 40 * 7298053 * 2
def baseEnd_7298053 : Nat := 3747409030987240067774371

theorem tailTrace_7298053 : CollatzResearch.WordTrace tailWord_7298053 prefixEnd_7298053 3747409030987240067774371 := by
  unfold tailWord_7298053
  simp only [CollatzResearch.WordTrace]
  refine ⟨266181860629407864065882813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177454573752938576043921875 266181860629407864065882813)
  ·
    refine ⟨99818197736027949024706055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266181860629407864065882813 99818197736027949024706055)
    ·
      refine ⟨149727296604041923537059083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99818197736027949024706055 149727296604041923537059083)
      ·
        refine ⟨224590944906062885305588625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149727296604041923537059083 224590944906062885305588625)
        ·
          refine ⟨168443208679547163979191469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224590944906062885305588625 168443208679547163979191469)
          ·
            refine ⟨63166203254830186492196801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168443208679547163979191469 63166203254830186492196801)
            ·
              refine ⟨47374652441122639869147601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63166203254830186492196801 47374652441122639869147601)
              ·
                refine ⟨35530989330841979901860701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47374652441122639869147601 35530989330841979901860701)
                ·
                  refine ⟨13324120999065742463197763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35530989330841979901860701 13324120999065742463197763)
                  ·
                    refine ⟨19986181498598613694796645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13324120999065742463197763 19986181498598613694796645)
                    ·
                      refine ⟨3747409030987240067774371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19986181498598613694796645 3747409030987240067774371)
                      ·
                        rfl

theorem cell23_7298053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_7298053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298053 prefixEnd_7298053 := by exact prefixLift 7298053
  have htrace : WordTrace (prefixWord ++ tailWord_7298053) baseStart_7298053 baseEnd_7298053 := by
    simpa [prefixWord, tailWord_7298053, baseEnd_7298053] using wordTrace_append hprefix tailTrace_7298053
  have hstable : (prefixWord ++ tailWord_7298053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298053).length < 2 ^ (prefixWord ++ tailWord_7298053).sum := by decide
  have hdescent : baseEnd_7298053 < baseStart_7298053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298083 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4]
def baseStart_7298083 : Nat := 118140960795 + 7298083 * 2 ^ 59
def prefixEnd_7298083 : Nat := 4983230072969 + 3 ^ 40 * 7298083 * 2
def baseEnd_7298083 : Nat := 3747424435406874950399233

theorem tailTrace_7298083 : CollatzResearch.WordTrace tailWord_7298083 prefixEnd_7298083 3747424435406874950399233 := by
  unfold tailWord_7298083
  simp only [CollatzResearch.WordTrace]
  refine ⟨266182954819299179189474903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177455303212866119459649935 266182954819299179189474903)
  ·
    refine ⟨399274432228948768784212355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266182954819299179189474903 399274432228948768784212355)
    ·
      refine ⟨598911648343423153176318533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399274432228948768784212355 598911648343423153176318533)
      ·
        refine ⟨112295934064391841220559725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598911648343423153176318533 112295934064391841220559725)
        ·
          refine ⟨42110975274146940457709897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112295934064391841220559725 42110975274146940457709897)
          ·
            refine ⟨31583231455610205343282423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42110975274146940457709897 31583231455610205343282423)
            ·
              refine ⟨47374847183415308014923635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31583231455610205343282423 47374847183415308014923635)
              ·
                refine ⟨71062270775122962022385453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47374847183415308014923635 71062270775122962022385453)
                ·
                  refine ⟨26648351540671110758394545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71062270775122962022385453 26648351540671110758394545)
                  ·
                    refine ⟨19986263655503333068795909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26648351540671110758394545 19986263655503333068795909)
                    ·
                      refine ⟨3747424435406874950399233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19986263655503333068795909 3747424435406874950399233)
                      ·
                        rfl

theorem cell23_7298083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_7298083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298083 prefixEnd_7298083 := by exact prefixLift 7298083
  have htrace : WordTrace (prefixWord ++ tailWord_7298083) baseStart_7298083 baseEnd_7298083 := by
    simpa [prefixWord, tailWord_7298083, baseEnd_7298083] using wordTrace_append hprefix tailTrace_7298083
  have hstable : (prefixWord ++ tailWord_7298083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298083).length < 2 ^ (prefixWord ++ tailWord_7298083).sum := by decide
  have hdescent : baseEnd_7298083 < baseStart_7298083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298103 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_7298103 : Nat := 118140960795 + 7298103 * 2 ^ 59
def prefixEnd_7298103 : Nat := 4983230072969 + 3 ^ 40 * 7298103 * 2
def baseEnd_7298103 : Nat := 3747434705019964872149141

theorem tailTrace_7298103 : CollatzResearch.WordTrace tailWord_7298103 prefixEnd_7298103 3747434705019964872149141 := by
  unfold tailWord_7298103
  simp only [CollatzResearch.WordTrace]
  refine ⟨266183684279226722605202963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177455789519484481736801975 266183684279226722605202963)
  ·
    refine ⟨399275526418840083907804445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266183684279226722605202963 399275526418840083907804445)
    ·
      refine ⟨149728322407065031465426667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399275526418840083907804445 149728322407065031465426667)
      ·
        refine ⟨224592483610597547198140001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149728322407065031465426667 224592483610597547198140001)
        ·
          refine ⟨168444362707948160398605001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224592483610597547198140001 168444362707948160398605001)
          ·
            refine ⟨126333272030961120298953751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168444362707948160398605001 126333272030961120298953751)
            ·
              refine ⟨189499908046441680448430627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126333272030961120298953751 189499908046441680448430627)
              ·
                refine ⟨284249862069662520672645941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189499908046441680448430627 284249862069662520672645941)
                ·
                  refine ⟨26648424569030861313060557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284249862069662520672645941 26648424569030861313060557)
                  ·
                    refine ⟨9993159213386572992397709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26648424569030861313060557 9993159213386572992397709)
                    ·
                      refine ⟨3747434705019964872149141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9993159213386572992397709 3747434705019964872149141)
                      ·
                        rfl

theorem cell23_7298103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_7298103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298103 prefixEnd_7298103 := by exact prefixLift 7298103
  have htrace : WordTrace (prefixWord ++ tailWord_7298103) baseStart_7298103 baseEnd_7298103 := by
    simpa [prefixWord, tailWord_7298103, baseEnd_7298103] using wordTrace_append hprefix tailTrace_7298103
  have hstable : (prefixWord ++ tailWord_7298103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298103).length < 2 ^ (prefixWord ++ tailWord_7298103).sum := by decide
  have hdescent : baseEnd_7298103 < baseStart_7298103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298110 : List Nat := [4, 2, 1, 3, 1, 1, 3, 8]
def baseStart_7298110 : Nat := 118140960795 + 7298110 * 2 ^ 59
def prefixEnd_7298110 : Nat := 4983230072969 + 3 ^ 40 * 7298110 * 2
def baseEnd_7298110 : Nat := 138794011088316531287467

theorem tailTrace_7298110 : CollatzResearch.WordTrace tailWord_7298110 prefixEnd_7298110 138794011088316531287467 := by
  unfold tailWord_7298110
  simp only [CollatzResearch.WordTrace]
  refine ⟨33272992448775170350088473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177455959726800908533805189 33272992448775170350088473)
  ·
    refine ⟨24954744336581377762566355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33272992448775170350088473 24954744336581377762566355)
    ·
      refine ⟨37432116504872066643849533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24954744336581377762566355 37432116504872066643849533)
      ·
        refine ⟨14037043689327024991443575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37432116504872066643849533 14037043689327024991443575)
        ·
          refine ⟨21055565533990537487165363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037043689327024991443575 21055565533990537487165363)
          ·
            refine ⟨31583348300985806230748045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21055565533990537487165363 31583348300985806230748045)
            ·
              refine ⟨11843755612869677336530517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31583348300985806230748045 11843755612869677336530517)
              ·
                refine ⟨138794011088316531287467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11843755612869677336530517 138794011088316531287467)
                ·
                  rfl

theorem cell23_7298110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_7298110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298110 prefixEnd_7298110 := by exact prefixLift 7298110
  have htrace : WordTrace (prefixWord ++ tailWord_7298110) baseStart_7298110 baseEnd_7298110 := by
    simpa [prefixWord, tailWord_7298110, baseEnd_7298110] using wordTrace_append hprefix tailTrace_7298110
  have hstable : (prefixWord ++ tailWord_7298110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298110).length < 2 ^ (prefixWord ++ tailWord_7298110).sum := by decide
  have hdescent : baseEnd_7298110 < baseStart_7298110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298120 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_7298120 : Nat := 118140960795 + 7298120 * 2 ^ 59
def prefixEnd_7298120 : Nat := 4983230072969 + 3 ^ 40 * 7298120 * 2
def baseEnd_7298120 : Nat := 3747443434191091305636563

theorem tailTrace_7298120 : CollatzResearch.WordTrace tailWord_7298120 prefixEnd_7298120 3747443434191091305636563 := by
  unfold tailWord_7298120
  simp only [CollatzResearch.WordTrace]
  refine ⟨133092152160082567254285907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177456202880110089672381209 133092152160082567254285907)
  ·
    refine ⟨199638228240123850881428861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133092152160082567254285907 199638228240123850881428861)
    ·
      refine ⟨74864335590046444080535823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199638228240123850881428861 74864335590046444080535823)
      ·
        refine ⟨112296503385069666120803735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74864335590046444080535823 112296503385069666120803735)
        ·
          refine ⟨168444755077604499181205603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112296503385069666120803735 168444755077604499181205603)
          ·
            refine ⟨252667132616406748771808405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168444755077604499181205603 252667132616406748771808405)
            ·
              refine ⟨11843771841394066348678519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252667132616406748771808405 11843771841394066348678519)
              ·
                refine ⟨17765657762091099523017779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11843771841394066348678519 17765657762091099523017779)
                ·
                  refine ⟨26648486643136649284526669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17765657762091099523017779 26648486643136649284526669)
                  ·
                    refine ⟨9993182491176243481697501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26648486643136649284526669 9993182491176243481697501)
                    ·
                      refine ⟨3747443434191091305636563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9993182491176243481697501 3747443434191091305636563)
                      ·
                        rfl

theorem cell23_7298120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_7298120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298120 prefixEnd_7298120 := by exact prefixLift 7298120
  have htrace : WordTrace (prefixWord ++ tailWord_7298120) baseStart_7298120 baseEnd_7298120 := by
    simpa [prefixWord, tailWord_7298120, baseEnd_7298120] using wordTrace_append hprefix tailTrace_7298120
  have hstable : (prefixWord ++ tailWord_7298120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298120).length < 2 ^ (prefixWord ++ tailWord_7298120).sum := by decide
  have hdescent : baseEnd_7298120 < baseStart_7298120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298133 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7298133 : Nat := 118140960795 + 7298133 * 2 ^ 59
def prefixEnd_7298133 : Nat := 4983230072969 + 3 ^ 40 * 7298133 * 2
def baseEnd_7298133 : Nat := 3747450109439599754774003

theorem tailTrace_7298133 : CollatzResearch.WordTrace tailWord_7298133 prefixEnd_7298133 3747450109439599754774003 := by
  unfold tailWord_7298133
  simp only [CollatzResearch.WordTrace]
  refine ⟨266184778469118037728795053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177456518979412025152530035 266184778469118037728795053)
  ·
    refine ⟨99819291925919264148298145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266184778469118037728795053 99819291925919264148298145)
    ·
      refine ⟨74864468944439448111223609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99819291925919264148298145 74864468944439448111223609)
      ·
        refine ⟨56148351708329586083417707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74864468944439448111223609 56148351708329586083417707)
        ·
          refine ⟨84222527562494379125126561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56148351708329586083417707 84222527562494379125126561)
          ·
            refine ⟨63166895671870784343844921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84222527562494379125126561 63166895671870784343844921)
            ·
              refine ⟨47375171753903088257883691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63166895671870784343844921 47375171753903088257883691)
              ·
                refine ⟨71062757630854632386825537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47375171753903088257883691 71062757630854632386825537)
                ·
                  refine ⟨53297068223140974290119153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71062757630854632386825537 53297068223140974290119153)
                  ·
                    refine ⟨39972801167355730717589365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53297068223140974290119153 39972801167355730717589365)
                    ·
                      refine ⟨3747450109439599754774003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39972801167355730717589365 3747450109439599754774003)
                      ·
                        rfl

theorem cell23_7298133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7298133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298133 prefixEnd_7298133 := by exact prefixLift 7298133
  have htrace : WordTrace (prefixWord ++ tailWord_7298133) baseStart_7298133 baseEnd_7298133 := by
    simpa [prefixWord, tailWord_7298133, baseEnd_7298133] using wordTrace_append hprefix tailTrace_7298133
  have hstable : (prefixWord ++ tailWord_7298133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298133).length < 2 ^ (prefixWord ++ tailWord_7298133).sum := by decide
  have hdescent : baseEnd_7298133 < baseStart_7298133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298153 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_7298153 : Nat := 118140960795 + 7298153 * 2 ^ 59
def prefixEnd_7298153 : Nat := 4983230072969 + 3 ^ 40 * 7298153 * 2
def baseEnd_7298153 : Nat := 1249153459684229892174637

theorem tailTrace_7298153 : CollatzResearch.WordTrace tailWord_7298153 prefixEnd_7298153 1249153459684229892174637 := by
  unfold tailWord_7298153
  simp only [CollatzResearch.WordTrace]
  refine ⟨266185507929045581144523113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177457005286030387429682075 266185507929045581144523113)
  ·
    refine ⟨199639130946784185858392335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266185507929045581144523113 199639130946784185858392335)
    ·
      refine ⟨299458696420176278787588503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199639130946784185858392335 299458696420176278787588503)
      ·
        refine ⟨449188044630264418181382755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299458696420176278787588503 449188044630264418181382755)
        ·
          refine ⟨673782066945396627272074133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449188044630264418181382755 673782066945396627272074133)
          ·
            refine ⟨31583534388065466903378475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 673782066945396627272074133 31583534388065466903378475)
            ·
              refine ⟨47375301582098200355067713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31583534388065466903378475 47375301582098200355067713)
              ·
                refine ⟨35531476186573650266300785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47375301582098200355067713 35531476186573650266300785)
                ·
                  refine ⟨26648607139930237699725589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35531476186573650266300785 26648607139930237699725589)
                  ·
                    refine ⟨1249153459684229892174637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26648607139930237699725589 1249153459684229892174637)
                    ·
                      rfl

theorem cell23_7298153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_7298153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298153 prefixEnd_7298153 := by exact prefixLift 7298153
  have htrace : WordTrace (prefixWord ++ tailWord_7298153) baseStart_7298153 baseEnd_7298153 := by
    simpa [prefixWord, tailWord_7298153, baseEnd_7298153] using wordTrace_append hprefix tailTrace_7298153
  have hstable : (prefixWord ++ tailWord_7298153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298153).length < 2 ^ (prefixWord ++ tailWord_7298153).sum := by decide
  have hdescent : baseEnd_7298153 < baseStart_7298153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298154 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_7298154 : Nat := 118140960795 + 7298154 * 2 ^ 59
def prefixEnd_7298154 : Nat := 4983230072969 + 3 ^ 40 * 7298154 * 2
def baseEnd_7298154 : Nat := 3747460892533344172611407

theorem tailTrace_7298154 : CollatzResearch.WordTrace tailWord_7298154 prefixEnd_7298154 3747460892533344172611407 := by
  unfold tailWord_7298154
  simp only [CollatzResearch.WordTrace]
  refine ⟨66546386100510489578827379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177457029601361305543539677 66546386100510489578827379)
  ·
    refine ⟨99819579150765734368241069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66546386100510489578827379 99819579150765734368241069)
    ·
      refine ⟨37432342181537150388090401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99819579150765734368241069 37432342181537150388090401)
      ·
        refine ⟨28074256636152862791067801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37432342181537150388090401 28074256636152862791067801)
        ·
          refine ⟨21055692477114647093300851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28074256636152862791067801 21055692477114647093300851)
          ·
            refine ⟨31583538715671970639951277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21055692477114647093300851 31583538715671970639951277)
            ·
              refine ⟨11843827018376988989981729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31583538715671970639951277 11843827018376988989981729)
              ·
                refine ⟨8882870263782741742486297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11843827018376988989981729 8882870263782741742486297)
                ·
                  refine ⟨6662152697837056306864723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882870263782741742486297 6662152697837056306864723)
                  ·
                    refine ⟨9993229046755584460297085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6662152697837056306864723 9993229046755584460297085)
                    ·
                      refine ⟨3747460892533344172611407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9993229046755584460297085 3747460892533344172611407)
                      ·
                        rfl

theorem cell23_7298154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_7298154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298154 prefixEnd_7298154 := by exact prefixLift 7298154
  have htrace : WordTrace (prefixWord ++ tailWord_7298154) baseStart_7298154 baseEnd_7298154 := by
    simpa [prefixWord, tailWord_7298154, baseEnd_7298154] using wordTrace_append hprefix tailTrace_7298154
  have hstable : (prefixWord ++ tailWord_7298154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298154).length < 2 ^ (prefixWord ++ tailWord_7298154).sum := by decide
  have hdescent : baseEnd_7298154 < baseStart_7298154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298194 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_7298194 : Nat := 118140960795 + 7298194 * 2 ^ 59
def prefixEnd_7298194 : Nat := 4983230072969 + 3 ^ 40 * 7298194 * 2
def baseEnd_7298194 : Nat := 3747481431759524016111223

theorem tailTrace_7298194 : CollatzResearch.WordTrace tailWord_7298194 prefixEnd_7298194 3747481431759524016111223 := by
  unfold tailWord_7298194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66546750830474261286691409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177458002214598030097843757 66546750830474261286691409)
  ·
    refine ⟨49910063122855695965018557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66546750830474261286691409 49910063122855695965018557)
    ·
      refine ⟨18716273671070885986881959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49910063122855695965018557 18716273671070885986881959)
      ·
        refine ⟨28074410506606328980322939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18716273671070885986881959 28074410506606328980322939)
        ·
          refine ⟨42111615759909493470484409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28074410506606328980322939 42111615759909493470484409)
          ·
            refine ⟨31583711819932120102863307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42111615759909493470484409 31583711819932120102863307)
            ·
              refine ⟨47375567729898180154294961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31583711819932120102863307 47375567729898180154294961)
              ·
                refine ⟨35531675797423635115721221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47375567729898180154294961 35531675797423635115721221)
                ·
                  refine ⟨6662189212016931584197729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35531675797423635115721221 6662189212016931584197729)
                  ·
                    refine ⟨4996641909012698688148297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6662189212016931584197729 4996641909012698688148297)
                    ·
                      refine ⟨3747481431759524016111223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996641909012698688148297 3747481431759524016111223)
                      ·
                        rfl

theorem cell23_7298194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_7298194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298194 prefixEnd_7298194 := by exact prefixLift 7298194
  have htrace : WordTrace (prefixWord ++ tailWord_7298194) baseStart_7298194 baseEnd_7298194 := by
    simpa [prefixWord, tailWord_7298194, baseEnd_7298194] using wordTrace_append hprefix tailTrace_7298194
  have hstable : (prefixWord ++ tailWord_7298194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298194).length < 2 ^ (prefixWord ++ tailWord_7298194).sum := by decide
  have hdescent : baseEnd_7298194 < baseStart_7298194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298223 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_7298223 : Nat := 118140960795 + 7298223 * 2 ^ 59
def prefixEnd_7298223 : Nat := 4983230072969 + 3 ^ 40 * 7298223 * 2
def baseEnd_7298223 : Nat := 3747496322698504402648589

theorem tailTrace_7298223 : CollatzResearch.WordTrace tailWord_7298223 prefixEnd_7298223 3747496322698504402648589 := by
  unfold tailWord_7298223
  simp only [CollatzResearch.WordTrace]
  refine ⟨266188061038791983099571323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177458707359194655399714215 266188061038791983099571323)
  ·
    refine ⟨399282091558187974649356985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266188061038791983099571323 399282091558187974649356985)
    ·
      refine ⟨299461568668640980987017739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399282091558187974649356985 299461568668640980987017739)
      ·
        refine ⟨449192353002961471480526609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299461568668640980987017739 449192353002961471480526609)
        ·
          refine ⟨336894264752221103610394957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449192353002961471480526609 336894264752221103610394957)
          ·
            refine ⟨126335349282082913853898109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336894264752221103610394957 126335349282082913853898109)
            ·
              refine ⟨47375755980781092695211791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126335349282082913853898109 47375755980781092695211791)
              ·
                refine ⟨71063633971171639042817687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47375755980781092695211791 71063633971171639042817687)
                ·
                  refine ⟨106595450956757458564226531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71063633971171639042817687 106595450956757458564226531)
                  ·
                    refine ⟨159893176435136187846339797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106595450956757458564226531 159893176435136187846339797)
                    ·
                      refine ⟨3747496322698504402648589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159893176435136187846339797 3747496322698504402648589)
                      ·
                        rfl

theorem cell23_7298223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_7298223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298223 prefixEnd_7298223 := by exact prefixLift 7298223
  have htrace : WordTrace (prefixWord ++ tailWord_7298223) baseStart_7298223 baseEnd_7298223 := by
    simpa [prefixWord, tailWord_7298223, baseEnd_7298223] using wordTrace_append hprefix tailTrace_7298223
  have hstable : (prefixWord ++ tailWord_7298223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298223).length < 2 ^ (prefixWord ++ tailWord_7298223).sum := by decide
  have hdescent : baseEnd_7298223 < baseStart_7298223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298344 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_7298344 : Nat := 118140960795 + 7298344 * 2 ^ 59
def prefixEnd_7298344 : Nat := 4983230072969 + 3 ^ 40 * 7298344 * 2
def baseEnd_7298344 : Nat := 3747558453857698429235533

theorem tailTrace_7298344 : CollatzResearch.WordTrace tailWord_7298344 prefixEnd_7298344 3747558453857698429235533 := by
  unfold tailWord_7298344
  simp only [CollatzResearch.WordTrace]
  refine ⟨133096237135676810382363043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177461649514235747176484057 133096237135676810382363043)
  ·
    refine ⟨199644355703515215573544565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133096237135676810382363043 199644355703515215573544565)
    ·
      refine ⟨18716658347204551460019803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199644355703515215573544565 18716658347204551460019803)
      ·
        refine ⟨28074987520806827190029705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18716658347204551460019803 28074987520806827190029705)
        ·
          refine ⟨21056240640605120392522279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28074987520806827190029705 21056240640605120392522279)
          ·
            refine ⟨31584360960907680588783419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21056240640605120392522279 31584360960907680588783419)
            ·
              refine ⟨47376541441361520883175129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31584360960907680588783419 47376541441361520883175129)
              ·
                refine ⟨35532406081021140662381347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47376541441361520883175129 35532406081021140662381347)
                ·
                  refine ⟨53298609121531710993572021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35532406081021140662381347 53298609121531710993572021)
                  ·
                    refine ⟨4996744605143597905647377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53298609121531710993572021 4996744605143597905647377)
                    ·
                      refine ⟨3747558453857698429235533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996744605143597905647377 3747558453857698429235533)
                      ·
                        rfl

theorem cell23_7298344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_7298344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298344 prefixEnd_7298344 := by exact prefixLift 7298344
  have htrace : WordTrace (prefixWord ++ tailWord_7298344) baseStart_7298344 baseEnd_7298344 := by
    simpa [prefixWord, tailWord_7298344, baseEnd_7298344] using wordTrace_append hprefix tailTrace_7298344
  have hstable : (prefixWord ++ tailWord_7298344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298344).length < 2 ^ (prefixWord ++ tailWord_7298344).sum := by decide
  have hdescent : baseEnd_7298344 < baseStart_7298344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298354 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_7298354 : Nat := 118140960795 + 7298354 * 2 ^ 59
def prefixEnd_7298354 : Nat := 4983230072969 + 3 ^ 40 * 7298354 * 2
def baseEnd_7298354 : Nat := 1249187862888081130036829

theorem tailTrace_7298354 : CollatzResearch.WordTrace tailWord_7298354 prefixEnd_7298354 1249187862888081130036829 := by
  unfold tailWord_7298354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66548209750329348118147529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177461892667544928315060077 66548209750329348118147529)
  ·
    refine ⟨49911157312747011088610647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66548209750329348118147529 49911157312747011088610647)
    ·
      refine ⟨74866735969120516632915971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49911157312747011088610647 74866735969120516632915971)
      ·
        refine ⟨112300103953680774949373957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74866735969120516632915971 112300103953680774949373957)
        ·
          refine ⟨21056269491315145303007617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112300103953680774949373957 21056269491315145303007617)
          ·
            refine ⟨15792202118486358977255713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21056269491315145303007617 15792202118486358977255713)
            ·
              refine ⟨11844151588864769232941785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15792202118486358977255713 11844151588864769232941785)
              ·
                refine ⟨8883113691648576924706339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11844151588864769232941785 8883113691648576924706339)
                ·
                  refine ⟨13324670537472865387059509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8883113691648576924706339 13324670537472865387059509)
                  ·
                    refine ⟨1249187862888081130036829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13324670537472865387059509 1249187862888081130036829)
                    ·
                      rfl

theorem cell23_7298354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_7298354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298354 prefixEnd_7298354 := by exact prefixLift 7298354
  have htrace : WordTrace (prefixWord ++ tailWord_7298354) baseStart_7298354 baseEnd_7298354 := by
    simpa [prefixWord, tailWord_7298354, baseEnd_7298354] using wordTrace_append hprefix tailTrace_7298354
  have hstable : (prefixWord ++ tailWord_7298354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298354).length < 2 ^ (prefixWord ++ tailWord_7298354).sum := by decide
  have hdescent : baseEnd_7298354 < baseStart_7298354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298360 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_7298360 : Nat := 118140960795 + 7298360 * 2 ^ 59
def prefixEnd_7298360 : Nat := 4983230072969 + 3 ^ 40 * 7298360 * 2
def baseEnd_7298360 : Nat := 3747566669548170366635459

theorem tailTrace_7298360 : CollatzResearch.WordTrace tailWord_7298360 prefixEnd_7298360 3747566669548170366635459 := by
  unfold tailWord_7298360
  simp only [CollatzResearch.WordTrace]
  refine ⟨133096528919647827748654267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177462038559530436998205689 133096528919647827748654267)
  ·
    refine ⟨199644793379471741622981401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133096528919647827748654267 199644793379471741622981401)
    ·
      refine ⟨149733595034603806217236051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199644793379471741622981401 149733595034603806217236051)
      ·
        refine ⟨224600392551905709325854077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149733595034603806217236051 224600392551905709325854077)
        ·
          refine ⟨84225147206964640997195279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224600392551905709325854077 84225147206964640997195279)
          ·
            refine ⟨126337720810446961495792919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84225147206964640997195279 126337720810446961495792919)
            ·
              refine ⟨189506581215670442243689379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126337720810446961495792919 189506581215670442243689379)
              ·
                refine ⟨284259871823505663365534069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189506581215670442243689379 284259871823505663365534069)
                ·
                  refine ⟨26649362983453655940518819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284259871823505663365534069 26649362983453655940518819)
                  ·
                    refine ⟨39974044475180483910778229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26649362983453655940518819 39974044475180483910778229)
                    ·
                      refine ⟨3747566669548170366635459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39974044475180483910778229 3747566669548170366635459)
                      ·
                        rfl

theorem cell23_7298360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_7298360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298360 prefixEnd_7298360 := by exact prefixLift 7298360
  have htrace : WordTrace (prefixWord ++ tailWord_7298360) baseStart_7298360 baseEnd_7298360 := by
    simpa [prefixWord, tailWord_7298360, baseEnd_7298360] using wordTrace_append hprefix tailTrace_7298360
  have hstable : (prefixWord ++ tailWord_7298360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298360).length < 2 ^ (prefixWord ++ tailWord_7298360).sum := by decide
  have hdescent : baseEnd_7298360 < baseStart_7298360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298367 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 4, 4]
def baseStart_7298367 : Nat := 118140960795 + 7298367 * 2 ^ 59
def prefixEnd_7298367 : Nat := 4983230072969 + 3 ^ 40 * 7298367 * 2
def baseEnd_7298367 : Nat := 1249190087970917279749309

theorem tailTrace_7298367 : CollatzResearch.WordTrace tailWord_7298367 prefixEnd_7298367 1249190087970917279749309 := by
  unfold tailWord_7298367
  simp only [CollatzResearch.WordTrace]
  refine ⟨266193313150270295692813355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177462208766846863795208903 266193313150270295692813355)
  ·
    refine ⟨399289969725405443539220033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266193313150270295692813355 399289969725405443539220033)
    ·
      refine ⟨299467477294054082654415025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399289969725405443539220033 299467477294054082654415025)
      ·
        refine ⟨224600607970540561990811269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299467477294054082654415025 224600607970540561990811269)
        ·
          refine ⟨42112613994476355373277113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224600607970540561990811269 42112613994476355373277113)
          ·
            refine ⟨31584460495857266529957835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42112613994476355373277113 31584460495857266529957835)
            ·
              refine ⟨47376690743785899794936753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31584460495857266529957835 47376690743785899794936753)
              ·
                refine ⟨35532518057839424846202565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47376690743785899794936753 35532518057839424846202565)
                ·
                  refine ⟨6662347135844892158662981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35532518057839424846202565 6662347135844892158662981)
                  ·
                    refine ⟨1249190087970917279749309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6662347135844892158662981 1249190087970917279749309)
                    ·
                      rfl

theorem cell23_7298367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_7298367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298367 prefixEnd_7298367 := by exact prefixLift 7298367
  have htrace : WordTrace (prefixWord ++ tailWord_7298367) baseStart_7298367 baseEnd_7298367 := by
    simpa [prefixWord, tailWord_7298367, baseEnd_7298367] using wordTrace_append hprefix tailTrace_7298367
  have hstable : (prefixWord ++ tailWord_7298367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298367).length < 2 ^ (prefixWord ++ tailWord_7298367).sum := by decide
  have hdescent : baseEnd_7298367 < baseStart_7298367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298380 : List Nat := [2, 2, 1, 3, 2, 2, 11]
def baseStart_7298380 : Nat := 118140960795 + 7298380 * 2 ^ 59
def prefixEnd_7298380 : Nat := 4983230072969 + 3 ^ 40 * 7298380 * 2
def baseEnd_7298380 : Nat := 46266381964953830720807

theorem tailTrace_7298380 : CollatzResearch.WordTrace tailWord_7298380 prefixEnd_7298380 46266381964953830720807 := by
  unfold tailWord_7298380
  simp only [CollatzResearch.WordTrace]
  refine ⟨133096893649611599456518297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177462524866148799275357729 133096893649611599456518297)
  ·
    refine ⟨99822670237208699592388723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133096893649611599456518297 99822670237208699592388723)
    ·
      refine ⟨149734005355813049388583085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99822670237208699592388723 149734005355813049388583085)
      ·
        refine ⟨56150252008429893520718657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149734005355813049388583085 56150252008429893520718657)
        ·
          refine ⟨42112689006322420140538993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56150252008429893520718657 42112689006322420140538993)
          ·
            refine ⟨31584516754741815105404245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42112689006322420140538993 31584516754741815105404245)
            ·
              refine ⟨46266381964953830720807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31584516754741815105404245 46266381964953830720807)
              ·
                rfl

theorem cell23_7298380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 11].length) (baseStart_7298380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298380 prefixEnd_7298380 := by exact prefixLift 7298380
  have htrace : WordTrace (prefixWord ++ tailWord_7298380) baseStart_7298380 baseEnd_7298380 := by
    simpa [prefixWord, tailWord_7298380, baseEnd_7298380] using wordTrace_append hprefix tailTrace_7298380
  have hstable : (prefixWord ++ tailWord_7298380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298380).length < 2 ^ (prefixWord ++ tailWord_7298380).sum := by decide
  have hdescent : baseEnd_7298380 < baseStart_7298380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298391 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 3, 2, 2]
def baseStart_7298391 : Nat := 118140960795 + 7298391 * 2 ^ 59
def prefixEnd_7298391 : Nat := 4983230072969 + 3 ^ 40 * 7298391 * 2
def baseEnd_7298391 : Nat := 3747582587448459745347817

theorem tailTrace_7298391 : CollatzResearch.WordTrace tailWord_7298391 prefixEnd_7298391 3747582587448459745347817 := by
  unfold tailWord_7298391
  simp only [CollatzResearch.WordTrace]
  refine ⟨266194188502183347791687027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177462792334788898527791351 266194188502183347791687027)
  ·
    refine ⟨399291282753275021687530541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266194188502183347791687027 399291282753275021687530541)
    ·
      refine ⟨149734231032478133132823953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399291282753275021687530541 149734231032478133132823953)
      ·
        refine ⟨112300673274358599849617965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149734231032478133132823953 112300673274358599849617965)
        ·
          refine ⟨42112752477884474943606737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112300673274358599849617965 42112752477884474943606737)
          ·
            refine ⟨31584564358413356207705053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42112752477884474943606737 31584564358413356207705053)
            ·
              refine ⟨11844211634405008577889395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31584564358413356207705053 11844211634405008577889395)
              ·
                refine ⟨17766317451607512866834093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11844211634405008577889395 17766317451607512866834093)
                ·
                  refine ⟨6662369044352817325062785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17766317451607512866834093 6662369044352817325062785)
                  ·
                    refine ⟨4996776783264612993797089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6662369044352817325062785 4996776783264612993797089)
                    ·
                      refine ⟨3747582587448459745347817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996776783264612993797089 3747582587448459745347817)
                      ·
                        rfl

theorem cell23_7298391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_7298391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298391 prefixEnd_7298391 := by exact prefixLift 7298391
  have htrace : WordTrace (prefixWord ++ tailWord_7298391) baseStart_7298391 baseEnd_7298391 := by
    simpa [prefixWord, tailWord_7298391, baseEnd_7298391] using wordTrace_append hprefix tailTrace_7298391
  have hstable : (prefixWord ++ tailWord_7298391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298391).length < 2 ^ (prefixWord ++ tailWord_7298391).sum := by decide
  have hdescent : baseEnd_7298391 < baseStart_7298391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298408 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_7298408 : Nat := 118140960795 + 7298408 * 2 ^ 59
def prefixEnd_7298408 : Nat := 4983230072969 + 3 ^ 40 * 7298408 * 2
def baseEnd_7298408 : Nat := 3747591316619586178835239

theorem tailTrace_7298408 : CollatzResearch.WordTrace tailWord_7298408 prefixEnd_7298408 3747591316619586178835239 := by
  unfold tailWord_7298408
  simp only [CollatzResearch.WordTrace]
  refine ⟨133097404271560879847527939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177463205695414506463370585 133097404271560879847527939)
  ·
    refine ⟨199646106407341319771291909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133097404271560879847527939 199646106407341319771291909)
    ·
      refine ⟨37433644951376497457117233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199646106407341319771291909 37433644951376497457117233)
      ·
        refine ⟨28075233713532373092837925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37433644951376497457117233 28075233713532373092837925)
        ·
          refine ⟨5264106321287319954907111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28075233713532373092837925 5264106321287319954907111)
          ·
            refine ⟨7896159481930979932360667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264106321287319954907111 7896159481930979932360667)
            ·
              refine ⟨11844239222896469898541001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7896159481930979932360667 11844239222896469898541001)
              ·
                refine ⟨8883179417172352423905751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11844239222896469898541001 8883179417172352423905751)
                ·
                  refine ⟨13324769125758528635858627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8883179417172352423905751 13324769125758528635858627)
                  ·
                    refine ⟨19987153688637792953787941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13324769125758528635858627 19987153688637792953787941)
                    ·
                      refine ⟨3747591316619586178835239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19987153688637792953787941 3747591316619586178835239)
                      ·
                        rfl

theorem cell23_7298408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_7298408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298408 prefixEnd_7298408 := by exact prefixLift 7298408
  have htrace : WordTrace (prefixWord ++ tailWord_7298408) baseStart_7298408 baseEnd_7298408 := by
    simpa [prefixWord, tailWord_7298408, baseEnd_7298408] using wordTrace_append hprefix tailTrace_7298408
  have hstable : (prefixWord ++ tailWord_7298408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298408).length < 2 ^ (prefixWord ++ tailWord_7298408).sum := by decide
  have hdescent : baseEnd_7298408 < baseStart_7298408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298457 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_7298457 : Nat := 118140960795 + 7298457 * 2 ^ 59
def prefixEnd_7298457 : Nat := 4983230072969 + 3 ^ 40 * 7298457 * 2
def baseEnd_7298457 : Nat := 1249205492390552162374171

theorem tailTrace_7298457 : CollatzResearch.WordTrace tailWord_7298457 prefixEnd_7298457 1249205492390552162374171 := by
  unfold tailWord_7298457
  simp only [CollatzResearch.WordTrace]
  refine ⟨266196595719944241063589625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177464397146629494042393083 266196595719944241063589625)
  ·
    refine ⟨199647446789958180797692219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266196595719944241063589625 199647446789958180797692219)
    ·
      refine ⟨299471170184937271196538329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199647446789958180797692219 299471170184937271196538329)
      ·
        refine ⟨224603377638702953397403747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299471170184937271196538329 224603377638702953397403747)
        ·
          refine ⟨336905066458054430096105621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224603377638702953397403747 336905066458054430096105621)
          ·
            refine ⟨15792424990221301410754951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 336905066458054430096105621 15792424990221301410754951)
            ·
              refine ⟨23688637485331952116132427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15792424990221301410754951 23688637485331952116132427)
              ·
                refine ⟨35532956227997928174198641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23688637485331952116132427 35532956227997928174198641)
                ·
                  refine ⟨26649717170998446130648981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35532956227997928174198641 26649717170998446130648981)
                  ·
                    refine ⟨1249205492390552162374171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26649717170998446130648981 1249205492390552162374171)
                    ·
                      rfl

theorem cell23_7298457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_7298457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298457 prefixEnd_7298457 := by exact prefixLift 7298457
  have htrace : WordTrace (prefixWord ++ tailWord_7298457) baseStart_7298457 baseEnd_7298457 := by
    simpa [prefixWord, tailWord_7298457, baseEnd_7298457] using wordTrace_append hprefix tailTrace_7298457
  have hstable : (prefixWord ++ tailWord_7298457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298457).length < 2 ^ (prefixWord ++ tailWord_7298457).sum := by decide
  have hdescent : baseEnd_7298457 < baseStart_7298457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298467 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 3]
def baseStart_7298467 : Nat := 118140960795 + 7298467 * 2 ^ 59
def prefixEnd_7298467 : Nat := 4983230072969 + 3 ^ 40 * 7298467 * 2
def baseEnd_7298467 : Nat := 3747621611978201447997467

theorem tailTrace_7298467 : CollatzResearch.WordTrace tailWord_7298467 prefixEnd_7298467 3747621611978201447997467 := by
  unfold tailWord_7298467
  simp only [CollatzResearch.WordTrace]
  refine ⟨266196960449908012771453655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177464640299938675180969103 266196960449908012771453655)
  ·
    refine ⟨399295440674862019157180483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266196960449908012771453655 399295440674862019157180483)
    ·
      refine ⟨598943161012293028735770725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399295440674862019157180483 598943161012293028735770725)
      ·
        refine ⟨112301842689804942887957011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598943161012293028735770725 112301842689804942887957011)
        ·
          refine ⟨168452764034707414331935517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112301842689804942887957011 168452764034707414331935517)
          ·
            refine ⟨63169786513015280374475819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168452764034707414331935517 63169786513015280374475819)
            ·
              refine ⟨94754679769522920561713729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63169786513015280374475819 94754679769522920561713729)
              ·
                refine ⟨71066009827142190421285297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94754679769522920561713729 71066009827142190421285297)
                ·
                  refine ⟨53299507370356642815963973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71066009827142190421285297 53299507370356642815963973)
                  ·
                    refine ⟨9993657631941870527993245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53299507370356642815963973 9993657631941870527993245)
                    ·
                      refine ⟨3747621611978201447997467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9993657631941870527993245 3747621611978201447997467)
                      ·
                        rfl

theorem cell23_7298467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_7298467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298467 prefixEnd_7298467 := by exact prefixLift 7298467
  have htrace : WordTrace (prefixWord ++ tailWord_7298467) baseStart_7298467 baseEnd_7298467 := by
    simpa [prefixWord, tailWord_7298467, baseEnd_7298467] using wordTrace_append hprefix tailTrace_7298467
  have hstable : (prefixWord ++ tailWord_7298467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298467).length < 2 ^ (prefixWord ++ tailWord_7298467).sum := by decide
  have hdescent : baseEnd_7298467 < baseStart_7298467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298481 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 4, 2, 2]
def baseStart_7298481 : Nat := 118140960795 + 7298481 * 2 ^ 59
def prefixEnd_7298481 : Nat := 4983230072969 + 3 ^ 40 * 7298481 * 2
def baseEnd_7298481 : Nat := 3747628800707364393222403

theorem tailTrace_7298481 : CollatzResearch.WordTrace tailWord_7298481 prefixEnd_7298481 3747628800707364393222403 := by
  unfold tailWord_7298481
  simp only [CollatzResearch.WordTrace]
  refine ⟨266197471071857293162463297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177464980714571528774975531 266197471071857293162463297)
  ·
    refine ⟨199648103303892969871847473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266197471071857293162463297 199648103303892969871847473)
    ·
      refine ⟨149736077477919727403885605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199648103303892969871847473 149736077477919727403885605)
      ·
        refine ⟨28075514527109948888228551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149736077477919727403885605 28075514527109948888228551)
        ·
          refine ⟨42113271790664923332342827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28075514527109948888228551 42113271790664923332342827)
          ·
            refine ⟨63169907685997384998514241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42113271790664923332342827 63169907685997384998514241)
            ·
              refine ⟨47377430764498038748885681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63169907685997384998514241 47377430764498038748885681)
              ·
                refine ⟨35533073073373529061664261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47377430764498038748885681 35533073073373529061664261)
                ·
                  refine ⟨6662451201257536699062049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35533073073373529061664261 6662451201257536699062049)
                  ·
                    refine ⟨4996838400943152524296537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6662451201257536699062049 4996838400943152524296537)
                    ·
                      refine ⟨3747628800707364393222403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996838400943152524296537 3747628800707364393222403)
                      ·
                        rfl

theorem cell23_7298481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_7298481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298481 prefixEnd_7298481 := by exact prefixLift 7298481
  have htrace : WordTrace (prefixWord ++ tailWord_7298481) baseStart_7298481 baseEnd_7298481 := by
    simpa [prefixWord, tailWord_7298481, baseEnd_7298481] using wordTrace_append hprefix tailTrace_7298481
  have hstable : (prefixWord ++ tailWord_7298481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298481).length < 2 ^ (prefixWord ++ tailWord_7298481).sum := by decide
  have hdescent : baseEnd_7298481 < baseStart_7298481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298485 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_7298485 : Nat := 118140960795 + 7298485 * 2 ^ 59
def prefixEnd_7298485 : Nat := 4983230072969 + 3 ^ 40 * 7298485 * 2
def baseEnd_7298485 : Nat := 3747630854629982377572385

theorem tailTrace_7298485 : CollatzResearch.WordTrace tailWord_7298485 prefixEnd_7298485 3747630854629982377572385 := by
  unfold tailWord_7298485
  simp only [CollatzResearch.WordTrace]
  refine ⟨266197616963842801845608909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177465077975895201230405939 266197616963842801845608909)
  ·
    refine ⟨99824106361441050692103341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266197616963842801845608909 99824106361441050692103341)
    ·
      refine ⟨37434039885540394009538753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99824106361441050692103341 37434039885540394009538753)
      ·
        refine ⟨28075529914155295507154065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37434039885540394009538753 28075529914155295507154065)
        ·
          refine ⟨21056647435616471630365549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28075529914155295507154065 21056647435616471630365549)
          ·
            refine ⟨7896242788356176861387081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21056647435616471630365549 7896242788356176861387081)
            ·
              refine ⟨5922182091267132646040311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896242788356176861387081 5922182091267132646040311)
              ·
                refine ⟨8883273136900698969060467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922182091267132646040311 8883273136900698969060467)
                ·
                  refine ⟨13324909705351048453590701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8883273136900698969060467 13324909705351048453590701)
                  ·
                    refine ⟨4996841139506643170096513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13324909705351048453590701 4996841139506643170096513)
                    ·
                      refine ⟨3747630854629982377572385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996841139506643170096513 3747630854629982377572385)
                      ·
                        rfl

theorem cell23_7298485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_7298485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298485 prefixEnd_7298485 := by exact prefixLift 7298485
  have htrace : WordTrace (prefixWord ++ tailWord_7298485) baseStart_7298485 baseEnd_7298485 := by
    simpa [prefixWord, tailWord_7298485, baseEnd_7298485] using wordTrace_append hprefix tailTrace_7298485
  have hstable : (prefixWord ++ tailWord_7298485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298485).length < 2 ^ (prefixWord ++ tailWord_7298485).sum := by decide
  have hdescent : baseEnd_7298485 < baseStart_7298485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298504 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 5]
def baseStart_7298504 : Nat := 118140960795 + 7298504 * 2 ^ 59
def prefixEnd_7298504 : Nat := 4983230072969 + 3 ^ 40 * 7298504 * 2
def baseEnd_7298504 : Nat := 416404512306935311470533

theorem tailTrace_7298504 : CollatzResearch.WordTrace tailWord_7298504 prefixEnd_7298504 416404512306935311470533 := by
  unfold tailWord_7298504
  simp only [CollatzResearch.WordTrace]
  refine ⟨133099154975386984045275283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177465539967182645393700377 133099154975386984045275283)
  ·
    refine ⟨199648732463080476067912925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133099154975386984045275283 199648732463080476067912925)
    ·
      refine ⟨74868274673655178525467347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199648732463080476067912925 74868274673655178525467347)
      ·
        refine ⟨112302412010482767788201021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74868274673655178525467347 112302412010482767788201021)
        ·
          refine ⟨42113404503931037920575383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112302412010482767788201021 42113404503931037920575383)
          ·
            refine ⟨63170106755896556880863075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42113404503931037920575383 63170106755896556880863075)
            ·
              refine ⟨94755160133844835321294613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63170106755896556880863075 94755160133844835321294613)
              ·
                refine ⟨4441648131273976655685685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94755160133844835321294613 4441648131273976655685685)
                ·
                  refine ⟨416404512306935311470533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4441648131273976655685685 416404512306935311470533)
                  ·
                    rfl

theorem cell23_7298504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 5].length) (baseStart_7298504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298504 prefixEnd_7298504 := by exact prefixLift 7298504
  have htrace : WordTrace (prefixWord ++ tailWord_7298504) baseStart_7298504 baseEnd_7298504 := by
    simpa [prefixWord, tailWord_7298504, baseEnd_7298504] using wordTrace_append hprefix tailTrace_7298504
  have hstable : (prefixWord ++ tailWord_7298504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298504).length < 2 ^ (prefixWord ++ tailWord_7298504).sum := by decide
  have hdescent : baseEnd_7298504 < baseStart_7298504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298517 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_7298517 : Nat := 118140960795 + 7298517 * 2 ^ 59
def prefixEnd_7298517 : Nat := 4983230072969 + 3 ^ 40 * 7298517 * 2
def baseEnd_7298517 : Nat := 1249215762003642084124079

theorem tailTrace_7298517 : CollatzResearch.WordTrace tailWord_7298517 prefixEnd_7298517 1249215762003642084124079 := by
  unfold tailWord_7298517
  simp only [CollatzResearch.WordTrace]
  refine ⟨266198784099726871310773805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177465856066484580873849203 266198784099726871310773805)
  ·
    refine ⟨99824544037397576741540177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266198784099726871310773805 99824544037397576741540177)
    ·
      refine ⟨74868408028048182556155133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99824544037397576741540177 74868408028048182556155133)
      ·
        refine ⟨28075653010518068458558175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74868408028048182556155133 28075653010518068458558175)
        ·
          refine ⟨42113479515777102687837263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28075653010518068458558175 42113479515777102687837263)
          ·
            refine ⟨63170219273665654031755895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42113479515777102687837263 63170219273665654031755895)
            ·
              refine ⟨94755328910498481047633843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63170219273665654031755895 94755328910498481047633843)
              ·
                refine ⟨142132993365747721571450765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94755328910498481047633843 142132993365747721571450765)
                ·
                  refine ⟨53299872512155395589294037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142132993365747721571450765 53299872512155395589294037)
                  ·
                    refine ⟨1249215762003642084124079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53299872512155395589294037 1249215762003642084124079)
                    ·
                      rfl

theorem cell23_7298517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_7298517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298517 prefixEnd_7298517 := by exact prefixLift 7298517
  have htrace : WordTrace (prefixWord ++ tailWord_7298517) baseStart_7298517 baseEnd_7298517 := by
    simpa [prefixWord, tailWord_7298517, baseEnd_7298517] using wordTrace_append hprefix tailTrace_7298517
  have hstable : (prefixWord ++ tailWord_7298517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298517).length < 2 ^ (prefixWord ++ tailWord_7298517).sum := by decide
  have hdescent : baseEnd_7298517 < baseStart_7298517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298538 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_7298538 : Nat := 118140960795 + 7298538 * 2 ^ 59
def prefixEnd_7298538 : Nat := 4983230072969 + 3 ^ 40 * 7298538 * 2
def baseEnd_7298538 : Nat := 416406452122741185578849

theorem tailTrace_7298538 : CollatzResearch.WordTrace tailWord_7298538 prefixEnd_7298538 416406452122741185578849 := by
  unfold tailWord_7298538
  simp only [CollatzResearch.WordTrace]
  refine ⟨66549887508162697974322067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177466366688433861264858845 66549887508162697974322067)
  ·
    refine ⟨99824831262244046961483101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66549887508162697974322067 99824831262244046961483101)
    ·
      refine ⟨37434311723341517610556163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99824831262244046961483101 37434311723341517610556163)
      ·
        refine ⟨56151467585012276415834245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37434311723341517610556163 56151467585012276415834245)
        ·
          refine ⟨10528400172189801827968921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56151467585012276415834245 10528400172189801827968921)
          ·
            refine ⟨7896300129142351370976691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10528400172189801827968921 7896300129142351370976691)
            ·
              refine ⟨11844450193713527056465037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7896300129142351370976691 11844450193713527056465037)
              ·
                refine ⟨4441668822642572646174389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11844450193713527056465037 4441668822642572646174389)
                ·
                  refine ⟨416406452122741185578849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4441668822642572646174389 416406452122741185578849)
                  ·
                    rfl

theorem cell23_7298538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_7298538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298538 prefixEnd_7298538 := by exact prefixLift 7298538
  have htrace : WordTrace (prefixWord ++ tailWord_7298538) baseStart_7298538 baseEnd_7298538 := by
    simpa [prefixWord, tailWord_7298538, baseEnd_7298538] using wordTrace_append hprefix tailTrace_7298538
  have hstable : (prefixWord ++ tailWord_7298538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298538).length < 2 ^ (prefixWord ++ tailWord_7298538).sum := by decide
  have hdescent : baseEnd_7298538 < baseStart_7298538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298554 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_7298554 : Nat := 118140960795 + 7298554 * 2 ^ 59
def prefixEnd_7298554 : Nat := 4983230072969 + 3 ^ 40 * 7298554 * 2
def baseEnd_7298554 : Nat := 3747666284795142607609567

theorem tailTrace_7298554 : CollatzResearch.WordTrace tailWord_7298554 prefixEnd_7298554 3747666284795142607609567 := by
  unfold tailWord_7298554
  simp only [CollatzResearch.WordTrace]
  refine ⟨66550033400148206657467679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177466755733728551086580477 66550033400148206657467679)
  ·
    refine ⟨99825050100222309986201519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66550033400148206657467679 99825050100222309986201519)
    ·
      refine ⟨149737575150333464979302279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99825050100222309986201519 149737575150333464979302279)
      ·
        refine ⟨224606362725500197468953419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149737575150333464979302279 224606362725500197468953419)
        ·
          refine ⟨336909544088250296203430129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224606362725500197468953419 336909544088250296203430129)
          ·
            refine ⟨252682158066187722152572597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336909544088250296203430129 252682158066187722152572597)
            ·
              refine ⟨23688952318705098951803681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252682158066187722152572597 23688952318705098951803681)
              ·
                refine ⟨17766714239028824213852761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23688952318705098951803681 17766714239028824213852761)
                ·
                  refine ⟨13325035679271618160389571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17766714239028824213852761 13325035679271618160389571)
                  ·
                    refine ⟨19987553518907427240584357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13325035679271618160389571 19987553518907427240584357)
                    ·
                      refine ⟨3747666284795142607609567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19987553518907427240584357 3747666284795142607609567)
                      ·
                        rfl

theorem cell23_7298554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_7298554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298554 prefixEnd_7298554 := by exact prefixLift 7298554
  have htrace : WordTrace (prefixWord ++ tailWord_7298554) baseStart_7298554 baseEnd_7298554 := by
    simpa [prefixWord, tailWord_7298554, baseEnd_7298554] using wordTrace_append hprefix tailTrace_7298554
  have hstable : (prefixWord ++ tailWord_7298554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298554).length < 2 ^ (prefixWord ++ tailWord_7298554).sum := by decide
  have hdescent : baseEnd_7298554 < baseStart_7298554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298597 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_7298597 : Nat := 118140960795 + 7298597 * 2 ^ 59
def prefixEnd_7298597 : Nat := 4983230072969 + 3 ^ 40 * 7298597 * 2
def baseEnd_7298597 : Nat := 3747688364463285939371869

theorem tailTrace_7298597 : CollatzResearch.WordTrace tailWord_7298597 prefixEnd_7298597 3747688364463285939371869 := by
  unfold tailWord_7298597
  simp only [CollatzResearch.WordTrace]
  refine ⟨266201701939437044973686045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177467801292958029982457363 266201701939437044973686045)
  ·
    refine ⟨99825638227288891865132267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266201701939437044973686045 99825638227288891865132267)
    ·
      refine ⟨149738457340933337797698401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99825638227288891865132267 149738457340933337797698401)
      ·
        refine ⟨112303843005700003348273801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149738457340933337797698401 112303843005700003348273801)
        ·
          refine ⟨84227882254275002511205351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112303843005700003348273801 84227882254275002511205351)
          ·
            refine ⟨126341823381412503766808027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84227882254275002511205351 126341823381412503766808027)
            ·
              refine ⟨189512735072118755650212041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126341823381412503766808027 189512735072118755650212041)
              ·
                refine ⟨142134551304089066737659031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189512735072118755650212041 142134551304089066737659031)
                ·
                  refine ⟨213201826956133600106488547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142134551304089066737659031 213201826956133600106488547)
                  ·
                    refine ⟨319802740434200400159732821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213201826956133600106488547 319802740434200400159732821)
                    ·
                      refine ⟨3747688364463285939371869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319802740434200400159732821 3747688364463285939371869)
                      ·
                        rfl

theorem cell23_7298597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_7298597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298597 prefixEnd_7298597 := by exact prefixLift 7298597
  have htrace : WordTrace (prefixWord ++ tailWord_7298597) baseStart_7298597 baseEnd_7298597 := by
    simpa [prefixWord, tailWord_7298597, baseEnd_7298597] using wordTrace_append hprefix tailTrace_7298597
  have hstable : (prefixWord ++ tailWord_7298597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298597).length < 2 ^ (prefixWord ++ tailWord_7298597).sum := by decide
  have hdescent : baseEnd_7298597 < baseStart_7298597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298615 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 1, 4]
def baseStart_7298615 : Nat := 118140960795 + 7298615 * 2 ^ 59
def prefixEnd_7298615 : Nat := 4983230072969 + 3 ^ 40 * 7298615 * 2
def baseEnd_7298615 : Nat := 1249232535705022289648929

theorem tailTrace_7298615 : CollatzResearch.WordTrace tailWord_7298615 prefixEnd_7298615 1249232535705022289648929 := by
  unfold tailWord_7298615
  simp only [CollatzResearch.WordTrace]
  refine ⟨266202358453371834047841299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177468238968914556031894199 266202358453371834047841299)
  ·
    refine ⟨399303537680057751071761949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266202358453371834047841299 399303537680057751071761949)
    ·
      refine ⟨149738826630021656651910731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399303537680057751071761949 149738826630021656651910731)
      ·
        refine ⟨224608239945032484977866097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149738826630021656651910731 224608239945032484977866097)
        ·
          refine ⟨168456179958774363733399573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224608239945032484977866097 168456179958774363733399573)
          ·
            refine ⟨7896383435567548300003105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168456179958774363733399573 7896383435567548300003105)
            ·
              refine ⟨5922287576675661225002329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896383435567548300003105 5922287576675661225002329)
              ·
                refine ⟨4441715682506745918751747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5922287576675661225002329 4441715682506745918751747)
                ·
                  refine ⟨6662573523760118878127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441715682506745918751747 6662573523760118878127621)
                  ·
                    refine ⟨1249232535705022289648929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6662573523760118878127621 1249232535705022289648929)
                    ·
                      rfl

theorem cell23_7298615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_7298615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298615 prefixEnd_7298615 := by exact prefixLift 7298615
  have htrace : WordTrace (prefixWord ++ tailWord_7298615) baseStart_7298615 baseEnd_7298615 := by
    simpa [prefixWord, tailWord_7298615, baseEnd_7298615] using wordTrace_append hprefix tailTrace_7298615
  have hstable : (prefixWord ++ tailWord_7298615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298615).length < 2 ^ (prefixWord ++ tailWord_7298615).sum := by decide
  have hdescent : baseEnd_7298615 < baseStart_7298615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298688 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 2, 4]
def baseStart_7298688 : Nat := 118140960795 + 7298688 * 2 ^ 59
def prefixEnd_7298688 : Nat := 4983230072969 + 3 ^ 40 * 7298688 * 2
def baseEnd_7298688 : Nat := 1249245030400948361111317

theorem tailTrace_7298688 : CollatzResearch.WordTrace tailWord_7298688 prefixEnd_7298688 1249245030400948361111317 := by
  unfold tailWord_7298688
  simp only [CollatzResearch.WordTrace]
  refine ⟨133102510491053683757624359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177470013988071578343499145 133102510491053683757624359)
  ·
    refine ⟨199653765736580525636436539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133102510491053683757624359 199653765736580525636436539)
    ·
      refine ⟨299480648604870788454654809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199653765736580525636436539 299480648604870788454654809)
      ·
        refine ⟨224610486453653091340991107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299480648604870788454654809 224610486453653091340991107)
        ·
          refine ⟨336915729680479637011486661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224610486453653091340991107 336915729680479637011486661)
          ·
            refine ⟨63171699315089931939653749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336915729680479637011486661 63171699315089931939653749)
            ·
              refine ⟨5922346810789681119342539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63171699315089931939653749 5922346810789681119342539)
              ·
                refine ⟨8883520216184521679013809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922346810789681119342539 8883520216184521679013809)
                ·
                  refine ⟨6662640162138391259260357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8883520216184521679013809 6662640162138391259260357)
                  ·
                    refine ⟨1249245030400948361111317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6662640162138391259260357 1249245030400948361111317)
                    ·
                      rfl

theorem cell23_7298688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 4].length) (baseStart_7298688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298688 prefixEnd_7298688 := by exact prefixLift 7298688
  have htrace : WordTrace (prefixWord ++ tailWord_7298688) baseStart_7298688 baseEnd_7298688 := by
    simpa [prefixWord, tailWord_7298688, baseEnd_7298688] using wordTrace_append hprefix tailTrace_7298688
  have hstable : (prefixWord ++ tailWord_7298688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298688).length < 2 ^ (prefixWord ++ tailWord_7298688).sum := by decide
  have hdescent : baseEnd_7298688 < baseStart_7298688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298698 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_7298698 : Nat := 118140960795 + 7298698 * 2 ^ 59
def prefixEnd_7298698 : Nat := 4983230072969 + 3 ^ 40 * 7298698 * 2
def baseEnd_7298698 : Nat := 3747740226009390044208905

theorem tailTrace_7298698 : CollatzResearch.WordTrace tailWord_7298698 prefixEnd_7298698 3747740226009390044208905 := by
  unfold tailWord_7298698
  simp only [CollatzResearch.WordTrace]
  refine ⟨66551346428017784805778187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177470257141380759482075165 66551346428017784805778187)
  ·
    refine ⟨99827019642026677208667281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66551346428017784805778187 99827019642026677208667281)
    ·
      refine ⟨74870264731520007906500461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99827019642026677208667281 74870264731520007906500461)
      ·
        refine ⟨28076349274320002964937673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74870264731520007906500461 28076349274320002964937673)
        ·
          refine ⟨21057261955740002223703255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28076349274320002964937673 21057261955740002223703255)
          ·
            refine ⟨31585892933610003335554883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21057261955740002223703255 31585892933610003335554883)
            ·
              refine ⟨47378839400415005003332325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31585892933610003335554883 47378839400415005003332325)
              ·
                refine ⟨8883532387577813438124811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47378839400415005003332325 8883532387577813438124811)
                ·
                  refine ⟨13325298581366720157187217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8883532387577813438124811 13325298581366720157187217)
                  ·
                    refine ⟨9993973936025040117890413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13325298581366720157187217 9993973936025040117890413)
                    ·
                      refine ⟨3747740226009390044208905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9993973936025040117890413 3747740226009390044208905)
                      ·
                        rfl

theorem cell23_7298698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_7298698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298698 prefixEnd_7298698 := by exact prefixLift 7298698
  have htrace : WordTrace (prefixWord ++ tailWord_7298698) baseStart_7298698 baseEnd_7298698 := by
    simpa [prefixWord, tailWord_7298698, baseEnd_7298698] using wordTrace_append hprefix tailTrace_7298698
  have hstable : (prefixWord ++ tailWord_7298698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298698).length < 2 ^ (prefixWord ++ tailWord_7298698).sum := by decide
  have hdescent : baseEnd_7298698 < baseStart_7298698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298712 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7298712 : Nat := 118140960795 + 7298712 * 2 ^ 59
def prefixEnd_7298712 : Nat := 4983230072969 + 3 ^ 40 * 7298712 * 2
def baseEnd_7298712 : Nat := 3747747414738552989433841

theorem tailTrace_7298712 : CollatzResearch.WordTrace tailWord_7298712 prefixEnd_7298712 3747747414738552989433841 := by
  unfold tailWord_7298712
  simp only [CollatzResearch.WordTrace]
  refine ⟨133102948167010209807061195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177470597556013613076081593 133102948167010209807061195)
  ·
    refine ⟨199654422250515314710591793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133102948167010209807061195 199654422250515314710591793)
    ·
      refine ⟨149740816687886486032943845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199654422250515314710591793 149740816687886486032943845)
      ·
        refine ⟨28076403128978716131176971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149740816687886486032943845 28076403128978716131176971)
        ·
          refine ⟨42114604693468074196765457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28076403128978716131176971 42114604693468074196765457)
          ·
            refine ⟨31585953520101055647574093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42114604693468074196765457 31585953520101055647574093)
            ·
              refine ⟨11844732570037895867840285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31585953520101055647574093 11844732570037895867840285)
              ·
                refine ⟨4441774713764210950440107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11844732570037895867840285 4441774713764210950440107)
                ·
                  refine ⟨6662662070646316425660161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441774713764210950440107 6662662070646316425660161)
                  ·
                    refine ⟨4996996552984737319245121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6662662070646316425660161 4996996552984737319245121)
                    ·
                      refine ⟨3747747414738552989433841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4996996552984737319245121 3747747414738552989433841)
                      ·
                        rfl

theorem cell23_7298712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7298712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298712 prefixEnd_7298712 := by exact prefixLift 7298712
  have htrace : WordTrace (prefixWord ++ tailWord_7298712) baseStart_7298712 baseEnd_7298712 := by
    simpa [prefixWord, tailWord_7298712, baseEnd_7298712] using wordTrace_append hprefix tailTrace_7298712
  have hstable : (prefixWord ++ tailWord_7298712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298712).length < 2 ^ (prefixWord ++ tailWord_7298712).sum := by decide
  have hdescent : baseEnd_7298712 < baseStart_7298712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298744 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_7298744 : Nat := 118140960795 + 7298744 * 2 ^ 59
def prefixEnd_7298744 : Nat := 4983230072969 + 3 ^ 40 * 7298744 * 2
def baseEnd_7298744 : Nat := 1249254615373165621411231

theorem tailTrace_7298744 : CollatzResearch.WordTrace tailWord_7298744 prefixEnd_7298744 1249254615373165621411231 := by
  unfold tailWord_7298744
  simp only [CollatzResearch.WordTrace]
  refine ⟨133103531734952244539643643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177471375646602992719524857 133103531734952244539643643)
  ·
    refine ⟨199655297602428366809465465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133103531734952244539643643 199655297602428366809465465)
    ·
      refine ⟨149741473201821275107099099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199655297602428366809465465 149741473201821275107099099)
      ·
        refine ⟨224612209802731912660648649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149741473201821275107099099 224612209802731912660648649)
        ·
          refine ⟨168459157352048934495486487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224612209802731912660648649 168459157352048934495486487)
          ·
            refine ⟨252688736028073401743229731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168459157352048934495486487 252688736028073401743229731)
            ·
              refine ⟨379033104042110102614844597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252688736028073401743229731 379033104042110102614844597)
              ·
                refine ⟨35534353503947822120141681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379033104042110102614844597 35534353503947822120141681)
                ·
                  refine ⟨26650765127960866590106261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35534353503947822120141681 26650765127960866590106261)
                  ·
                    refine ⟨1249254615373165621411231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26650765127960866590106261 1249254615373165621411231)
                    ·
                      rfl

theorem cell23_7298744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_7298744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298744 prefixEnd_7298744 := by exact prefixLift 7298744
  have htrace : WordTrace (prefixWord ++ tailWord_7298744) baseStart_7298744 baseEnd_7298744 := by
    simpa [prefixWord, tailWord_7298744, baseEnd_7298744] using wordTrace_append hprefix tailTrace_7298744
  have hstable : (prefixWord ++ tailWord_7298744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298744).length < 2 ^ (prefixWord ++ tailWord_7298744).sum := by decide
  have hdescent : baseEnd_7298744 < baseStart_7298744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298745 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7298745 : Nat := 118140960795 + 7298745 * 2 ^ 59
def prefixEnd_7298745 : Nat := 4983230072969 + 3 ^ 40 * 7298745 * 2
def baseEnd_7298745 : Nat := 3747764359600151360321189

theorem tailTrace_7298745 : CollatzResearch.WordTrace tailWord_7298745 prefixEnd_7298745 3747764359600151360321189 := by
  unfold tailWord_7298745
  simp only [CollatzResearch.WordTrace]
  refine ⟨266207099942900866250073689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177471399961933910833382459 266207099942900866250073689)
  ·
    refine ⟨199655324957175649687555267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266207099942900866250073689 199655324957175649687555267)
    ·
      refine ⟨299482987435763474531332901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199655324957175649687555267 299482987435763474531332901)
      ·
        refine ⟨56153060144205651474624919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299482987435763474531332901 56153060144205651474624919)
        ·
          refine ⟨84229590216308477211937379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56153060144205651474624919 84229590216308477211937379)
          ·
            refine ⟨126344385324462715817906069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84229590216308477211937379 126344385324462715817906069)
            ·
              refine ⟨5922393062084189803964347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126344385324462715817906069 5922393062084189803964347)
              ·
                refine ⟨8883589593126284705946521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922393062084189803964347 8883589593126284705946521)
                ·
                  refine ⟨6662692194844713529459891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8883589593126284705946521 6662692194844713529459891)
                  ·
                    refine ⟨9994038292267070294189837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6662692194844713529459891 9994038292267070294189837)
                    ·
                      refine ⟨3747764359600151360321189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9994038292267070294189837 3747764359600151360321189)
                      ·
                        rfl

theorem cell23_7298745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7298745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298745 prefixEnd_7298745 := by exact prefixLift 7298745
  have htrace : WordTrace (prefixWord ++ tailWord_7298745) baseStart_7298745 baseEnd_7298745 := by
    simpa [prefixWord, tailWord_7298745, baseEnd_7298745] using wordTrace_append hprefix tailTrace_7298745
  have hstable : (prefixWord ++ tailWord_7298745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298745).length < 2 ^ (prefixWord ++ tailWord_7298745).sum := by decide
  have hdescent : baseEnd_7298745 < baseStart_7298745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298768 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 4, 2, 2]
def baseStart_7298768 : Nat := 118140960795 + 7298768 * 2 ^ 59
def prefixEnd_7298768 : Nat := 4983230072969 + 3 ^ 40 * 7298768 * 2
def baseEnd_7298768 : Nat := 3747776169655204770333583

theorem tailTrace_7298768 : CollatzResearch.WordTrace tailWord_7298768 prefixEnd_7298768 3747776169655204770333583 := by
  unfold tailWord_7298768
  simp only [CollatzResearch.WordTrace]
  refine ⟨133103969410908770589080479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177471959214545027452107305 133103969410908770589080479)
  ·
    refine ⟨199655954116363155883620719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133103969410908770589080479 199655954116363155883620719)
    ·
      refine ⟨299483931174544733825431079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199655954116363155883620719 299483931174544733825431079)
      ·
        refine ⟨449225896761817100738146619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299483931174544733825431079 449225896761817100738146619)
        ·
          refine ⟨673838845142725651107219929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449225896761817100738146619 673838845142725651107219929)
          ·
            refine ⟨505379133857044238330414947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673838845142725651107219929 505379133857044238330414947)
            ·
              refine ⟨758068700785566357495622421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505379133857044238330414947 758068700785566357495622421)
              ·
                refine ⟨35534470349323423007607301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 758068700785566357495622421 35534470349323423007607301)
                ·
                  refine ⟨6662713190498141813926369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35534470349323423007607301 6662713190498141813926369)
                  ·
                    refine ⟨4997034892873606360444777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6662713190498141813926369 4997034892873606360444777)
                    ·
                      refine ⟨3747776169655204770333583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997034892873606360444777 3747776169655204770333583)
                      ·
                        rfl

theorem cell23_7298768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 2, 2].length) (baseStart_7298768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298768 prefixEnd_7298768 := by exact prefixLift 7298768
  have htrace : WordTrace (prefixWord ++ tailWord_7298768) baseStart_7298768 baseEnd_7298768 := by
    simpa [prefixWord, tailWord_7298768, baseEnd_7298768] using wordTrace_append hprefix tailTrace_7298768
  have hstable : (prefixWord ++ tailWord_7298768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298768).length < 2 ^ (prefixWord ++ tailWord_7298768).sum := by decide
  have hdescent : baseEnd_7298768 < baseStart_7298768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298784 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_7298784 : Nat := 118140960795 + 7298784 * 2 ^ 59
def prefixEnd_7298784 : Nat := 4983230072969 + 3 ^ 40 * 7298784 * 2
def baseEnd_7298784 : Nat := 3747784385345676707733509

theorem tailTrace_7298784 : CollatzResearch.WordTrace tailWord_7298784 prefixEnd_7298784 3747784385345676707733509 := by
  unfold tailWord_7298784
  simp only [CollatzResearch.WordTrace]
  refine ⟨133104261194879787955371703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177472348259839717273828937 133104261194879787955371703)
  ·
    refine ⟨199656391792319681933057555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133104261194879787955371703 199656391792319681933057555)
    ·
      refine ⟨299484587688479522899586333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199656391792319681933057555 299484587688479522899586333)
      ·
        refine ⟨112306720383179821087344875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299484587688479522899586333 112306720383179821087344875)
        ·
          refine ⟨168460080574769731631017313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112306720383179821087344875 168460080574769731631017313)
          ·
            refine ⟨126345060431077298723262985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168460080574769731631017313 126345060431077298723262985)
            ·
              refine ⟨94758795323307974042447239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126345060431077298723262985 94758795323307974042447239)
              ·
                refine ⟨142138192984961961063670859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94758795323307974042447239 142138192984961961063670859)
                ·
                  refine ⟨213207289477442941595506289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142138192984961961063670859 213207289477442941595506289)
                  ·
                    refine ⟨159905467108082206196629717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213207289477442941595506289 159905467108082206196629717)
                    ·
                      refine ⟨3747784385345676707733509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159905467108082206196629717 3747784385345676707733509)
                      ·
                        rfl

theorem cell23_7298784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_7298784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298784 prefixEnd_7298784 := by exact prefixLift 7298784
  have htrace : WordTrace (prefixWord ++ tailWord_7298784) baseStart_7298784 baseEnd_7298784 := by
    simpa [prefixWord, tailWord_7298784, baseEnd_7298784] using wordTrace_append hprefix tailTrace_7298784
  have hstable : (prefixWord ++ tailWord_7298784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298784).length < 2 ^ (prefixWord ++ tailWord_7298784).sum := by decide
  have hdescent : baseEnd_7298784 < baseStart_7298784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298801 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_7298801 : Nat := 118140960795 + 7298801 * 2 ^ 59
def prefixEnd_7298801 : Nat := 4983230072969 + 3 ^ 40 * 7298801 * 2
def baseEnd_7298801 : Nat := 3747793114516803141220931

theorem tailTrace_7298801 : CollatzResearch.WordTrace tailWord_7298801 prefixEnd_7298801 3747793114516803141220931 := by
  unfold tailWord_7298801
  simp only [CollatzResearch.WordTrace]
  refine ⟨266209142430697987814112257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177472761620465325209408171 266209142430697987814112257)
  ·
    refine ⟨199656856823023490860584193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266209142430697987814112257 199656856823023490860584193)
    ·
      refine ⟨149742642617267618145438145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199656856823023490860584193 149742642617267618145438145)
      ·
        refine ⟨112306981962950713609078609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149742642617267618145438145 112306981962950713609078609)
        ·
          refine ⟨84230236472213035206808957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112306981962950713609078609 84230236472213035206808957)
          ·
            refine ⟨31586338677079888202553359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84230236472213035206808957 31586338677079888202553359)
            ·
              refine ⟨47379508015619832303830039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31586338677079888202553359 47379508015619832303830039)
              ·
                refine ⟨71069262023429748455745059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47379508015619832303830039 71069262023429748455745059)
                ·
                  refine ⟨106603893035144622683617589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71069262023429748455745059 106603893035144622683617589)
                  ·
                    refine ⟨9994114972044808376589149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106603893035144622683617589 9994114972044808376589149)
                    ·
                      refine ⟨3747793114516803141220931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9994114972044808376589149 3747793114516803141220931)
                      ·
                        rfl

theorem cell23_7298801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_7298801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298801 prefixEnd_7298801 := by exact prefixLift 7298801
  have htrace : WordTrace (prefixWord ++ tailWord_7298801) baseStart_7298801 baseEnd_7298801 := by
    simpa [prefixWord, tailWord_7298801, baseEnd_7298801] using wordTrace_append hprefix tailTrace_7298801
  have hstable : (prefixWord ++ tailWord_7298801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298801).length < 2 ^ (prefixWord ++ tailWord_7298801).sum := by decide
  have hdescent : baseEnd_7298801 < baseStart_7298801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298818 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7298818 : Nat := 118140960795 + 7298818 * 2 ^ 59
def prefixEnd_7298818 : Nat := 4983230072969 + 3 ^ 40 * 7298818 * 2
def baseEnd_7298818 : Nat := 3747801843687929574708353

theorem tailTrace_7298818 : CollatzResearch.WordTrace tailWord_7298818 prefixEnd_7298818 3747801843687929574708353 := by
  unfold tailWord_7298818
  simp only [CollatzResearch.WordTrace]
  refine ⟨66552440617909099929370277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177473174981090933144987405 66552440617909099929370277)
  ·
    refine ⟨12478582615857956236756927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66552440617909099929370277 12478582615857956236756927)
    ·
      refine ⟨18717873923786934355135391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12478582615857956236756927 18717873923786934355135391)
      ·
        refine ⟨28076810885680401532703087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18717873923786934355135391 28076810885680401532703087)
        ·
          refine ⟨42115216328520602299054631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28076810885680401532703087 42115216328520602299054631)
          ·
            refine ⟨63172824492780903448581947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42115216328520602299054631 63172824492780903448581947)
            ·
              refine ⟨94759236739171355172872921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63172824492780903448581947 94759236739171355172872921)
              ·
                refine ⟨71069427554378516379654691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94759236739171355172872921 71069427554378516379654691)
                ·
                  refine ⟨106604141331567774569482037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71069427554378516379654691 106604141331567774569482037)
                  ·
                    refine ⟨9994138249834478865888941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106604141331567774569482037 9994138249834478865888941)
                    ·
                      refine ⟨3747801843687929574708353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9994138249834478865888941 3747801843687929574708353)
                      ·
                        rfl

theorem cell23_7298818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7298818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298818 prefixEnd_7298818 := by exact prefixLift 7298818
  have htrace : WordTrace (prefixWord ++ tailWord_7298818) baseStart_7298818 baseEnd_7298818 := by
    simpa [prefixWord, tailWord_7298818, baseEnd_7298818] using wordTrace_append hprefix tailTrace_7298818
  have hstable : (prefixWord ++ tailWord_7298818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298818).length < 2 ^ (prefixWord ++ tailWord_7298818).sum := by decide
  have hdescent : baseEnd_7298818 < baseStart_7298818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298836 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7298836 : Nat := 118140960795 + 7298836 * 2 ^ 59
def prefixEnd_7298836 : Nat := 4983230072969 + 3 ^ 40 * 7298836 * 2
def baseEnd_7298836 : Nat := 3747811086339710504283271

theorem tailTrace_7298836 : CollatzResearch.WordTrace tailWord_7298836 prefixEnd_7298836 3747811086339710504283271 := by
  unfold tailWord_7298836
  simp only [CollatzResearch.WordTrace]
  refine ⟨133105209492785594395818181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177473612657047459194424241 133105209492785594395818181)
  ·
    refine ⟨24957226779897298949215909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133105209492785594395818181 24957226779897298949215909)
    ·
      refine ⟨4679480021230743552977983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24957226779897298949215909 4679480021230743552977983)
      ·
        refine ⟨7019220031846115329466975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4679480021230743552977983 7019220031846115329466975)
        ·
          refine ⟨10528830047769172994200463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7019220031846115329466975 10528830047769172994200463)
          ·
            refine ⟨15793245071653759491300695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10528830047769172994200463 15793245071653759491300695)
            ·
              refine ⟨23689867607480639236951043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15793245071653759491300695 23689867607480639236951043)
              ·
                refine ⟨35534801411220958855426565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23689867607480639236951043 35534801411220958855426565)
                ·
                  refine ⟨6662775264603929785392481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35534801411220958855426565 6662775264603929785392481)
                  ·
                    refine ⟨4997081448452947339044361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6662775264603929785392481 4997081448452947339044361)
                    ·
                      refine ⟨3747811086339710504283271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997081448452947339044361 3747811086339710504283271)
                      ·
                        rfl

theorem cell23_7298836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7298836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298836 prefixEnd_7298836 := by exact prefixLift 7298836
  have htrace : WordTrace (prefixWord ++ tailWord_7298836) baseStart_7298836 baseEnd_7298836 := by
    simpa [prefixWord, tailWord_7298836, baseEnd_7298836] using wordTrace_append hprefix tailTrace_7298836
  have hstable : (prefixWord ++ tailWord_7298836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298836).length < 2 ^ (prefixWord ++ tailWord_7298836).sum := by decide
  have hdescent : baseEnd_7298836 < baseStart_7298836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298925 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7298925 : Nat := 118140960795 + 7298925 * 2 ^ 59
def prefixEnd_7298925 : Nat := 4983230072969 + 3 ^ 40 * 7298925 * 2
def baseEnd_7298925 : Nat := 3747856786117960656070361

theorem tailTrace_7298925 : CollatzResearch.WordTrace tailWord_7298925 prefixEnd_7298925 3747856786117960656070361 := by
  unfold tailWord_7298925
  simp only [CollatzResearch.WordTrace]
  refine ⟨266213665082248756991626229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177475776721499171327750819 266213665082248756991626229)
  ·
    refine ⟨24957531101460820967964959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266213665082248756991626229 24957531101460820967964959)
    ·
      refine ⟨37436296652191231451947439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24957531101460820967964959 37436296652191231451947439)
      ·
        refine ⟨56154444978286847177921159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37436296652191231451947439 56154444978286847177921159)
        ·
          refine ⟨84231667467430270766881739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56154444978286847177921159 84231667467430270766881739)
          ·
            refine ⟨126347501201145406150322609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84231667467430270766881739 126347501201145406150322609)
            ·
              refine ⟨94760625900859054612741957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126347501201145406150322609 94760625900859054612741957)
              ·
                refine ⟨17767617356411072739889117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94760625900859054612741957 17767617356411072739889117)
                ·
                  refine ⟨6662856508654152277458419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17767617356411072739889117 6662856508654152277458419)
                  ·
                    refine ⟨9994284762981228416187629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6662856508654152277458419 9994284762981228416187629)
                    ·
                      refine ⟨3747856786117960656070361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9994284762981228416187629 3747856786117960656070361)
                      ·
                        rfl

theorem cell23_7298925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7298925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298925 prefixEnd_7298925 := by exact prefixLift 7298925
  have htrace : WordTrace (prefixWord ++ tailWord_7298925) baseStart_7298925 baseEnd_7298925 := by
    simpa [prefixWord, tailWord_7298925, baseEnd_7298925] using wordTrace_append hprefix tailTrace_7298925
  have hstable : (prefixWord ++ tailWord_7298925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298925).length < 2 ^ (prefixWord ++ tailWord_7298925).sum := by decide
  have hdescent : baseEnd_7298925 < baseStart_7298925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298961 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_7298961 : Nat := 118140960795 + 7298961 * 2 ^ 59
def prefixEnd_7298961 : Nat := 4983230072969 + 3 ^ 40 * 7298961 * 2
def baseEnd_7298961 : Nat := 3747875271421522515220195

theorem tailTrace_7298961 : CollatzResearch.WordTrace tailWord_7298961 prefixEnd_7298961 3747875271421522515220195 := by
  unfold tailWord_7298961
  simp only [CollatzResearch.WordTrace]
  refine ⟨266214978110118335139936737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177476652073412223426624491 266214978110118335139936737)
  ·
    refine ⟨199661233582588751354952553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266214978110118335139936737 199661233582588751354952553)
    ·
      refine ⟨149745925186941563516214415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199661233582588751354952553 149745925186941563516214415)
      ·
        refine ⟨224618887780412345274321623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149745925186941563516214415 224618887780412345274321623)
        ·
          refine ⟨336928331670618517911482435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224618887780412345274321623 336928331670618517911482435)
          ·
            refine ⟨505392497505927776867223653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336928331670618517911482435 505392497505927776867223653)
            ·
              refine ⟨94761093282361458162604435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 505392497505927776867223653 94761093282361458162604435)
              ·
                refine ⟨142141639923542187243906653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94761093282361458162604435 142141639923542187243906653)
                ·
                  refine ⟨53303114971328320216464995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142141639923542187243906653 53303114971328320216464995)
                  ·
                    refine ⟨79954672456992480324697493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53303114971328320216464995 79954672456992480324697493)
                    ·
                      refine ⟨3747875271421522515220195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79954672456992480324697493 3747875271421522515220195)
                      ·
                        rfl

theorem cell23_7298961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_7298961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298961 prefixEnd_7298961 := by exact prefixLift 7298961
  have htrace : WordTrace (prefixWord ++ tailWord_7298961) baseStart_7298961 baseEnd_7298961 := by
    simpa [prefixWord, tailWord_7298961, baseEnd_7298961] using wordTrace_append hprefix tailTrace_7298961
  have hstable : (prefixWord ++ tailWord_7298961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298961).length < 2 ^ (prefixWord ++ tailWord_7298961).sum := by decide
  have hdescent : baseEnd_7298961 < baseStart_7298961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298975 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 1, 6]
def baseStart_7298975 : Nat := 118140960795 + 7298975 * 2 ^ 59
def prefixEnd_7298975 : Nat := 4983230072969 + 3 ^ 40 * 7298975 * 2
def baseEnd_7298975 : Nat := 1249294153383561820148377

theorem tailTrace_7298975 : CollatzResearch.WordTrace tailWord_7298975 prefixEnd_7298975 1249294153383561820148377 := by
  unfold tailWord_7298975
  simp only [CollatzResearch.WordTrace]
  refine ⟨266215488732067615530946379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177476992488045077020630919 266215488732067615530946379)
  ·
    refine ⟨399323233098101423296419569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266215488732067615530946379 399323233098101423296419569)
    ·
      refine ⟨299492424823576067472314677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399323233098101423296419569 299492424823576067472314677)
      ·
        refine ⟨28077414827210256325529501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299492424823576067472314677 28077414827210256325529501)
        ·
          refine ⟨10529030560203846122073563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28077414827210256325529501 10529030560203846122073563)
          ·
            refine ⟨15793545840305769183110345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529030560203846122073563 15793545840305769183110345)
            ·
              refine ⟨11845159380229326887332759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15793545840305769183110345 11845159380229326887332759)
              ·
                refine ⟨17767739070343990330999139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11845159380229326887332759 17767739070343990330999139)
                ·
                  refine ⟨26651608605515985496498709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17767739070343990330999139 26651608605515985496498709)
                  ·
                    refine ⟨1249294153383561820148377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26651608605515985496498709 1249294153383561820148377)
                    ·
                      rfl

theorem cell23_7298975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_7298975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298975 prefixEnd_7298975 := by exact prefixLift 7298975
  have htrace : WordTrace (prefixWord ++ tailWord_7298975) baseStart_7298975 baseEnd_7298975 := by
    simpa [prefixWord, tailWord_7298975, baseEnd_7298975] using wordTrace_append hprefix tailTrace_7298975
  have hstable : (prefixWord ++ tailWord_7298975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298975).length < 2 ^ (prefixWord ++ tailWord_7298975).sum := by decide
  have hdescent : baseEnd_7298975 < baseStart_7298975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298981 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_7298981 : Nat := 118140960795 + 7298981 * 2 ^ 59
def prefixEnd_7298981 : Nat := 4983230072969 + 3 ^ 40 * 7298981 * 2
def baseEnd_7298981 : Nat := 3747885541034612436970103

theorem tailTrace_7298981 : CollatzResearch.WordTrace tailWord_7298981 prefixEnd_7298981 3747885541034612436970103 := by
  unfold tailWord_7298981
  simp only [CollatzResearch.WordTrace]
  refine ⟨266215707570045878555664797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177477138380030585703776531 266215707570045878555664797)
  ·
    refine ⟨99830890338767204458374299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266215707570045878555664797 99830890338767204458374299)
    ·
      refine ⟨149746335508150806687561449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99830890338767204458374299 149746335508150806687561449)
      ·
        refine ⟨112309751631113105015671087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149746335508150806687561449 112309751631113105015671087)
        ·
          refine ⟨168464627446669657523506631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112309751631113105015671087 168464627446669657523506631)
          ·
            refine ⟨252696941170004486285259947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168464627446669657523506631 252696941170004486285259947)
            ·
              refine ⟨379045411755006729427889921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252696941170004486285259947 379045411755006729427889921)
              ·
                refine ⟨284284058816255047070917441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379045411755006729427889921 284284058816255047070917441)
                ·
                  refine ⟨213213044112191285303188081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284284058816255047070917441 213213044112191285303188081)
                  ·
                    refine ⟨159909783084143463977391061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213213044112191285303188081 159909783084143463977391061)
                    ·
                      refine ⟨3747885541034612436970103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159909783084143463977391061 3747885541034612436970103)
                      ·
                        rfl

theorem cell23_7298981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_7298981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298981 prefixEnd_7298981 := by exact prefixLift 7298981
  have htrace : WordTrace (prefixWord ++ tailWord_7298981) baseStart_7298981 baseEnd_7298981 := by
    simpa [prefixWord, tailWord_7298981, baseEnd_7298981] using wordTrace_append hprefix tailTrace_7298981
  have hstable : (prefixWord ++ tailWord_7298981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298981).length < 2 ^ (prefixWord ++ tailWord_7298981).sum := by decide
  have hdescent : baseEnd_7298981 < baseStart_7298981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7298996 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7298996 : Nat := 118140960795 + 7298996 * 2 ^ 59
def prefixEnd_7298996 : Nat := 4983230072969 + 3 ^ 40 * 7298996 * 2
def baseEnd_7298996 : Nat := 1249297747748143292760845

theorem tailTrace_7298996 : CollatzResearch.WordTrace tailWord_7298996 prefixEnd_7298996 1249297747748143292760845 := by
  unfold tailWord_7298996
  simp only [CollatzResearch.WordTrace]
  refine ⟨133108127332495768058730421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177477503109994357411640561 133108127332495768058730421)
  ·
    refine ⟨12478886937421478255505977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133108127332495768058730421 12478886937421478255505977)
    ·
      refine ⟨9359165203066108691629483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12478886937421478255505977 9359165203066108691629483)
      ·
        refine ⟨14038747804599163037444225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359165203066108691629483 14038747804599163037444225)
        ·
          refine ⟨10529060853449372278083169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14038747804599163037444225 10529060853449372278083169)
          ·
            refine ⟨7896795640087029208562377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10529060853449372278083169 7896795640087029208562377)
            ·
              refine ⟨5922596730065271906421783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896795640087029208562377 5922596730065271906421783)
              ·
                refine ⟨8883895095097907859632675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922596730065271906421783 8883895095097907859632675)
                ·
                  refine ⟨13325842642646861789449013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8883895095097907859632675 13325842642646861789449013)
                  ·
                    refine ⟨1249297747748143292760845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13325842642646861789449013 1249297747748143292760845)
                    ·
                      rfl

theorem cell23_7298996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7298996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7298996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7298996 prefixEnd_7298996 := by exact prefixLift 7298996
  have htrace : WordTrace (prefixWord ++ tailWord_7298996) baseStart_7298996 baseEnd_7298996 := by
    simpa [prefixWord, tailWord_7298996, baseEnd_7298996] using wordTrace_append hprefix tailTrace_7298996
  have hstable : (prefixWord ++ tailWord_7298996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7298996).length < 2 ^ (prefixWord ++ tailWord_7298996).sum := by decide
  have hdescent : baseEnd_7298996 < baseStart_7298996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7298996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299011 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_7299011 : Nat := 118140960795 + 7299011 * 2 ^ 59
def prefixEnd_7299011 : Nat := 4983230072969 + 3 ^ 40 * 7299011 * 2
def baseEnd_7299011 : Nat := 3747900945454247319594965

theorem tailTrace_7299011 : CollatzResearch.WordTrace tailWord_7299011 prefixEnd_7299011 3747900945454247319594965 := by
  unfold tailWord_7299011
  simp only [CollatzResearch.WordTrace]
  refine ⟨266216801759937193679256887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177477867839958129119504591 266216801759937193679256887)
  ·
    refine ⟨399325202639905790518885331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266216801759937193679256887 399325202639905790518885331)
    ·
      refine ⟨598987803959858685778327997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399325202639905790518885331 598987803959858685778327997)
      ·
        refine ⟨224620426484947007166872999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598987803959858685778327997 224620426484947007166872999)
        ·
          refine ⟨336930639727420510750309499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224620426484947007166872999 336930639727420510750309499)
          ·
            refine ⟨505395959591130766125464249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336930639727420510750309499 505395959591130766125464249)
            ·
              refine ⟨379046969693348074594098187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505395959591130766125464249 379046969693348074594098187)
              ·
                refine ⟨568570454540022111891147281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379046969693348074594098187 568570454540022111891147281)
                ·
                  refine ⟨426427840905016583918360461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568570454540022111891147281 426427840905016583918360461)
                  ·
                    refine ⟨159910440339381218969385173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426427840905016583918360461 159910440339381218969385173)
                    ·
                      refine ⟨3747900945454247319594965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159910440339381218969385173 3747900945454247319594965)
                      ·
                        rfl

theorem cell23_7299011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_7299011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299011 prefixEnd_7299011 := by exact prefixLift 7299011
  have htrace : WordTrace (prefixWord ++ tailWord_7299011) baseStart_7299011 baseEnd_7299011 := by
    simpa [prefixWord, tailWord_7299011, baseEnd_7299011] using wordTrace_append hprefix tailTrace_7299011
  have hstable : (prefixWord ++ tailWord_7299011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299011).length < 2 ^ (prefixWord ++ tailWord_7299011).sum := by decide
  have hdescent : baseEnd_7299011 < baseStart_7299011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299025 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 3, 3, 2]
def baseStart_7299025 : Nat := 118140960795 + 7299025 * 2 ^ 59
def prefixEnd_7299025 : Nat := 4983230072969 + 3 ^ 40 * 7299025 * 2
def baseEnd_7299025 : Nat := 3747908134183410264819901

theorem tailTrace_7299025 : CollatzResearch.WordTrace tailWord_7299025 prefixEnd_7299025 3747908134183410264819901 := by
  unfold tailWord_7299025
  simp only [CollatzResearch.WordTrace]
  refine ⟨266217312381886474070266529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177478208254590982713511019 266217312381886474070266529)
  ·
    refine ⟨199662984286414855552699897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266217312381886474070266529 199662984286414855552699897)
    ·
      refine ⟨149747238214811141664524923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199662984286414855552699897 149747238214811141664524923)
      ·
        refine ⟨224620857322216712496787385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149747238214811141664524923 224620857322216712496787385)
        ·
          refine ⟨168465642991662534372590539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224620857322216712496787385 168465642991662534372590539)
          ·
            refine ⟨252698464487493801558885809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168465642991662534372590539 252698464487493801558885809)
            ·
              refine ⟨189523848365620351169164357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252698464487493801558885809 189523848365620351169164357)
              ·
                refine ⟨35535721568553815844218317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189523848365620351169164357 35535721568553815844218317)
                ·
                  refine ⟨13325895588207680941581869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35535721568553815844218317 13325895588207680941581869)
                  ·
                    refine ⟨4997210845577880353093201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13325895588207680941581869 4997210845577880353093201)
                    ·
                      refine ⟨3747908134183410264819901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997210845577880353093201 3747908134183410264819901)
                      ·
                        rfl

theorem cell23_7299025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_7299025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299025 prefixEnd_7299025 := by exact prefixLift 7299025
  have htrace : WordTrace (prefixWord ++ tailWord_7299025) baseStart_7299025 baseEnd_7299025 := by
    simpa [prefixWord, tailWord_7299025, baseEnd_7299025] using wordTrace_append hprefix tailTrace_7299025
  have hstable : (prefixWord ++ tailWord_7299025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299025).length < 2 ^ (prefixWord ++ tailWord_7299025).sum := by decide
  have hdescent : baseEnd_7299025 < baseStart_7299025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299055 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 3, 4, 2]
def baseStart_7299055 : Nat := 118140960795 + 7299055 * 2 ^ 59
def prefixEnd_7299055 : Nat := 4983230072969 + 3 ^ 40 * 7299055 * 2
def baseEnd_7299055 : Nat := 3747923538603045147444763

theorem tailTrace_7299055 : CollatzResearch.WordTrace tailWord_7299055 prefixEnd_7299055 3747923538603045147444763 := by
  unfold tailWord_7299055
  simp only [CollatzResearch.WordTrace]
  refine ⟨266218406571777789193858619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177478937714518526129239079 266218406571777789193858619)
  ·
    refine ⟨399327609857666683790787929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266218406571777789193858619 399327609857666683790787929)
    ·
      refine ⟨299495707393250012843090947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399327609857666683790787929 299495707393250012843090947)
      ·
        refine ⟨449243561089875019264636421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299495707393250012843090947 449243561089875019264636421)
        ·
          refine ⟨84233167704351566112119329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 449243561089875019264636421 84233167704351566112119329)
          ·
            refine ⟨63174875778263674584089497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84233167704351566112119329 63174875778263674584089497)
            ·
              refine ⟨47381156833697755938067123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63174875778263674584089497 47381156833697755938067123)
              ·
                refine ⟨71071735250546633907100685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47381156833697755938067123 71071735250546633907100685)
                ·
                  refine ⟨26651900718954987715162757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71071735250546633907100685 26651900718954987715162757)
                  ·
                    refine ⟨4997231384804060196593017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26651900718954987715162757 4997231384804060196593017)
                    ·
                      refine ⟨3747923538603045147444763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997231384804060196593017 3747923538603045147444763)
                      ·
                        rfl

theorem cell23_7299055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4, 2].length) (baseStart_7299055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299055 prefixEnd_7299055 := by exact prefixLift 7299055
  have htrace : WordTrace (prefixWord ++ tailWord_7299055) baseStart_7299055 baseEnd_7299055 := by
    simpa [prefixWord, tailWord_7299055, baseEnd_7299055] using wordTrace_append hprefix tailTrace_7299055
  have hstable : (prefixWord ++ tailWord_7299055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299055).length < 2 ^ (prefixWord ++ tailWord_7299055).sum := by decide
  have hdescent : baseEnd_7299055 < baseStart_7299055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299125 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_7299125 : Nat := 118140960795 + 7299125 * 2 ^ 59
def prefixEnd_7299125 : Nat := 4983230072969 + 3 ^ 40 * 7299125 * 2
def baseEnd_7299125 : Nat := 1249319827416286624523147

theorem tailTrace_7299125 : CollatzResearch.WordTrace tailWord_7299125 prefixEnd_7299125 1249319827416286624523147 := by
  unfold tailWord_7299125
  simp only [CollatzResearch.WordTrace]
  refine ⟨266220959681524191148906829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177480639787682794099271219 266220959681524191148906829)
  ·
    refine ⟨99832859880571571680840061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266220959681524191148906829 99832859880571571680840061)
    ·
      refine ⟨37437322455214339380315023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99832859880571571680840061 37437322455214339380315023)
      ·
        refine ⟨56155983682821509070472535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37437322455214339380315023 56155983682821509070472535)
        ·
          refine ⟨84233975524232263605708803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56155983682821509070472535 84233975524232263605708803)
          ·
            refine ⟨126350963286348395408563205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84233975524232263605708803 126350963286348395408563205)
            ·
              refine ⟨23690805616190324139105601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126350963286348395408563205 23690805616190324139105601)
              ·
                refine ⟨17768104212142743104329201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23690805616190324139105601 17768104212142743104329201)
                ·
                  refine ⟨13326078159107057328246901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17768104212142743104329201 13326078159107057328246901)
                  ·
                    refine ⟨1249319827416286624523147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13326078159107057328246901 1249319827416286624523147)
                    ·
                      rfl

theorem cell23_7299125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_7299125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299125 prefixEnd_7299125 := by exact prefixLift 7299125
  have htrace : WordTrace (prefixWord ++ tailWord_7299125) baseStart_7299125 baseEnd_7299125 := by
    simpa [prefixWord, tailWord_7299125, baseEnd_7299125] using wordTrace_append hprefix tailTrace_7299125
  have hstable : (prefixWord ++ tailWord_7299125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299125).length < 2 ^ (prefixWord ++ tailWord_7299125).sum := by decide
  have hdescent : baseEnd_7299125 < baseStart_7299125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299142 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_7299142 : Nat := 118140960795 + 7299142 * 2 ^ 59
def prefixEnd_7299142 : Nat := 4983230072969 + 3 ^ 40 * 7299142 * 2
def baseEnd_7299142 : Nat := 1249322737139995435685621

theorem tailTrace_7299142 : CollatzResearch.WordTrace tailWord_7299142 prefixEnd_7299142 1249322737139995435685621 := by
  unfold tailWord_7299142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319424366326956345383615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177481053148308402034850453 8319424366326956345383615)
  ·
    refine ⟨12479136549490434518075423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8319424366326956345383615 12479136549490434518075423)
    ·
      refine ⟨18718704824235651777113135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12479136549490434518075423 18718704824235651777113135)
      ·
        refine ⟨28078057236353477665669703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18718704824235651777113135 28078057236353477665669703)
        ·
          refine ⟨42117085854530216498504555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28078057236353477665669703 42117085854530216498504555)
          ·
            refine ⟨63175628781795324747756833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42117085854530216498504555 63175628781795324747756833)
            ·
              refine ⟨47381721586346493560817625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63175628781795324747756833 47381721586346493560817625)
              ·
                refine ⟨35536291189759870170613219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47381721586346493560817625 35536291189759870170613219)
                ·
                  refine ⟨53304436784639805255919829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35536291189759870170613219 53304436784639805255919829)
                  ·
                    refine ⟨1249322737139995435685621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53304436784639805255919829 1249322737139995435685621)
                    ·
                      rfl

theorem cell23_7299142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_7299142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299142 prefixEnd_7299142 := by exact prefixLift 7299142
  have htrace : WordTrace (prefixWord ++ tailWord_7299142) baseStart_7299142 baseEnd_7299142 := by
    simpa [prefixWord, tailWord_7299142, baseEnd_7299142] using wordTrace_append hprefix tailTrace_7299142
  have hstable : (prefixWord ++ tailWord_7299142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299142).length < 2 ^ (prefixWord ++ tailWord_7299142).sum := by decide
  have hdescent : baseEnd_7299142 < baseStart_7299142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299182 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_7299182 : Nat := 118140960795 + 7299182 * 2 ^ 59
def prefixEnd_7299182 : Nat := 4983230072969 + 3 ^ 40 * 7299182 * 2
def baseEnd_7299182 : Nat := 3747988750646166150556679

theorem tailTrace_7299182 : CollatzResearch.WordTrace tailWord_7299182 prefixEnd_7299182 3747988750646166150556679 := by
  unfold tailWord_7299182
  simp only [CollatzResearch.WordTrace]
  refine ⟨33277879830289711235466475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177482025761545126589154533 33277879830289711235466475)
  ·
    refine ⟨49916819745434566853199713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33277879830289711235466475 49916819745434566853199713)
    ·
      refine ⟨37437614809075925139899785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49916819745434566853199713 37437614809075925139899785)
      ·
        refine ⟨28078211106806943854924839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37437614809075925139899785 28078211106806943854924839)
        ·
          refine ⟨42117316660210415782387259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28078211106806943854924839 42117316660210415782387259)
          ·
            refine ⟨63175974990315623673580889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42117316660210415782387259 63175974990315623673580889)
            ·
              refine ⟨47381981242736717755185667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63175974990315623673580889 47381981242736717755185667)
              ·
                refine ⟨71072971864105076632778501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47381981242736717755185667 71072971864105076632778501)
                ·
                  refine ⟨13326182224519701868645969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71072971864105076632778501 13326182224519701868645969)
                  ·
                    refine ⟨9994636668389776401484477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13326182224519701868645969 9994636668389776401484477)
                    ·
                      refine ⟨3747988750646166150556679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9994636668389776401484477 3747988750646166150556679)
                      ·
                        rfl

theorem cell23_7299182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_7299182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299182 prefixEnd_7299182 := by exact prefixLift 7299182
  have htrace : WordTrace (prefixWord ++ tailWord_7299182) baseStart_7299182 baseEnd_7299182 := by
    simpa [prefixWord, tailWord_7299182, baseEnd_7299182] using wordTrace_append hprefix tailTrace_7299182
  have hstable : (prefixWord ++ tailWord_7299182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299182).length < 2 ^ (prefixWord ++ tailWord_7299182).sum := by decide
  have hdescent : baseEnd_7299182 < baseStart_7299182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299223 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 1, 4]
def baseStart_7299223 : Nat := 118140960795 + 7299223 * 2 ^ 59
def prefixEnd_7299223 : Nat := 4983230072969 + 3 ^ 40 * 7299223 * 2
def baseEnd_7299223 : Nat := 1249336601117666830047997

theorem tailTrace_7299223 : CollatzResearch.WordTrace tailWord_7299223 prefixEnd_7299223 1249336601117666830047997 := by
  unfold tailWord_7299223
  simp only [CollatzResearch.WordTrace]
  refine ⟨266224534035169153885974323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177483022690112769257316215 266224534035169153885974323)
  ·
    refine ⟨399336801052753730828961485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266224534035169153885974323 399336801052753730828961485)
    ·
      refine ⟨149751300394782649060860557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399336801052753730828961485 149751300394782649060860557)
      ·
        refine ⟨56156737648043493397822709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149751300394782649060860557 56156737648043493397822709)
        ·
          refine ⟨5264694154504077506045879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56156737648043493397822709 5264694154504077506045879)
          ·
            refine ⟨7897041231756116259068819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264694154504077506045879 7897041231756116259068819)
            ·
              refine ⟨11845561847634174388603229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897041231756116259068819 11845561847634174388603229)
              ·
                refine ⟨4442085692862815395726211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11845561847634174388603229 4442085692862815395726211)
                ·
                  refine ⟨6663128539294223093589317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442085692862815395726211 6663128539294223093589317)
                  ·
                    refine ⟨1249336601117666830047997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663128539294223093589317 1249336601117666830047997)
                    ·
                      rfl

theorem cell23_7299223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_7299223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299223 prefixEnd_7299223 := by exact prefixLift 7299223
  have htrace : WordTrace (prefixWord ++ tailWord_7299223) baseStart_7299223 baseEnd_7299223 := by
    simpa [prefixWord, tailWord_7299223, baseEnd_7299223] using wordTrace_append hprefix tailTrace_7299223
  have hstable : (prefixWord ++ tailWord_7299223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299223).length < 2 ^ (prefixWord ++ tailWord_7299223).sum := by decide
  have hdescent : baseEnd_7299223 < baseStart_7299223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299232 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 1, 5]
def baseStart_7299232 : Nat := 118140960795 + 7299232 * 2 ^ 59
def prefixEnd_7299232 : Nat := 4983230072969 + 3 ^ 40 * 7299232 * 2
def baseEnd_7299232 : Nat := 1249338141559630318310483

theorem tailTrace_7299232 : CollatzResearch.WordTrace tailWord_7299232 prefixEnd_7299232 1249338141559630318310483 := by
  unfold tailWord_7299232
  simp only [CollatzResearch.WordTrace]
  refine ⟨133112431146068274211525975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177483241528091032282034633 133112431146068274211525975)
  ·
    refine ⟨199668646719102411317288963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133112431146068274211525975 199668646719102411317288963)
    ·
      refine ⟨299502970078653616975933445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199668646719102411317288963 299502970078653616975933445)
      ·
        refine ⟨56156806889747553182987521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299502970078653616975933445 56156806889747553182987521)
        ·
          refine ⟨42117605167310664887240641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56156806889747553182987521 42117605167310664887240641)
          ·
            refine ⟨31588203875482998665430481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42117605167310664887240641 31588203875482998665430481)
            ·
              refine ⟨23691152906612248999072861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31588203875482998665430481 23691152906612248999072861)
              ·
                refine ⟨8884182339979593374652323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23691152906612248999072861 8884182339979593374652323)
                ·
                  refine ⟨13326273509969390061978485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8884182339979593374652323 13326273509969390061978485)
                  ·
                    refine ⟨1249338141559630318310483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13326273509969390061978485 1249338141559630318310483)
                    ·
                      rfl

theorem cell23_7299232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_7299232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299232 prefixEnd_7299232 := by exact prefixLift 7299232
  have htrace : WordTrace (prefixWord ++ tailWord_7299232) baseStart_7299232 baseEnd_7299232 := by
    simpa [prefixWord, tailWord_7299232, baseEnd_7299232] using wordTrace_append hprefix tailTrace_7299232
  have hstable : (prefixWord ++ tailWord_7299232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299232).length < 2 ^ (prefixWord ++ tailWord_7299232).sum := by decide
  have hdescent : baseEnd_7299232 < baseStart_7299232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299235 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 4]
def baseStart_7299235 : Nat := 118140960795 + 7299235 * 2 ^ 59
def prefixEnd_7299235 : Nat := 4983230072969 + 3 ^ 40 * 7299235 * 2
def baseEnd_7299235 : Nat := 3748015965120854443193935

theorem tailTrace_7299235 : CollatzResearch.WordTrace tailWord_7299235 prefixEnd_7299235 3748015965120854443193935 := by
  unfold tailWord_7299235
  simp only [CollatzResearch.WordTrace]
  refine ⟨266224971711125679935411159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177483314474083786623607439 266224971711125679935411159)
  ·
    refine ⟨399337457566688519903116739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266224971711125679935411159 399337457566688519903116739)
    ·
      refine ⟨599006186350032779854675109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399337457566688519903116739 599006186350032779854675109)
      ·
        refine ⟨112313659940631146222751583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599006186350032779854675109 112313659940631146222751583)
        ·
          refine ⟨168470489910946719334127375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112313659940631146222751583 168470489910946719334127375)
          ·
            refine ⟨252705734866420079001191063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168470489910946719334127375 252705734866420079001191063)
            ·
              refine ⟨379058602299630118501786595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252705734866420079001191063 379058602299630118501786595)
              ·
                refine ⟨568587903449445177752679893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379058602299630118501786595 568587903449445177752679893)
                ·
                  refine ⟨13326278987096371353578435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 568587903449445177752679893 13326278987096371353578435)
                  ·
                    refine ⟨19989418480644557030367653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13326278987096371353578435 19989418480644557030367653)
                    ·
                      refine ⟨3748015965120854443193935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19989418480644557030367653 3748015965120854443193935)
                      ·
                        rfl

theorem cell23_7299235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_7299235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299235 prefixEnd_7299235 := by exact prefixLift 7299235
  have htrace : WordTrace (prefixWord ++ tailWord_7299235) baseStart_7299235 baseEnd_7299235 := by
    simpa [prefixWord, tailWord_7299235, baseEnd_7299235] using wordTrace_append hprefix tailTrace_7299235
  have hstable : (prefixWord ++ tailWord_7299235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299235).length < 2 ^ (prefixWord ++ tailWord_7299235).sum := by decide
  have hdescent : baseEnd_7299235 < baseStart_7299235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299253 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 6]
def baseStart_7299253 : Nat := 118140960795 + 7299253 * 2 ^ 59
def prefixEnd_7299253 : Nat := 4983230072969 + 3 ^ 40 * 7299253 * 2
def baseEnd_7299253 : Nat := 416447245308070596974317

theorem tailTrace_7299253 : CollatzResearch.WordTrace tailWord_7299253 prefixEnd_7299253 416447245308070596974317 := by
  unfold tailWord_7299253
  simp only [CollatzResearch.WordTrace]
  refine ⟨266225628225060469009566413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177483752150040312673044275 266225628225060469009566413)
  ·
    refine ⟨99834610584397675878587405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266225628225060469009566413 99834610584397675878587405)
    ·
      refine ⟨37437978969149128454470277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99834610584397675878587405 37437978969149128454470277)
      ·
        refine ⟨7019621056715461585213177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37437978969149128454470277 7019621056715461585213177)
        ·
          refine ⟨5264715792536596188909883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7019621056715461585213177 5264715792536596188909883)
          ·
            refine ⟨7897073688804894283364825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264715792536596188909883 7897073688804894283364825)
            ·
              refine ⟨5922805266603670712523619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7897073688804894283364825 5922805266603670712523619)
              ·
                refine ⟨8884207899905506068785429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922805266603670712523619 8884207899905506068785429)
                ·
                  refine ⟨416447245308070596974317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8884207899905506068785429 416447245308070596974317)
                  ·
                    rfl

theorem cell23_7299253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_7299253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299253 prefixEnd_7299253 := by exact prefixLift 7299253
  have htrace : WordTrace (prefixWord ++ tailWord_7299253) baseStart_7299253 baseEnd_7299253 := by
    simpa [prefixWord, tailWord_7299253, baseEnd_7299253] using wordTrace_append hprefix tailTrace_7299253
  have hstable : (prefixWord ++ tailWord_7299253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299253).length < 2 ^ (prefixWord ++ tailWord_7299253).sum := by decide
  have hdescent : baseEnd_7299253 < baseStart_7299253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299266 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7299266 : Nat := 118140960795 + 7299266 * 2 ^ 59
def prefixEnd_7299266 : Nat := 4983230072969 + 3 ^ 40 * 7299266 * 2
def baseEnd_7299266 : Nat := 1249343961007047940635431

theorem tailTrace_7299266 : CollatzResearch.WordTrace tailWord_7299266 prefixEnd_7299266 1249343961007047940635431 := by
  unfold tailWord_7299266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66556525593503343057447413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177484068249342248153193101 66556525593503343057447413)
  ·
    refine ⟨6239674274390938411635695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66556525593503343057447413 6239674274390938411635695)
    ·
      refine ⟨9359511411586407617453543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239674274390938411635695 9359511411586407617453543)
      ·
        refine ⟨14039267117379611426180315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359511411586407617453543 14039267117379611426180315)
        ·
          refine ⟨21058900676069417139270473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039267117379611426180315 21058900676069417139270473)
          ·
            refine ⟨15794175507052062854452855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21058900676069417139270473 15794175507052062854452855)
            ·
              refine ⟨23691263260578094281679283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15794175507052062854452855 23691263260578094281679283)
              ·
                refine ⟨35536894890867141422518925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23691263260578094281679283 35536894890867141422518925)
                ·
                  refine ⟨13326335584075178033444597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35536894890867141422518925 13326335584075178033444597)
                  ·
                    refine ⟨1249343961007047940635431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13326335584075178033444597 1249343961007047940635431)
                    ·
                      rfl

theorem cell23_7299266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7299266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299266 prefixEnd_7299266 := by exact prefixLift 7299266
  have htrace : WordTrace (prefixWord ++ tailWord_7299266) baseStart_7299266 baseEnd_7299266 := by
    simpa [prefixWord, tailWord_7299266, baseEnd_7299266] using wordTrace_append hprefix tailTrace_7299266
  have hstable : (prefixWord ++ tailWord_7299266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299266).length < 2 ^ (prefixWord ++ tailWord_7299266).sum := by decide
  have hdescent : baseEnd_7299266 < baseStart_7299266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299269 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 3, 2, 2]
def baseStart_7299269 : Nat := 118140960795 + 7299269 * 2 ^ 59
def prefixEnd_7299269 : Nat := 4983230072969 + 3 ^ 40 * 7299269 * 2
def baseEnd_7299269 : Nat := 3748033423463107310168779

theorem tailTrace_7299269 : CollatzResearch.WordTrace tailWord_7299269 prefixEnd_7299269 3748033423463107310168779 := by
  unfold tailWord_7299269
  simp only [CollatzResearch.WordTrace]
  refine ⟨266226211793002503742148861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177484141195335002494765907 266226211793002503742148861)
  ·
    refine ⟨99834829422375938903305823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266226211793002503742148861 99834829422375938903305823)
    ·
      refine ⟨149752244133563908354958735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99834829422375938903305823 149752244133563908354958735)
      ·
        refine ⟨224628366200345862532438103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149752244133563908354958735 224628366200345862532438103)
        ·
          refine ⟨336942549300518793798657155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224628366200345862532438103 336942549300518793798657155)
          ·
            refine ⟨505413823950778190697985733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336942549300518793798657155 505413823950778190697985733)
            ·
              refine ⟨94765091990770910755872325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 505413823950778190697985733 94765091990770910755872325)
              ·
                refine ⟨17768454748269545766726061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94765091990770910755872325 17768454748269545766726061)
                ·
                  refine ⟨6663170530601079662522273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17768454748269545766726061 6663170530601079662522273)
                  ·
                    refine ⟨4997377897950809746891705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6663170530601079662522273 4997377897950809746891705)
                    ·
                      refine ⟨3748033423463107310168779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997377897950809746891705 3748033423463107310168779)
                      ·
                        rfl

theorem cell23_7299269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_7299269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299269 prefixEnd_7299269 := by exact prefixLift 7299269
  have htrace : WordTrace (prefixWord ++ tailWord_7299269) baseStart_7299269 baseEnd_7299269 := by
    simpa [prefixWord, tailWord_7299269, baseEnd_7299269] using wordTrace_append hprefix tailTrace_7299269
  have hstable : (prefixWord ++ tailWord_7299269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299269).length < 2 ^ (prefixWord ++ tailWord_7299269).sum := by decide
  have hdescent : baseEnd_7299269 < baseStart_7299269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299282 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7299282 : Nat := 118140960795 + 7299282 * 2 ^ 59
def prefixEnd_7299282 : Nat := 4983230072969 + 3 ^ 40 * 7299282 * 2
def baseEnd_7299282 : Nat := 3748040098711615759306219

theorem tailTrace_7299282 : CollatzResearch.WordTrace tailWord_7299282 prefixEnd_7299282 3748040098711615759306219 := by
  unfold tailWord_7299282
  simp only [CollatzResearch.WordTrace]
  refine ⟨66556671485488851740593025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177484457294636937974914733 66556671485488851740593025)
  ·
    refine ⟨49917503614116638805444769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66556671485488851740593025 49917503614116638805444769)
    ·
      refine ⟨37438127710587479104083577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49917503614116638805444769 37438127710587479104083577)
      ·
        refine ⟨28078595782940609328062683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37438127710587479104083577 28078595782940609328062683)
        ·
          refine ⟨42117893674410913992094025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28078595782940609328062683 42117893674410913992094025)
          ·
            refine ⟨31588420255808185494070519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42117893674410913992094025 31588420255808185494070519)
            ·
              refine ⟨47382630383712278241105779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31588420255808185494070519 47382630383712278241105779)
              ·
                refine ⟨71073945575568417361658669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47382630383712278241105779 71073945575568417361658669)
                ·
                  refine ⟨26652729590838156510622001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71073945575568417361658669 26652729590838156510622001)
                  ·
                    refine ⟨19989547193128617382966501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26652729590838156510622001 19989547193128617382966501)
                    ·
                      refine ⟨3748040098711615759306219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19989547193128617382966501 3748040098711615759306219)
                      ·
                        rfl

theorem cell23_7299282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7299282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299282 prefixEnd_7299282 := by exact prefixLift 7299282
  have htrace : WordTrace (prefixWord ++ tailWord_7299282) baseStart_7299282 baseEnd_7299282 := by
    simpa [prefixWord, tailWord_7299282, baseEnd_7299282] using wordTrace_append hprefix tailTrace_7299282
  have hstable : (prefixWord ++ tailWord_7299282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299282).length < 2 ^ (prefixWord ++ tailWord_7299282).sum := by decide
  have hdescent : baseEnd_7299282 < baseStart_7299282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299292 : List Nat := [2, 2, 5, 2, 12]
def baseStart_7299292 : Nat := 118140960795 + 7299292 * 2 ^ 59
def prefixEnd_7299292 : Nat := 4983230072969 + 3 ^ 40 * 7299292 * 2
def baseEnd_7299292 : Nat := 5141351486307490699837

theorem tailTrace_7299292 : CollatzResearch.WordTrace tailWord_7299292 prefixEnd_7299292 5141351486307490699837 := by
  unfold tailWord_7299292
  simp only [CollatzResearch.WordTrace]
  refine ⟨133113525335959589335118065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177484700447946119113490753 133113525335959589335118065)
  ·
    refine ⟨99835144001969692001338549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133113525335959589335118065 99835144001969692001338549)
    ·
      refine ⟨9359544750184658625125489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99835144001969692001338549 9359544750184658625125489)
      ·
        refine ⟨7019658562638493968844117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9359544750184658625125489 7019658562638493968844117)
        ·
          refine ⟨5141351486307490699837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7019658562638493968844117 5141351486307490699837)
          ·
            rfl

theorem cell23_7299292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 12].length) (baseStart_7299292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299292 prefixEnd_7299292 := by exact prefixLift 7299292
  have htrace : WordTrace (prefixWord ++ tailWord_7299292) baseStart_7299292 baseEnd_7299292 := by
    simpa [prefixWord, tailWord_7299292, baseEnd_7299292] using wordTrace_append hprefix tailTrace_7299292
  have hstable : (prefixWord ++ tailWord_7299292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299292).length < 2 ^ (prefixWord ++ tailWord_7299292).sum := by decide
  have hdescent : baseEnd_7299292 < baseStart_7299292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299309 : List Nat := [1, 5, 1, 2, 3, 2, 1, 8]
def baseStart_7299309 : Nat := 118140960795 + 7299309 * 2 ^ 59
def prefixEnd_7299309 : Nat := 4983230072969 + 3 ^ 40 * 7299309 * 2
def baseEnd_7299309 : Nat := 138816813432936561246985

theorem tailTrace_7299309 : CollatzResearch.WordTrace tailWord_7299309 prefixEnd_7299309 138816813432936561246985 := by
  unfold tailWord_7299309
  simp only [CollatzResearch.WordTrace]
  refine ⟨266227670712857590573604981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177485113808571727049069987 266227670712857590573604981)
  ·
    refine ⟨24958844129330399116275467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266227670712857590573604981 24958844129330399116275467)
    ·
      refine ⟨37438266193995598674413201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24958844129330399116275467 37438266193995598674413201)
      ·
        refine ⟨28078699645496699005809901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37438266193995598674413201 28078699645496699005809901)
        ·
          refine ⟨10529512367061262127178713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28078699645496699005809901 10529512367061262127178713)
          ·
            refine ⟨7897134275295946595384035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10529512367061262127178713 7897134275295946595384035)
            ·
              refine ⟨11845701412943919893076053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897134275295946595384035 11845701412943919893076053)
              ·
                refine ⟨138816813432936561246985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11845701412943919893076053 138816813432936561246985)
                ·
                  rfl

theorem cell23_7299309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 8].length) (baseStart_7299309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299309 prefixEnd_7299309 := by exact prefixLift 7299309
  have htrace : WordTrace (prefixWord ++ tailWord_7299309) baseStart_7299309 baseEnd_7299309 := by
    simpa [prefixWord, tailWord_7299309, baseEnd_7299309] using wordTrace_append hprefix tailTrace_7299309
  have hstable : (prefixWord ++ tailWord_7299309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299309).length < 2 ^ (prefixWord ++ tailWord_7299309).sum := by decide
  have hdescent : baseEnd_7299309 < baseStart_7299309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299329 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_7299329 : Nat := 118140960795 + 7299329 * 2 ^ 59
def prefixEnd_7299329 : Nat := 4983230072969 + 3 ^ 40 * 7299329 * 2
def baseEnd_7299329 : Nat := 3748064232302377075418503

theorem tailTrace_7299329 : CollatzResearch.WordTrace tailWord_7299329 prefixEnd_7299329 3748064232302377075418503 := by
  unfold tailWord_7299329
  simp only [CollatzResearch.WordTrace]
  refine ⟨266228400172785133989333041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177485600115190089326222027 266228400172785133989333041)
  ·
    refine ⟨199671300129588850491999781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266228400172785133989333041 199671300129588850491999781)
    ·
      refine ⟨37438368774297909467249959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199671300129588850491999781 37438368774297909467249959)
      ·
        refine ⟨56157553161446864200874939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37438368774297909467249959 56157553161446864200874939)
        ·
          refine ⟨84236329742170296301312409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56157553161446864200874939 84236329742170296301312409)
          ·
            refine ⟨63177247306627722225984307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84236329742170296301312409 63177247306627722225984307)
            ·
              refine ⟨94765870959941583338976461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63177247306627722225984307 94765870959941583338976461)
              ·
                refine ⟨35537201609978093752116173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94765870959941583338976461 35537201609978093752116173)
                ·
                  refine ⟨13326450603741785157043565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35537201609978093752116173 13326450603741785157043565)
                  ·
                    refine ⟨4997418976403169433891337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13326450603741785157043565 4997418976403169433891337)
                    ·
                      refine ⟨3748064232302377075418503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997418976403169433891337 3748064232302377075418503)
                      ·
                        rfl

theorem cell23_7299329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_7299329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299329 prefixEnd_7299329 := by exact prefixLift 7299329
  have htrace : WordTrace (prefixWord ++ tailWord_7299329) baseStart_7299329 baseEnd_7299329 := by
    simpa [prefixWord, tailWord_7299329, baseEnd_7299329] using wordTrace_append hprefix tailTrace_7299329
  have hstable : (prefixWord ++ tailWord_7299329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299329).length < 2 ^ (prefixWord ++ tailWord_7299329).sum := by decide
  have hdescent : baseEnd_7299329 < baseStart_7299329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299370 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7299370 : Nat := 118140960795 + 7299370 * 2 ^ 59
def prefixEnd_7299370 : Nat := 4983230072969 + 3 ^ 40 * 7299370 * 2
def baseEnd_7299370 : Nat := 3748085285009211415005815

theorem tailTrace_7299370 : CollatzResearch.WordTrace tailWord_7299370 prefixEnd_7299370 3748085285009211415005815 := by
  unfold tailWord_7299370
  simp only [CollatzResearch.WordTrace]
  refine ⟨66557473891409149497893891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177486597043757731994383709 66557473891409149497893891)
  ·
    refine ⟨99836210837113724246840837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66557473891409149497893891 99836210837113724246840837)
    ·
      refine ⟨18719289531958823296282657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99836210837113724246840837 18719289531958823296282657)
      ·
        refine ⟨14039467148969117472211993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18719289531958823296282657 14039467148969117472211993)
        ·
          refine ⟨10529600361726838104158995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14039467148969117472211993 10529600361726838104158995)
          ·
            refine ⟨15794400542590257156238493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529600361726838104158995 15794400542590257156238493)
            ·
              refine ⟨5922900203471346433589435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15794400542590257156238493 5922900203471346433589435)
              ·
                refine ⟨8884350305207019650384153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922900203471346433589435 8884350305207019650384153)
                ·
                  refine ⟨6663262728905264737788115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8884350305207019650384153 6663262728905264737788115)
                  ·
                    refine ⟨9994894093357897106682173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6663262728905264737788115 9994894093357897106682173)
                    ·
                      refine ⟨3748085285009211415005815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9994894093357897106682173 3748085285009211415005815)
                      ·
                        rfl

theorem cell23_7299370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7299370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299370 prefixEnd_7299370 := by exact prefixLift 7299370
  have htrace : WordTrace (prefixWord ++ tailWord_7299370) baseStart_7299370 baseEnd_7299370 := by
    simpa [prefixWord, tailWord_7299370, baseEnd_7299370] using wordTrace_append hprefix tailTrace_7299370
  have hstable : (prefixWord ++ tailWord_7299370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299370).length < 2 ^ (prefixWord ++ tailWord_7299370).sum := by decide
  have hdescent : baseEnd_7299370 < baseStart_7299370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299372 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_7299372 : Nat := 118140960795 + 7299372 * 2 ^ 59
def prefixEnd_7299372 : Nat := 4983230072969 + 3 ^ 40 * 7299372 * 2
def baseEnd_7299372 : Nat := 3748086311970520407180805

theorem tailTrace_7299372 : CollatzResearch.WordTrace tailWord_7299372 prefixEnd_7299372 3748086311970520407180805 := by
  unfold tailWord_7299372
  simp only [CollatzResearch.WordTrace]
  refine ⟨133114984255814676166574185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177486645674419568222098913 133114984255814676166574185)
  ·
    refine ⟨99836238191861007124930639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133114984255814676166574185 99836238191861007124930639)
    ·
      refine ⟨149754357287791510687395959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99836238191861007124930639 149754357287791510687395959)
      ·
        refine ⟨224631535931687266031093939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149754357287791510687395959 224631535931687266031093939)
        ·
          refine ⟨336947303897530899046640909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224631535931687266031093939 336947303897530899046640909)
          ·
            refine ⟨126355238961574087142490341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336947303897530899046640909 126355238961574087142490341)
            ·
              refine ⟨23691607305295141339216939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126355238961574087142490341 23691607305295141339216939)
              ·
                refine ⟨35537410957942712008825409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23691607305295141339216939 35537410957942712008825409)
                ·
                  refine ⟨26653058218457034006619057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35537410957942712008825409 26653058218457034006619057)
                  ·
                    refine ⟨19989793663842775504964293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26653058218457034006619057 19989793663842775504964293)
                    ·
                      refine ⟨3748086311970520407180805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19989793663842775504964293 3748086311970520407180805)
                      ·
                        rfl

theorem cell23_7299372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_7299372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299372 prefixEnd_7299372 := by exact prefixLift 7299372
  have htrace : WordTrace (prefixWord ++ tailWord_7299372) baseStart_7299372 baseEnd_7299372 := by
    simpa [prefixWord, tailWord_7299372, baseEnd_7299372] using wordTrace_append hprefix tailTrace_7299372
  have hstable : (prefixWord ++ tailWord_7299372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299372).length < 2 ^ (prefixWord ++ tailWord_7299372).sum := by decide
  have hdescent : baseEnd_7299372 < baseStart_7299372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299392 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_7299392 : Nat := 118140960795 + 7299392 * 2 ^ 59
def prefixEnd_7299392 : Nat := 4983230072969 + 3 ^ 40 * 7299392 * 2
def baseEnd_7299392 : Nat := 3748096581583610328930713

theorem tailTrace_7299392 : CollatzResearch.WordTrace tailWord_7299392 prefixEnd_7299392 3748096581583610328930713 := by
  unfold tailWord_7299392
  simp only [CollatzResearch.WordTrace]
  refine ⟨133115348985778447874438215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177487131981037930499250953 133115348985778447874438215)
  ·
    refine ⟨199673023478667671811657323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133115348985778447874438215 199673023478667671811657323)
    ·
      refine ⟨299509535218001507717485985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199673023478667671811657323 299509535218001507717485985)
      ·
        refine ⟨224632151413501130788114489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299509535218001507717485985 224632151413501130788114489)
        ·
          refine ⟨168474113560125848091085867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224632151413501130788114489 168474113560125848091085867)
          ·
            refine ⟨252711170340188772136628801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168474113560125848091085867 252711170340188772136628801)
            ·
              refine ⟨189533377755141579102471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252711170340188772136628801 189533377755141579102471601)
              ·
                refine ⟨142150033316356184326853701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189533377755141579102471601 142150033316356184326853701)
                ·
                  refine ⟨26653131246816784561285069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142150033316356184326853701 26653131246816784561285069)
                  ·
                    refine ⟨9994924217556294210481901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26653131246816784561285069 9994924217556294210481901)
                    ·
                      refine ⟨3748096581583610328930713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9994924217556294210481901 3748096581583610328930713)
                      ·
                        rfl

theorem cell23_7299392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_7299392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299392 prefixEnd_7299392 := by exact prefixLift 7299392
  have htrace : WordTrace (prefixWord ++ tailWord_7299392) baseStart_7299392 baseEnd_7299392 := by
    simpa [prefixWord, tailWord_7299392, baseEnd_7299392] using wordTrace_append hprefix tailTrace_7299392
  have hstable : (prefixWord ++ tailWord_7299392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299392).length < 2 ^ (prefixWord ++ tailWord_7299392).sum := by decide
  have hdescent : baseEnd_7299392 < baseStart_7299392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299396 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7299396 : Nat := 118140960795 + 7299396 * 2 ^ 59
def prefixEnd_7299396 : Nat := 4983230072969 + 3 ^ 40 * 7299396 * 2
def baseEnd_7299396 : Nat := 3748098635506228313280695

theorem tailTrace_7299396 : CollatzResearch.WordTrace tailWord_7299396 prefixEnd_7299396 3748098635506228313280695 := by
  unfold tailWord_7299396
  simp only [CollatzResearch.WordTrace]
  refine ⟨133115421931771202216011021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177487229242361602954681361 133115421931771202216011021)
  ·
    refine ⟨49918283224414200831004133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133115421931771202216011021 49918283224414200831004133)
    ·
      refine ⟨9359678104577662655813275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49918283224414200831004133 9359678104577662655813275)
      ·
        refine ⟨14039517156866493983719913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359678104577662655813275 14039517156866493983719913)
        ·
          refine ⟨10529637867649870487789935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14039517156866493983719913 10529637867649870487789935)
          ·
            refine ⟨15794456801474805731684903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529637867649870487789935 15794456801474805731684903)
            ·
              refine ⟨23691685202212208597527355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15794456801474805731684903 23691685202212208597527355)
              ·
                refine ⟨35537527803318312896291033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23691685202212208597527355 35537527803318312896291033)
                ·
                  refine ⟨26653145852488734672218275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35537527803318312896291033 26653145852488734672218275)
                  ·
                    refine ⟨39979718778733102008327413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26653145852488734672218275 39979718778733102008327413)
                    ·
                      refine ⟨3748098635506228313280695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39979718778733102008327413 3748098635506228313280695)
                      ·
                        rfl

theorem cell23_7299396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7299396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299396 prefixEnd_7299396 := by exact prefixLift 7299396
  have htrace : WordTrace (prefixWord ++ tailWord_7299396) baseStart_7299396 baseEnd_7299396 := by
    simpa [prefixWord, tailWord_7299396, baseEnd_7299396] using wordTrace_append hprefix tailTrace_7299396
  have hstable : (prefixWord ++ tailWord_7299396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299396).length < 2 ^ (prefixWord ++ tailWord_7299396).sum := by decide
  have hdescent : baseEnd_7299396 < baseStart_7299396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299449 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 4, 4, 2]
def baseStart_7299449 : Nat := 118140960795 + 7299449 * 2 ^ 59
def prefixEnd_7299449 : Nat := 4983230072969 + 3 ^ 40 * 7299449 * 2
def baseEnd_7299449 : Nat := 3748125849980916605917951

theorem tailTrace_7299449 : CollatzResearch.WordTrace tailWord_7299449 prefixEnd_7299449 3748125849980916605917951 := by
  unfold tailWord_7299449
  simp only [CollatzResearch.WordTrace]
  refine ⟨266232776932350394483701401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177488517954900262989134267 266232776932350394483701401)
  ·
    refine ⟨199674582699262795862776051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266232776932350394483701401 199674582699262795862776051)
    ·
      refine ⟨299511874048894193794164077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199674582699262795862776051 299511874048894193794164077)
      ·
        refine ⟨112316952768335322672811529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299511874048894193794164077 112316952768335322672811529)
        ·
          refine ⟨84237714576251492004608647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112316952768335322672811529 84237714576251492004608647)
          ·
            refine ⟨126356571864377238006912971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84237714576251492004608647 126356571864377238006912971)
            ·
              refine ⟨189534857796565857010369457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126356571864377238006912971 189534857796565857010369457)
              ·
                refine ⟨142151143347424392757777093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189534857796565857010369457 142151143347424392757777093)
                ·
                  refine ⟨26653339377642073642083205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142151143347424392757777093 26653339377642073642083205)
                  ·
                    refine ⟨4997501133307888807890601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26653339377642073642083205 4997501133307888807890601)
                    ·
                      refine ⟨3748125849980916605917951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997501133307888807890601 3748125849980916605917951)
                      ·
                        rfl

theorem cell23_7299449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_7299449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299449 prefixEnd_7299449 := by exact prefixLift 7299449
  have htrace : WordTrace (prefixWord ++ tailWord_7299449) baseStart_7299449 baseEnd_7299449 := by
    simpa [prefixWord, tailWord_7299449, baseEnd_7299449] using wordTrace_append hprefix tailTrace_7299449
  have hstable : (prefixWord ++ tailWord_7299449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299449).length < 2 ^ (prefixWord ++ tailWord_7299449).sum := by decide
  have hdescent : baseEnd_7299449 < baseStart_7299449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299512 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_7299512 : Nat := 118140960795 + 7299512 * 2 ^ 59
def prefixEnd_7299512 : Nat := 4983230072969 + 3 ^ 40 * 7299512 * 2
def baseEnd_7299512 : Nat := 3748158199262149859430161

theorem tailTrace_7299512 : CollatzResearch.WordTrace tailWord_7299512 prefixEnd_7299512 3748158199262149859430161 := by
  unfold tailWord_7299512
  simp only [CollatzResearch.WordTrace]
  refine ⟨133117537365561078121622395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177490049820748104162163193 133117537365561078121622395)
  ·
    refine ⟨199676306048341617182433593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133117537365561078121622395 199676306048341617182433593)
    ·
      refine ⟨149757229536256212886825195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199676306048341617182433593 149757229536256212886825195)
      ·
        refine ⟨224635844304384319330237793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149757229536256212886825195 224635844304384319330237793)
        ·
          refine ⟨168476883228288239497678345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224635844304384319330237793 168476883228288239497678345)
          ·
            refine ⟨126357662421216179623258759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168476883228288239497678345 126357662421216179623258759)
            ·
              refine ⟨189536493631824269434888139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126357662421216179623258759 189536493631824269434888139)
              ·
                refine ⟨284304740447736404152332209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189536493631824269434888139 284304740447736404152332209)
                ·
                  refine ⟨213228555335802303114249157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284304740447736404152332209 213228555335802303114249157)
                  ·
                    refine ⟨39980354125462931833921717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213228555335802303114249157 39980354125462931833921717)
                    ·
                      refine ⟨3748158199262149859430161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39980354125462931833921717 3748158199262149859430161)
                      ·
                        rfl

theorem cell23_7299512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_7299512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299512 prefixEnd_7299512 := by exact prefixLift 7299512
  have htrace : WordTrace (prefixWord ++ tailWord_7299512) baseStart_7299512 baseEnd_7299512 := by
    simpa [prefixWord, tailWord_7299512, baseEnd_7299512] using wordTrace_append hprefix tailTrace_7299512
  have hstable : (prefixWord ++ tailWord_7299512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299512).length < 2 ^ (prefixWord ++ tailWord_7299512).sum := by decide
  have hdescent : baseEnd_7299512 < baseStart_7299512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299559 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7299559 : Nat := 118140960795 + 7299559 * 2 ^ 59
def prefixEnd_7299559 : Nat := 4983230072969 + 3 ^ 40 * 7299559 * 2
def baseEnd_7299559 : Nat := 3748182332852911175542445

theorem tailTrace_7299559 : CollatzResearch.WordTrace tailWord_7299559 prefixEnd_7299559 3748182332852911175542445 := by
  unfold tailWord_7299559
  simp only [CollatzResearch.WordTrace]
  refine ⟨266236788961951883270205731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177491192641301255513470487 266236788961951883270205731)
  ·
    refine ⟨399355183442927824905308597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266236788961951883270205731 399355183442927824905308597)
    ·
      refine ⟨37439548447774483584872681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 399355183442927824905308597 37439548447774483584872681)
      ·
        refine ⟨28079661335830862688654511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37439548447774483584872681 28079661335830862688654511)
        ·
          refine ⟨42119492003746294032981767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28079661335830862688654511 42119492003746294032981767)
          ·
            refine ⟨63179238005619441049472651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42119492003746294032981767 63179238005619441049472651)
            ·
              refine ⟨94768857008429161574208977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63179238005619441049472651 94768857008429161574208977)
              ·
                refine ⟨71076642756321871180656733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94768857008429161574208977 71076642756321871180656733)
                ·
                  refine ⟨26653741033620701692746275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71076642756321871180656733 26653741033620701692746275)
                  ·
                    refine ⟨39980611550431052539119413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26653741033620701692746275 39980611550431052539119413)
                    ·
                      refine ⟨3748182332852911175542445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39980611550431052539119413 3748182332852911175542445)
                      ·
                        rfl

theorem cell23_7299559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7299559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299559 prefixEnd_7299559 := by exact prefixLift 7299559
  have htrace : WordTrace (prefixWord ++ tailWord_7299559) baseStart_7299559 baseEnd_7299559 := by
    simpa [prefixWord, tailWord_7299559, baseEnd_7299559] using wordTrace_append hprefix tailTrace_7299559
  have hstable : (prefixWord ++ tailWord_7299559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299559).length < 2 ^ (prefixWord ++ tailWord_7299559).sum := by decide
  have hdescent : baseEnd_7299559 < baseStart_7299559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299566 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_7299566 : Nat := 118140960795 + 7299566 * 2 ^ 59
def prefixEnd_7299566 : Nat := 4983230072969 + 3 ^ 40 * 7299566 * 2
def baseEnd_7299566 : Nat := 1249395309072497549384971

theorem tailTrace_7299566 : CollatzResearch.WordTrace tailWord_7299566 prefixEnd_7299566 1249395309072497549384971 := by
  unfold tailWord_7299566
  simp only [CollatzResearch.WordTrace]
  refine ⟨33279630534115815433213819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177491362848617682310473701 33279630534115815433213819)
  ·
    refine ⟨49919445801173723149820729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33279630534115815433213819 49919445801173723149820729)
    ·
      refine ⟨37439584350880292362365547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49919445801173723149820729 37439584350880292362365547)
      ·
        refine ⟨56159376526320438543548321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37439584350880292362365547 56159376526320438543548321)
        ·
          refine ⟨42119532394740328907661241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56159376526320438543548321 42119532394740328907661241)
          ·
            refine ⟨31589649296055246680745931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42119532394740328907661241 31589649296055246680745931)
            ·
              refine ⟨47384473944082870021118897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31589649296055246680745931 47384473944082870021118897)
              ·
                refine ⟨35538355458062152515839173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47384473944082870021118897 35538355458062152515839173)
                ·
                  refine ⟨6663441648386653596719845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35538355458062152515839173 6663441648386653596719845)
                  ·
                    refine ⟨1249395309072497549384971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663441648386653596719845 1249395309072497549384971)
                    ·
                      rfl

theorem cell23_7299566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_7299566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299566 prefixEnd_7299566 := by exact prefixLift 7299566
  have htrace : WordTrace (prefixWord ++ tailWord_7299566) baseStart_7299566 baseEnd_7299566 := by
    simpa [prefixWord, tailWord_7299566, baseEnd_7299566] using wordTrace_append hprefix tailTrace_7299566
  have hstable : (prefixWord ++ tailWord_7299566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299566).length < 2 ^ (prefixWord ++ tailWord_7299566).sum := by decide
  have hdescent : baseEnd_7299566 < baseStart_7299566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299569 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_7299569 : Nat := 118140960795 + 7299569 * 2 ^ 59
def prefixEnd_7299569 : Nat := 4983230072969 + 3 ^ 40 * 7299569 * 2
def baseEnd_7299569 : Nat := 3748187467659456136417399

theorem tailTrace_7299569 : CollatzResearch.WordTrace tailWord_7299569 prefixEnd_7299569 3748187467659456136417399 := by
  unfold tailWord_7299569
  simp only [CollatzResearch.WordTrace]
  refine ⟨266237153691915654978069761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177491435794610436652046507 266237153691915654978069761)
  ·
    refine ⟨199677865268936741233552321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266237153691915654978069761 199677865268936741233552321)
    ·
      refine ⟨149758398951702555925164241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199677865268936741233552321 149758398951702555925164241)
      ·
        refine ⟨112318799213776916943873181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149758398951702555925164241 112318799213776916943873181)
        ·
          refine ⟨42119549705166343853952443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112318799213776916943873181 42119549705166343853952443)
          ·
            refine ⟨63179324557749515780928665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42119549705166343853952443 63179324557749515780928665)
            ·
              refine ⟨47384493418312136835696499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63179324557749515780928665 47384493418312136835696499)
              ·
                refine ⟨71076740127468205253544749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47384493418312136835696499 71076740127468205253544749)
                ·
                  refine ⟨26653777547800576970079281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71076740127468205253544749 26653777547800576970079281)
                  ·
                    refine ⟨19990333160850432727559461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26653777547800576970079281 19990333160850432727559461)
                    ·
                      refine ⟨3748187467659456136417399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19990333160850432727559461 3748187467659456136417399)
                      ·
                        rfl

theorem cell23_7299569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_7299569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299569 prefixEnd_7299569 := by exact prefixLift 7299569
  have htrace : WordTrace (prefixWord ++ tailWord_7299569) baseStart_7299569 baseEnd_7299569 := by
    simpa [prefixWord, tailWord_7299569, baseEnd_7299569] using wordTrace_append hprefix tailTrace_7299569
  have hstable : (prefixWord ++ tailWord_7299569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299569).length < 2 ^ (prefixWord ++ tailWord_7299569).sum := by decide
  have hdescent : baseEnd_7299569 < baseStart_7299569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299576 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_7299576 : Nat := 118140960795 + 7299576 * 2 ^ 59
def prefixEnd_7299576 : Nat := 4983230072969 + 3 ^ 40 * 7299576 * 2
def baseEnd_7299576 : Nat := 3748191062024037609029867

theorem tailTrace_7299576 : CollatzResearch.WordTrace tailWord_7299576 prefixEnd_7299576 3748191062024037609029867 := by
  unfold tailWord_7299576
  simp only [CollatzResearch.WordTrace]
  refine ⟨133118704501445147586787291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177491606001926863449049721 133118704501445147586787291)
  ·
    refine ⟨199678056752167721380180937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133118704501445147586787291 199678056752167721380180937)
    ·
      refine ⟨149758542564125791035135703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199678056752167721380180937 149758542564125791035135703)
      ·
        refine ⟨224637813846188686552703555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149758542564125791035135703 224637813846188686552703555)
        ·
          refine ⟨336956720769283029829055333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224637813846188686552703555 336956720769283029829055333)
          ·
            refine ⟨63179385144240568092947875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336956720769283029829055333 63179385144240568092947875)
            ·
              refine ⟨94769077716360852139421813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63179385144240568092947875 94769077716360852139421813)
              ·
                refine ⟨8884601035908829888070795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94769077716360852139421813 8884601035908829888070795)
                ·
                  refine ⟨13326901553863244832106193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8884601035908829888070795 13326901553863244832106193)
                  ·
                    refine ⟨9995176165397433624079645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13326901553863244832106193 9995176165397433624079645)
                    ·
                      refine ⟨3748191062024037609029867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9995176165397433624079645 3748191062024037609029867)
                      ·
                        rfl

theorem cell23_7299576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_7299576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299576 prefixEnd_7299576 := by exact prefixLift 7299576
  have htrace : WordTrace (prefixWord ++ tailWord_7299576) baseStart_7299576 baseEnd_7299576 := by
    simpa [prefixWord, tailWord_7299576, baseEnd_7299576] using wordTrace_append hprefix tailTrace_7299576
  have hstable : (prefixWord ++ tailWord_7299576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299576).length < 2 ^ (prefixWord ++ tailWord_7299576).sum := by decide
  have hdescent : baseEnd_7299576 < baseStart_7299576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299607 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7299607 : Nat := 118140960795 + 7299607 * 2 ^ 59
def prefixEnd_7299607 : Nat := 4983230072969 + 3 ^ 40 * 7299607 * 2
def baseEnd_7299607 : Nat := 3748206979924326987742225

theorem tailTrace_7299607 : CollatzResearch.WordTrace tailWord_7299607 prefixEnd_7299607 3748206979924326987742225 := by
  unfold tailWord_7299607
  simp only [CollatzResearch.WordTrace]
  refine ⟨266238539665777987467953075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177492359777185324978635383 266238539665777987467953075)
  ·
    refine ⟨399357809498666981201929613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266238539665777987467953075 399357809498666981201929613)
    ·
      refine ⟨149759178562000117950723605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399357809498666981201929613 149759178562000117950723605)
      ·
        refine ⟨7019961495093755528940169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149759178562000117950723605 7019961495093755528940169)
        ·
          refine ⟨5264971121320316646705127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7019961495093755528940169 5264971121320316646705127)
          ·
            refine ⟨7897456681980474970057691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264971121320316646705127 7897456681980474970057691)
            ·
              refine ⟨11846185022970712455086537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897456681980474970057691 11846185022970712455086537)
              ·
                refine ⟨8884638767228034341314903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11846185022970712455086537 8884638767228034341314903)
                ·
                  refine ⟨13326958150842051511972355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8884638767228034341314903 13326958150842051511972355)
                  ·
                    refine ⟨19990437226263077267958533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13326958150842051511972355 19990437226263077267958533)
                    ·
                      refine ⟨3748206979924326987742225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19990437226263077267958533 3748206979924326987742225)
                      ·
                        rfl

theorem cell23_7299607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7299607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299607 prefixEnd_7299607 := by exact prefixLift 7299607
  have htrace : WordTrace (prefixWord ++ tailWord_7299607) baseStart_7299607 baseEnd_7299607 := by
    simpa [prefixWord, tailWord_7299607, baseEnd_7299607] using wordTrace_append hprefix tailTrace_7299607
  have hstable : (prefixWord ++ tailWord_7299607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299607).length < 2 ^ (prefixWord ++ tailWord_7299607).sum := by decide
  have hdescent : baseEnd_7299607 < baseStart_7299607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299633 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 1, 3, 2]
def baseStart_7299633 : Nat := 118140960795 + 7299633 * 2 ^ 59
def prefixEnd_7299633 : Nat := 4983230072969 + 3 ^ 40 * 7299633 * 2
def baseEnd_7299633 : Nat := 3748220330421343886017105

theorem tailTrace_7299633 : CollatzResearch.WordTrace tailWord_7299633 prefixEnd_7299633 3748220330421343886017105 := by
  unfold tailWord_7299633
  simp only [CollatzResearch.WordTrace]
  refine ⟨266239487963683793908399553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177492991975789195938933035 266239487963683793908399553)
  ·
    refine ⟨199679615972762845431299665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266239487963683793908399553 199679615972762845431299665)
    ·
      refine ⟨149759711979572134073474749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199679615972762845431299665 149759711979572134073474749)
      ·
        refine ⟨56159891992339550277553031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149759711979572134073474749 56159891992339550277553031)
        ·
          refine ⟨84239837988509325416329547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56159891992339550277553031 84239837988509325416329547)
          ·
            refine ⟨126359756982763988124494321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84239837988509325416329547 126359756982763988124494321)
            ·
              refine ⟨94769817737072991093370741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126359756982763988124494321 94769817737072991093370741)
              ·
                refine ⟨8884670412850592915003507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94769817737072991093370741 8884670412850592915003507)
                ·
                  refine ⟨13327005619275889372505261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8884670412850592915003507 13327005619275889372505261)
                  ·
                    refine ⟨4997627107228458514689473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13327005619275889372505261 4997627107228458514689473)
                    ·
                      refine ⟨3748220330421343886017105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997627107228458514689473 3748220330421343886017105)
                      ·
                        rfl

theorem cell23_7299633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_7299633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299633 prefixEnd_7299633 := by exact prefixLift 7299633
  have htrace : WordTrace (prefixWord ++ tailWord_7299633) baseStart_7299633 baseEnd_7299633 := by
    simpa [prefixWord, tailWord_7299633, baseEnd_7299633] using wordTrace_append hprefix tailTrace_7299633
  have hstable : (prefixWord ++ tailWord_7299633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299633).length < 2 ^ (prefixWord ++ tailWord_7299633).sum := by decide
  have hdescent : baseEnd_7299633 < baseStart_7299633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299639 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 2, 6]
def baseStart_7299639 : Nat := 118140960795 + 7299639 * 2 ^ 59
def prefixEnd_7299639 : Nat := 4983230072969 + 3 ^ 40 * 7299639 * 2
def baseEnd_7299639 : Nat := 1249407803768423620847359

theorem tailTrace_7299639 : CollatzResearch.WordTrace tailWord_7299639 prefixEnd_7299639 1249407803768423620847359 := by
  unfold tailWord_7299639
  simp only [CollatzResearch.WordTrace]
  refine ⟨266239706801662056933117971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177493137867774704622078647 266239706801662056933117971)
  ·
    refine ⟨399359560202493085399676957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266239706801662056933117971 399359560202493085399676957)
    ·
      refine ⟨149759835075934907024878859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399359560202493085399676957 149759835075934907024878859)
      ·
        refine ⟨224639752613902360537318289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149759835075934907024878859 224639752613902360537318289)
        ·
          refine ⟨168479814460426770402988717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224639752613902360537318289 168479814460426770402988717)
          ·
            refine ⟨63179930422660038901120769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168479814460426770402988717 63179930422660038901120769)
            ·
              refine ⟨47384947816995029175840577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63179930422660038901120769 47384947816995029175840577)
              ·
                refine ⟨35538710862746271881880433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47384947816995029175840577 35538710862746271881880433)
                ·
                  refine ⟨26654033147059703911410325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35538710862746271881880433 26654033147059703911410325)
                  ·
                    refine ⟨1249407803768423620847359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26654033147059703911410325 1249407803768423620847359)
                    ·
                      rfl

theorem cell23_7299639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_7299639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299639 prefixEnd_7299639 := by exact prefixLift 7299639
  have htrace : WordTrace (prefixWord ++ tailWord_7299639) baseStart_7299639 baseEnd_7299639 := by
    simpa [prefixWord, tailWord_7299639, baseEnd_7299639] using wordTrace_append hprefix tailTrace_7299639
  have hstable : (prefixWord ++ tailWord_7299639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299639).length < 2 ^ (prefixWord ++ tailWord_7299639).sum := by decide
  have hdescent : baseEnd_7299639 < baseStart_7299639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299659 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4]
def baseStart_7299659 : Nat := 118140960795 + 7299659 * 2 ^ 59
def prefixEnd_7299659 : Nat := 4983230072969 + 3 ^ 40 * 7299659 * 2
def baseEnd_7299659 : Nat := 3748233680918360784291985

theorem tailTrace_7299659 : CollatzResearch.WordTrace tailWord_7299659 prefixEnd_7299659 3748233680918360784291985 := by
  unfold tailWord_7299659
  simp only [CollatzResearch.WordTrace]
  refine ⟨266240436261589600348846031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177493624174393066899230687 266240436261589600348846031)
  ·
    refine ⟨399360654392384400523269047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266240436261589600348846031 399360654392384400523269047)
    ·
      refine ⟨599040981588576600784903571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399360654392384400523269047 599040981588576600784903571)
      ·
        refine ⟨898561472382864901177355357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599040981588576600784903571 898561472382864901177355357)
        ·
          refine ⟨336960552143574337941508259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898561472382864901177355357 336960552143574337941508259)
          ·
            refine ⟨505440828215361506912262389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336960552143574337941508259 505440828215361506912262389)
            ·
              refine ⟨47385077645190141273024599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 505440828215361506912262389 47385077645190141273024599)
              ·
                refine ⟨71077616467785211909536899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47385077645190141273024599 71077616467785211909536899)
                ·
                  refine ⟨106616424701677817864305349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71077616467785211909536899 106616424701677817864305349)
                  ·
                    refine ⟨19990579631564590849557253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106616424701677817864305349 19990579631564590849557253)
                    ·
                      refine ⟨3748233680918360784291985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19990579631564590849557253 3748233680918360784291985)
                      ·
                        rfl

theorem cell23_7299659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_7299659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299659 prefixEnd_7299659 := by exact prefixLift 7299659
  have htrace : WordTrace (prefixWord ++ tailWord_7299659) baseStart_7299659 baseEnd_7299659 := by
    simpa [prefixWord, tailWord_7299659, baseEnd_7299659] using wordTrace_append hprefix tailTrace_7299659
  have hstable : (prefixWord ++ tailWord_7299659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299659).length < 2 ^ (prefixWord ++ tailWord_7299659).sum := by decide
  have hdescent : baseEnd_7299659 < baseStart_7299659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299666 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_7299666 : Nat := 118140960795 + 7299666 * 2 ^ 59
def prefixEnd_7299666 : Nat := 4983230072969 + 3 ^ 40 * 7299666 * 2
def baseEnd_7299666 : Nat := 3748237275282942256904453

theorem tailTrace_7299666 : CollatzResearch.WordTrace tailWord_7299666 prefixEnd_7299666 3748237275282942256904453 := by
  unfold tailWord_7299666
  simp only [CollatzResearch.WordTrace]
  refine ⟨66560172893141060136087713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177493794381709493696233901 66560172893141060136087713)
  ·
    refine ⟨49920129669855795102065785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66560172893141060136087713 49920129669855795102065785)
    ·
      refine ⟨37440097252391846326549339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49920129669855795102065785 37440097252391846326549339)
      ·
        refine ⟨56160145878587769489824009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37440097252391846326549339 56160145878587769489824009)
        ·
          refine ⟨42120109408940827117368007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56160145878587769489824009 42120109408940827117368007)
          ·
            refine ⟨63180164113411240676052011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42120109408940827117368007 63180164113411240676052011)
            ·
              refine ⟨94770246170116861014078017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63180164113411240676052011 94770246170116861014078017)
              ·
                refine ⟨71077684627587645760558513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94770246170116861014078017 71077684627587645760558513)
                ·
                  refine ⟨53308263470690734320418885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71077684627587645760558513 53308263470690734320418885)
                  ·
                    refine ⟨9995299400754512685078541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53308263470690734320418885 9995299400754512685078541)
                    ·
                      refine ⟨3748237275282942256904453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9995299400754512685078541 3748237275282942256904453)
                      ·
                        rfl

theorem cell23_7299666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_7299666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299666 prefixEnd_7299666 := by exact prefixLift 7299666
  have htrace : WordTrace (prefixWord ++ tailWord_7299666) baseStart_7299666 baseEnd_7299666 := by
    simpa [prefixWord, tailWord_7299666, baseEnd_7299666] using wordTrace_append hprefix tailTrace_7299666
  have hstable : (prefixWord ++ tailWord_7299666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299666).length < 2 ^ (prefixWord ++ tailWord_7299666).sum := by decide
  have hdescent : baseEnd_7299666 < baseStart_7299666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299669 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 9]
def baseStart_7299669 : Nat := 118140960795 + 7299669 * 2 ^ 59
def prefixEnd_7299669 : Nat := 4983230072969 + 3 ^ 40 * 7299669 * 2
def baseEnd_7299669 : Nat := 416470979524989527240771

theorem tailTrace_7299669 : CollatzResearch.WordTrace tailWord_7299669 prefixEnd_7299669 416470979524989527240771 := by
  unfold tailWord_7299669
  simp only [CollatzResearch.WordTrace]
  refine ⟨266240800991553372056710061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177493867327702248037806707 266240800991553372056710061)
  ·
    refine ⟨99840300371832514521266273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266240800991553372056710061 99840300371832514521266273)
    ·
      refine ⟨74880225278874385890949705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99840300371832514521266273 74880225278874385890949705)
      ·
        refine ⟨56160168959155789418212279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74880225278874385890949705 56160168959155789418212279)
        ·
          refine ⟨84240253438733684127318419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56160168959155789418212279 84240253438733684127318419)
          ·
            refine ⟨126360380158100526190977629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84240253438733684127318419 126360380158100526190977629)
            ·
              refine ⟨47385142559287697321616611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126360380158100526190977629 47385142559287697321616611)
              ·
                refine ⟨71077713838931545982424917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47385142559287697321616611 71077713838931545982424917)
                ·
                  refine ⟨416470979524989527240771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71077713838931545982424917 416470979524989527240771)
                  ·
                    rfl

theorem cell23_7299669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_7299669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299669 prefixEnd_7299669 := by exact prefixLift 7299669
  have htrace : WordTrace (prefixWord ++ tailWord_7299669) baseStart_7299669 baseEnd_7299669 := by
    simpa [prefixWord, tailWord_7299669, baseEnd_7299669] using wordTrace_append hprefix tailTrace_7299669
  have hstable : (prefixWord ++ tailWord_7299669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299669).length < 2 ^ (prefixWord ++ tailWord_7299669).sum := by decide
  have hdescent : baseEnd_7299669 < baseStart_7299669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299678 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7299678 : Nat := 118140960795 + 7299678 * 2 ^ 59
def prefixEnd_7299678 : Nat := 4983230072969 + 3 ^ 40 * 7299678 * 2
def baseEnd_7299678 : Nat := 3748243437050796209954399

theorem tailTrace_7299678 : CollatzResearch.WordTrace tailWord_7299678 prefixEnd_7299678 3748243437050796209954399 := by
  unfold tailWord_7299678
  simp only [CollatzResearch.WordTrace]
  refine ⟨33280141156065095824223461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177494086165680511062525125 33280141156065095824223461)
  ·
    refine ⟨6240026466762205467041899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33280141156065095824223461 6240026466762205467041899)
    ·
      refine ⟨9360039700143308200562849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240026466762205467041899 9360039700143308200562849)
      ·
        refine ⟨7020029775107481150422137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9360039700143308200562849 7020029775107481150422137)
        ·
          refine ⟨5265022331330610862816603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7020029775107481150422137 5265022331330610862816603)
          ·
            refine ⟨7897533496995916294224905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265022331330610862816603 7897533496995916294224905)
            ·
              refine ⟨5923150122746937220668679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7897533496995916294224905 5923150122746937220668679)
              ·
                refine ⟨8884725184120405831003019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923150122746937220668679 8884725184120405831003019)
                ·
                  refine ⟨13327087776180608746504529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8884725184120405831003019 13327087776180608746504529)
                  ·
                    refine ⟨9995315832135456559878397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13327087776180608746504529 9995315832135456559878397)
                    ·
                      refine ⟨3748243437050796209954399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9995315832135456559878397 3748243437050796209954399)
                      ·
                        rfl

theorem cell23_7299678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7299678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299678 prefixEnd_7299678 := by exact prefixLift 7299678
  have htrace : WordTrace (prefixWord ++ tailWord_7299678) baseStart_7299678 baseEnd_7299678 := by
    simpa [prefixWord, tailWord_7299678, baseEnd_7299678] using wordTrace_append hprefix tailTrace_7299678
  have hstable : (prefixWord ++ tailWord_7299678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299678).length < 2 ^ (prefixWord ++ tailWord_7299678).sum := by decide
  have hdescent : baseEnd_7299678 < baseStart_7299678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299716 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_7299716 : Nat := 118140960795 + 7299716 * 2 ^ 59
def prefixEnd_7299716 : Nat := 4983230072969 + 3 ^ 40 * 7299716 * 2
def baseEnd_7299716 : Nat := 1249420983105222353759741

theorem tailTrace_7299716 : CollatzResearch.WordTrace tailWord_7299716 prefixEnd_7299716 1249420983105222353759741 := by
  unfold tailWord_7299716
  simp only [CollatzResearch.WordTrace]
  refine ⟨133121257611191549541835501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177495010148255399389114001 133121257611191549541835501)
  ·
    refine ⟨49920471604196831078188313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133121257611191549541835501 49920471604196831078188313)
    ·
      refine ⟨37440353703147623308641235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49920471604196831078188313 37440353703147623308641235)
      ·
        refine ⟨56160530554721434962961853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37440353703147623308641235 56160530554721434962961853)
        ·
          refine ⟨21060198958020538111110695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56160530554721434962961853 21060198958020538111110695)
          ·
            refine ⟨31590298437030807166666043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21060198958020538111110695 31590298437030807166666043)
            ·
              refine ⟨47385447655546210749999065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31590298437030807166666043 47385447655546210749999065)
              ·
                refine ⟨35539085741659658062499299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47385447655546210749999065 35539085741659658062499299)
                ·
                  refine ⟨53308628612489487093748949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35539085741659658062499299 53308628612489487093748949)
                  ·
                    refine ⟨1249420983105222353759741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53308628612489487093748949 1249420983105222353759741)
                    ·
                      rfl

theorem cell23_7299716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_7299716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299716 prefixEnd_7299716 := by exact prefixLift 7299716
  have htrace : WordTrace (prefixWord ++ tailWord_7299716) baseStart_7299716 baseEnd_7299716 := by
    simpa [prefixWord, tailWord_7299716, baseEnd_7299716] using wordTrace_append hprefix tailTrace_7299716
  have hstable : (prefixWord ++ tailWord_7299716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299716).length < 2 ^ (prefixWord ++ tailWord_7299716).sum := by decide
  have hdescent : baseEnd_7299716 < baseStart_7299716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299736 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7299736 : Nat := 118140960795 + 7299736 * 2 ^ 59
def prefixEnd_7299736 : Nat := 4983230072969 + 3 ^ 40 * 7299736 * 2
def baseEnd_7299736 : Nat := 3748273218928756983029131

theorem tailTrace_7299736 : CollatzResearch.WordTrace tailWord_7299736 prefixEnd_7299736 3748273218928756983029131 := by
  unfold tailWord_7299736
  simp only [CollatzResearch.WordTrace]
  refine ⟨133121622341155321249699531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177495496454873761666266041 133121622341155321249699531)
  ·
    refine ⟨199682433511732981874549297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133121622341155321249699531 199682433511732981874549297)
    ·
      refine ⟨149761825133799736405911973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199682433511732981874549297 149761825133799736405911973)
      ·
        refine ⟨28080342212587450576108495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149761825133799736405911973 28080342212587450576108495)
        ·
          refine ⟨42120513318881175864162743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28080342212587450576108495 42120513318881175864162743)
          ·
            refine ⟨63180769978321763796244115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42120513318881175864162743 63180769978321763796244115)
            ·
              refine ⟨94771154967482645694366173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63180769978321763796244115 94771154967482645694366173)
              ·
                refine ⟨35539183112805992135387315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94771154967482645694366173 35539183112805992135387315)
                ·
                  refine ⟨53308774669208988203080973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35539183112805992135387315 53308774669208988203080973)
                  ·
                    refine ⟨19990790500953370576155365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53308774669208988203080973 19990790500953370576155365)
                    ·
                      refine ⟨3748273218928756983029131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19990790500953370576155365 3748273218928756983029131)
                      ·
                        rfl

theorem cell23_7299736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7299736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299736 prefixEnd_7299736 := by exact prefixLift 7299736
  have htrace : WordTrace (prefixWord ++ tailWord_7299736) baseStart_7299736 baseEnd_7299736 := by
    simpa [prefixWord, tailWord_7299736, baseEnd_7299736] using wordTrace_append hprefix tailTrace_7299736
  have hstable : (prefixWord ++ tailWord_7299736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299736).length < 2 ^ (prefixWord ++ tailWord_7299736).sum := by decide
  have hdescent : baseEnd_7299736 < baseStart_7299736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299739 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_7299739 : Nat := 118140960795 + 7299739 * 2 ^ 59
def prefixEnd_7299739 : Nat := 4983230072969 + 3 ^ 40 * 7299739 * 2
def baseEnd_7299739 : Nat := 3748274759370720471291617

theorem tailTrace_7299739 : CollatzResearch.WordTrace tailWord_7299739 prefixEnd_7299739 3748274759370720471291617 := by
  unfold tailWord_7299739
  simp only [CollatzResearch.WordTrace]
  refine ⟨266243354101299774011758271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177495569400866516007838847 266243354101299774011758271)
  ·
    refine ⟨399365031151949661017637407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266243354101299774011758271 399365031151949661017637407)
    ·
      refine ⟨599047546727924491526456111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399365031151949661017637407 599047546727924491526456111)
      ·
        refine ⟨898571320091886737289684167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599047546727924491526456111 898571320091886737289684167)
        ·
          refine ⟨1347856980137830105934526251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898571320091886737289684167 1347856980137830105934526251)
          ·
            refine ⟨2021785470206745158901789377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347856980137830105934526251 2021785470206745158901789377)
            ·
              refine ⟨1516339102655058869176342033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021785470206745158901789377 1516339102655058869176342033)
              ·
                refine ⟨1137254326991294151882256525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516339102655058869176342033 1137254326991294151882256525)
                ·
                  refine ⟨426470372621735306955846197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137254326991294151882256525 426470372621735306955846197)
                  ·
                    refine ⟨39981597433287685027110581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 426470372621735306955846197 39981597433287685027110581)
                    ·
                      refine ⟨3748274759370720471291617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39981597433287685027110581 3748274759370720471291617)
                      ·
                        rfl

theorem cell23_7299739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_7299739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299739 prefixEnd_7299739 := by exact prefixLift 7299739
  have htrace : WordTrace (prefixWord ++ tailWord_7299739) baseStart_7299739 baseEnd_7299739 := by
    simpa [prefixWord, tailWord_7299739, baseEnd_7299739] using wordTrace_append hprefix tailTrace_7299739
  have hstable : (prefixWord ++ tailWord_7299739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299739).length < 2 ^ (prefixWord ++ tailWord_7299739).sum := by decide
  have hdescent : baseEnd_7299739 < baseStart_7299739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299754 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_7299754 : Nat := 118140960795 + 7299754 * 2 ^ 59
def prefixEnd_7299754 : Nat := 4983230072969 + 3 ^ 40 * 7299754 * 2
def baseEnd_7299754 : Nat := 416475829064504212511561

theorem tailTrace_7299754 : CollatzResearch.WordTrace tailWord_7299754 prefixEnd_7299754 416475829064504212511561 := by
  unfold tailWord_7299754
  simp only [CollatzResearch.WordTrace]
  refine ⟨66560975299061357893388579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177495934130830287715702877 66560975299061357893388579)
  ·
    refine ⟨99841462948592036840082869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66560975299061357893388579 99841462948592036840082869)
    ·
      refine ⟨9360137151430503453757769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99841462948592036840082869 9360137151430503453757769)
      ·
        refine ⟨7020102863572877590318327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9360137151430503453757769 7020102863572877590318327)
        ·
          refine ⟨10530154295359316385477491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020102863572877590318327 10530154295359316385477491)
          ·
            refine ⟨15795231443038974578216237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10530154295359316385477491 15795231443038974578216237)
            ·
              refine ⟨5923211791139615466831089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15795231443038974578216237 5923211791139615466831089)
              ·
                refine ⟨4442408843354711600123317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923211791139615466831089 4442408843354711600123317)
                ·
                  refine ⟨416475829064504212511561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442408843354711600123317 416475829064504212511561)
                  ·
                    rfl

theorem cell23_7299754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_7299754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299754 prefixEnd_7299754 := by exact prefixLift 7299754
  have htrace : WordTrace (prefixWord ++ tailWord_7299754) baseStart_7299754 baseEnd_7299754 := by
    simpa [prefixWord, tailWord_7299754, baseEnd_7299754] using wordTrace_append hprefix tailTrace_7299754
  have hstable : (prefixWord ++ tailWord_7299754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299754).length < 2 ^ (prefixWord ++ tailWord_7299754).sum := by decide
  have hdescent : baseEnd_7299754 < baseStart_7299754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299763 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 3, 4]
def baseStart_7299763 : Nat := 118140960795 + 7299763 * 2 ^ 59
def prefixEnd_7299763 : Nat := 4983230072969 + 3 ^ 40 * 7299763 * 2
def baseEnd_7299763 : Nat := 1249429027635476125797169

theorem tailTrace_7299763 : CollatzResearch.WordTrace tailWord_7299763 prefixEnd_7299763 1249429027635476125797169 := by
  unfold tailWord_7299763
  simp only [CollatzResearch.WordTrace]
  refine ⟨266244229453212826110631943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177496152968808550740421295 266244229453212826110631943)
  ·
    refine ⟨399366344179819239165947915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266244229453212826110631943 399366344179819239165947915)
    ·
      refine ⟨599049516269728858748921873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399366344179819239165947915 599049516269728858748921873)
      ·
        refine ⟨449287137202296644061691405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599049516269728858748921873 449287137202296644061691405)
        ·
          refine ⟨168482676450861241523134277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449287137202296644061691405 168482676450861241523134277)
          ·
            refine ⟨31590501834536482785587677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168482676450861241523134277 31590501834536482785587677)
            ·
              refine ⟨11846438187951181044595379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31590501834536482785587677 11846438187951181044595379)
              ·
                refine ⟨17769657281926771566893069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11846438187951181044595379 17769657281926771566893069)
                ·
                  refine ⟨6663621480722539337584901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17769657281926771566893069 6663621480722539337584901)
                  ·
                    refine ⟨1249429027635476125797169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663621480722539337584901 1249429027635476125797169)
                    ·
                      rfl

theorem cell23_7299763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 4].length) (baseStart_7299763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299763 prefixEnd_7299763 := by exact prefixLift 7299763
  have htrace : WordTrace (prefixWord ++ tailWord_7299763) baseStart_7299763 baseEnd_7299763 := by
    simpa [prefixWord, tailWord_7299763, baseEnd_7299763] using wordTrace_append hprefix tailTrace_7299763
  have hstable : (prefixWord ++ tailWord_7299763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299763).length < 2 ^ (prefixWord ++ tailWord_7299763).sum := by decide
  have hdescent : baseEnd_7299763 < baseStart_7299763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299790 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_7299790 : Nat := 118140960795 + 7299790 * 2 ^ 59
def prefixEnd_7299790 : Nat := 4983230072969 + 3 ^ 40 * 7299790 * 2
def baseEnd_7299790 : Nat := 3748300946884099771753883

theorem tailTrace_7299790 : CollatzResearch.WordTrace tailWord_7299790 prefixEnd_7299790 3748300946884099771753883 := by
  unfold tailWord_7299790
  simp only [CollatzResearch.WordTrace]
  refine ⟨33280651778014376215233103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177496809482743339814576549 33280651778014376215233103)
  ·
    refine ⟨49920977667021564322849655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33280651778014376215233103 49920977667021564322849655)
    ·
      refine ⟨74881466500532346484274483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49920977667021564322849655 74881466500532346484274483)
      ·
        refine ⟨112322199750798519726411725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74881466500532346484274483 112322199750798519726411725)
        ·
          refine ⟨42120824906549444897404397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112322199750798519726411725 42120824906549444897404397)
          ·
            refine ⟨15795309339956041836526649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42120824906549444897404397 15795309339956041836526649)
            ·
              refine ⟨11846482004967031377394987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15795309339956041836526649 11846482004967031377394987)
              ·
                refine ⟨17769723007450547066092481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11846482004967031377394987 17769723007450547066092481)
                ·
                  refine ⟨13327292255587910299569361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17769723007450547066092481 13327292255587910299569361)
                  ·
                    refine ⟨9995469191690932724677021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13327292255587910299569361 9995469191690932724677021)
                    ·
                      refine ⟨3748300946884099771753883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9995469191690932724677021 3748300946884099771753883)
                      ·
                        rfl

theorem cell23_7299790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_7299790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299790 prefixEnd_7299790 := by exact prefixLift 7299790
  have htrace : WordTrace (prefixWord ++ tailWord_7299790) baseStart_7299790 baseEnd_7299790 := by
    simpa [prefixWord, tailWord_7299790, baseEnd_7299790] using wordTrace_append hprefix tailTrace_7299790
  have hstable : (prefixWord ++ tailWord_7299790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299790).length < 2 ^ (prefixWord ++ tailWord_7299790).sum := by decide
  have hdescent : baseEnd_7299790 < baseStart_7299790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299830 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7299830 : Nat := 118140960795 + 7299830 * 2 ^ 59
def prefixEnd_7299830 : Nat := 4983230072969 + 3 ^ 40 * 7299830 * 2
def baseEnd_7299830 : Nat := 3748321486110279615253699

theorem tailTrace_7299830 : CollatzResearch.WordTrace tailWord_7299830 prefixEnd_7299830 3748321486110279615253699 := by
  unfold tailWord_7299830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640417071498131034582559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177497782095980064368880629 16640417071498131034582559)
  ·
    refine ⟨24960625607247196551873839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16640417071498131034582559 24960625607247196551873839)
    ·
      refine ⟨37440938410870794827810759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24960625607247196551873839 37440938410870794827810759)
      ·
        refine ⟨56161407616306192241716139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37440938410870794827810759 56161407616306192241716139)
        ·
          refine ⟨84242111424459288362574209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56161407616306192241716139 84242111424459288362574209)
          ·
            refine ⟨63181583568344466271930657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84242111424459288362574209 63181583568344466271930657)
            ·
              refine ⟨47386187676258349703947993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63181583568344466271930657 47386187676258349703947993)
              ·
                refine ⟨35539640757193762277960995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47386187676258349703947993 35539640757193762277960995)
                ·
                  refine ⟨53309461135790643416941493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35539640757193762277960995 53309461135790643416941493)
                  ·
                    refine ⟨4997761981480372820338265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53309461135790643416941493 4997761981480372820338265)
                    ·
                      refine ⟨3748321486110279615253699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997761981480372820338265 3748321486110279615253699)
                      ·
                        rfl

theorem cell23_7299830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7299830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299830 prefixEnd_7299830 := by exact prefixLift 7299830
  have htrace : WordTrace (prefixWord ++ tailWord_7299830) baseStart_7299830 baseEnd_7299830 := by
    simpa [prefixWord, tailWord_7299830, baseEnd_7299830] using wordTrace_append hprefix tailTrace_7299830
  have hstable : (prefixWord ++ tailWord_7299830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299830).length < 2 ^ (prefixWord ++ tailWord_7299830).sum := by decide
  have hdescent : baseEnd_7299830 < baseStart_7299830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299843 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 4]
def baseStart_7299843 : Nat := 118140960795 + 7299843 * 2 ^ 59
def prefixEnd_7299843 : Nat := 4983230072969 + 3 ^ 40 * 7299843 * 2
def baseEnd_7299843 : Nat := 3748328161358788064391139

theorem tailTrace_7299843 : CollatzResearch.WordTrace tailWord_7299843 prefixEnd_7299843 3748328161358788064391139 := by
  unfold tailWord_7299843
  simp only [CollatzResearch.WordTrace]
  refine ⟨266247147292922999773544183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177498098195281999849029455 266247147292922999773544183)
  ·
    refine ⟨399370720939384499660316275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266247147292922999773544183 399370720939384499660316275)
    ·
      refine ⟨599056081409076749490474413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399370720939384499660316275 599056081409076749490474413)
      ·
        refine ⟨224646030528403781058927905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 599056081409076749490474413 224646030528403781058927905)
        ·
          refine ⟨168484522896302835794195929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224646030528403781058927905 168484522896302835794195929)
          ·
            refine ⟨126363392172227126845646947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168484522896302835794195929 126363392172227126845646947)
            ·
              refine ⟨189545088258340690268470421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126363392172227126845646947 189545088258340690268470421)
              ·
                refine ⟨8884926012109719856334551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189545088258340690268470421 8884926012109719856334551)
                ·
                  refine ⟨13327389018164579784501827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8884926012109719856334551 13327389018164579784501827)
                  ·
                    refine ⟨19991083527246869676752741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13327389018164579784501827 19991083527246869676752741)
                    ·
                      refine ⟨3748328161358788064391139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19991083527246869676752741 3748328161358788064391139)
                      ·
                        rfl

theorem cell23_7299843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_7299843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299843 prefixEnd_7299843 := by exact prefixLift 7299843
  have htrace : WordTrace (prefixWord ++ tailWord_7299843) baseStart_7299843 baseEnd_7299843 := by
    simpa [prefixWord, tailWord_7299843, baseEnd_7299843] using wordTrace_append hprefix tailTrace_7299843
  have hstable : (prefixWord ++ tailWord_7299843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299843).length < 2 ^ (prefixWord ++ tailWord_7299843).sum := by decide
  have hdescent : baseEnd_7299843 < baseStart_7299843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299847 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7299847 : Nat := 118140960795 + 7299847 * 2 ^ 59
def prefixEnd_7299847 : Nat := 4983230072969 + 3 ^ 40 * 7299847 * 2
def baseEnd_7299847 : Nat := 3748330215281406048741121

theorem tailTrace_7299847 : CollatzResearch.WordTrace tailWord_7299847 prefixEnd_7299847 3748330215281406048741121 := by
  unfold tailWord_7299847
  simp only [CollatzResearch.WordTrace]
  refine ⟨266247293184908508456689795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177498195456605672304459863 266247293184908508456689795)
  ·
    refine ⟨399370939777362762685034693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266247293184908508456689795 399370939777362762685034693)
    ·
      refine ⟨74882051208255518003444005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399370939777362762685034693 74882051208255518003444005)
      ·
        refine ⟨14040384601547909625645751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74882051208255518003444005 14040384601547909625645751)
        ·
          refine ⟨21060576902321864438468627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14040384601547909625645751 21060576902321864438468627)
          ·
            refine ⟨31590865353482796657702941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21060576902321864438468627 31590865353482796657702941)
            ·
              refine ⟨11846574507556048746638603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31590865353482796657702941 11846574507556048746638603)
              ·
                refine ⟨17769861761334073119957905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11846574507556048746638603 17769861761334073119957905)
                ·
                  refine ⟨13327396321000554839968429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17769861761334073119957905 13327396321000554839968429)
                  ·
                    refine ⟨4997773620375208064988161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13327396321000554839968429 4997773620375208064988161)
                    ·
                      refine ⟨3748330215281406048741121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997773620375208064988161 3748330215281406048741121)
                      ·
                        rfl

theorem cell23_7299847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7299847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299847 prefixEnd_7299847 := by exact prefixLift 7299847
  have htrace : WordTrace (prefixWord ++ tailWord_7299847) baseStart_7299847 baseEnd_7299847 := by
    simpa [prefixWord, tailWord_7299847, baseEnd_7299847] using wordTrace_append hprefix tailTrace_7299847
  have hstable : (prefixWord ++ tailWord_7299847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299847).length < 2 ^ (prefixWord ++ tailWord_7299847).sum := by decide
  have hdescent : baseEnd_7299847 < baseStart_7299847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299866 : List Nat := [3, 1, 1, 3, 2, 1, 12]
def baseStart_7299866 : Nat := 118140960795 + 7299866 * 2 ^ 59
def prefixEnd_7299866 : Nat := 4983230072969 + 3 ^ 40 * 7299866 * 2
def baseEnd_7299866 : Nat := 46275802116220265116093

theorem tailTrace_7299866 : CollatzResearch.WordTrace tailWord_7299866 prefixEnd_7299866 46275802116220265116093 := by
  unfold tailWord_7299866
  simp only [CollatzResearch.WordTrace]
  refine ⟨66561996542959918675407863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177498657447893116467754301 66561996542959918675407863)
  ·
    refine ⟨99842994814439878013111795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66561996542959918675407863 99842994814439878013111795)
    ·
      refine ⟨149764492221659817019667693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99842994814439878013111795 149764492221659817019667693)
      ·
        refine ⟨56161684583122431382375385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149764492221659817019667693 56161684583122431382375385)
        ·
          refine ⟨42121263437341823536781539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56161684583122431382375385 42121263437341823536781539)
          ·
            refine ⟨63181895156012735305172309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42121263437341823536781539 63181895156012735305172309)
            ·
              refine ⟨46275802116220265116093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63181895156012735305172309 46275802116220265116093)
              ·
                rfl

theorem cell23_7299866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 12].length) (baseStart_7299866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299866 prefixEnd_7299866 := by exact prefixLift 7299866
  have htrace : WordTrace (prefixWord ++ tailWord_7299866) baseStart_7299866 baseEnd_7299866 := by
    simpa [prefixWord, tailWord_7299866, baseEnd_7299866] using wordTrace_append hprefix tailTrace_7299866
  have hstable : (prefixWord ++ tailWord_7299866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299866).length < 2 ^ (prefixWord ++ tailWord_7299866).sum := by decide
  have hdescent : baseEnd_7299866 < baseStart_7299866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299877 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 3, 2, 2]
def baseStart_7299877 : Nat := 118140960795 + 7299877 * 2 ^ 59
def prefixEnd_7299877 : Nat := 4983230072969 + 3 ^ 40 * 7299877 * 2
def baseEnd_7299877 : Nat := 3748345619701040931365983

theorem tailTrace_7299877 : CollatzResearch.WordTrace tailWord_7299877 prefixEnd_7299877 3748345619701040931365983 := by
  unfold tailWord_7299877
  simp only [CollatzResearch.WordTrace]
  refine ⟨266248387374799823580281885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177498924916533215720187923 266248387374799823580281885)
  ·
    refine ⟨99843145265549933842605707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266248387374799823580281885 99843145265549933842605707)
    ·
      refine ⟨149764717898324900763908561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99843145265549933842605707 149764717898324900763908561)
      ·
        refine ⟨112323538423743675572931421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149764717898324900763908561 112323538423743675572931421)
        ·
          refine ⟨42121326908903878339849283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112323538423743675572931421 42121326908903878339849283)
          ·
            refine ⟨63181990363355817509773925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42121326908903878339849283 63181990363355817509773925)
            ·
              refine ⟨11846623193129215783082611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63181990363355817509773925 11846623193129215783082611)
              ·
                refine ⟨17769934789693823674623917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11846623193129215783082611 17769934789693823674623917)
                ·
                  refine ⟨6663725546135183877983969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17769934789693823674623917 6663725546135183877983969)
                  ·
                    refine ⟨4997794159601387908487977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6663725546135183877983969 4997794159601387908487977)
                    ·
                      refine ⟨3748345619701040931365983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997794159601387908487977 3748345619701040931365983)
                      ·
                        rfl

theorem cell23_7299877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_7299877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299877 prefixEnd_7299877 := by exact prefixLift 7299877
  have htrace : WordTrace (prefixWord ++ tailWord_7299877) baseStart_7299877 baseEnd_7299877 := by
    simpa [prefixWord, tailWord_7299877, baseEnd_7299877] using wordTrace_append hprefix tailTrace_7299877
  have hstable : (prefixWord ++ tailWord_7299877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299877).length < 2 ^ (prefixWord ++ tailWord_7299877).sum := by decide
  have hdescent : baseEnd_7299877 < baseStart_7299877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299894 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7299894 : Nat := 118140960795 + 7299894 * 2 ^ 59
def prefixEnd_7299894 : Nat := 4983230072969 + 3 ^ 40 * 7299894 * 2
def baseEnd_7299894 : Nat := 3748354348872167364853405

theorem tailTrace_7299894 : CollatzResearch.WordTrace tailWord_7299894 prefixEnd_7299894 3748354348872167364853405 := by
  unfold tailWord_7299894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640562963483639717728171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177499338277158823655767157 16640562963483639717728171)
  ·
    refine ⟨24960844445225459576592257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16640562963483639717728171 24960844445225459576592257)
    ·
      refine ⟨18720633333919094682444193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24960844445225459576592257 18720633333919094682444193)
      ·
        refine ⟨14040475000439321011833145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18720633333919094682444193 14040475000439321011833145)
        ·
          refine ⟨10530356250329490758874859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14040475000439321011833145 10530356250329490758874859)
          ·
            refine ⟨15795534375494236138312289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10530356250329490758874859 15795534375494236138312289)
            ·
              refine ⟨11846650781620677103734217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15795534375494236138312289 11846650781620677103734217)
              ·
                refine ⟨8884988086215507827800663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11846650781620677103734217 8884988086215507827800663)
                ·
                  refine ⟨13327482129323261741700995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8884988086215507827800663 13327482129323261741700995)
                  ·
                    refine ⟨19991223193984892612551493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13327482129323261741700995 19991223193984892612551493)
                    ·
                      refine ⟨3748354348872167364853405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19991223193984892612551493 3748354348872167364853405)
                      ·
                        rfl

theorem cell23_7299894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7299894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299894 prefixEnd_7299894 := by exact prefixLift 7299894
  have htrace : WordTrace (prefixWord ++ tailWord_7299894) baseStart_7299894 baseEnd_7299894 := by
    simpa [prefixWord, tailWord_7299894, baseEnd_7299894] using wordTrace_append hprefix tailTrace_7299894
  have hstable : (prefixWord ++ tailWord_7299894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299894).length < 2 ^ (prefixWord ++ tailWord_7299894).sum := by decide
  have hdescent : baseEnd_7299894 < baseStart_7299894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299917 : List Nat := [1, 6, 1, 2, 3, 1, 9]
def baseStart_7299917 : Nat := 118140960795 + 7299917 * 2 ^ 59
def prefixEnd_7299917 : Nat := 4983230072969 + 3 ^ 40 * 7299917 * 2
def baseEnd_7299917 : Nat := 46276125418854577467479

theorem tailTrace_7299917 : CollatzResearch.WordTrace tailWord_7299917 prefixEnd_7299917 46276125418854577467479 := by
  unfold tailWord_7299917
  simp only [CollatzResearch.WordTrace]
  refine ⟨266249846294654910411738005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177499897529769940274492003 266249846294654910411738005)
  ·
    refine ⟨12480461545061948925550219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 266249846294654910411738005 12480461545061948925550219)
    ·
      refine ⟨18720692317592923388325329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12480461545061948925550219 18720692317592923388325329)
      ·
        refine ⟨14040519238194692541243997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18720692317592923388325329 14040519238194692541243997)
        ·
          refine ⟨5265194714323009702966499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14040519238194692541243997 5265194714323009702966499)
          ·
            refine ⟨7897792071484514554449749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265194714323009702966499 7897792071484514554449749)
            ·
              refine ⟨46276125418854577467479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7897792071484514554449749 46276125418854577467479)
              ·
                rfl

theorem cell23_7299917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 9].length) (baseStart_7299917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299917 prefixEnd_7299917 := by exact prefixLift 7299917
  have htrace : WordTrace (prefixWord ++ tailWord_7299917) baseStart_7299917 baseEnd_7299917 := by
    simpa [prefixWord, tailWord_7299917, baseEnd_7299917] using wordTrace_append hprefix tailTrace_7299917
  have hstable : (prefixWord ++ tailWord_7299917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299917).length < 2 ^ (prefixWord ++ tailWord_7299917).sum := by decide
  have hdescent : baseEnd_7299917 < baseStart_7299917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299944 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_7299944 : Nat := 118140960795 + 7299944 * 2 ^ 59
def prefixEnd_7299944 : Nat := 4983230072969 + 3 ^ 40 * 7299944 * 2
def baseEnd_7299944 : Nat := 3748380022904892169228175

theorem tailTrace_7299944 : CollatzResearch.WordTrace tailWord_7299944 prefixEnd_7299944 3748380022904892169228175 := by
  unfold tailWord_7299944
  simp only [CollatzResearch.WordTrace]
  refine ⟨133125415532778547011485443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177500554043704729348647257 133125415532778547011485443)
  ·
    refine ⟨199688123299167820517228165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133125415532778547011485443 199688123299167820517228165)
    ·
      refine ⟨37441523118593966346980281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199688123299167820517228165 37441523118593966346980281)
      ·
        refine ⟨28081142338945474760235211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37441523118593966346980281 28081142338945474760235211)
        ·
          refine ⟨42121713508418212140352817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28081142338945474760235211 42121713508418212140352817)
          ·
            refine ⟨31591285131313659105264613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42121713508418212140352817 31591285131313659105264613)
            ·
              refine ⟨5923365962121311082237115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31591285131313659105264613 5923365962121311082237115)
              ·
                refine ⟨8885048943181966623355673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923365962121311082237115 8885048943181966623355673)
                ·
                  refine ⟨6663786707386474967516755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8885048943181966623355673 6663786707386474967516755)
                  ·
                    refine ⟨9995680061079712451275133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6663786707386474967516755 9995680061079712451275133)
                    ·
                      refine ⟨3748380022904892169228175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9995680061079712451275133 3748380022904892169228175)
                      ·
                        rfl

theorem cell23_7299944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_7299944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299944 prefixEnd_7299944 := by exact prefixLift 7299944
  have htrace : WordTrace (prefixWord ++ tailWord_7299944) baseStart_7299944 baseEnd_7299944 := by
    simpa [prefixWord, tailWord_7299944, baseEnd_7299944] using wordTrace_append hprefix tailTrace_7299944
  have hstable : (prefixWord ++ tailWord_7299944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299944).length < 2 ^ (prefixWord ++ tailWord_7299944).sum := by decide
  have hdescent : baseEnd_7299944 < baseStart_7299944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299953 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_7299953 : Nat := 118140960795 + 7299953 * 2 ^ 59
def prefixEnd_7299953 : Nat := 4983230072969 + 3 ^ 40 * 7299953 * 2
def baseEnd_7299953 : Nat := 3748384644230782634015633

theorem tailTrace_7299953 : CollatzResearch.WordTrace tailWord_7299953 prefixEnd_7299953 3748384644230782634015633 := by
  unfold tailWord_7299953
  simp only [CollatzResearch.WordTrace]
  refine ⟨266251159322524488560048513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177500772881682992373365675 266251159322524488560048513)
  ·
    refine ⟨199688369491893366420036385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266251159322524488560048513 199688369491893366420036385)
    ·
      refine ⟨149766277118920024815027289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199688369491893366420036385 149766277118920024815027289)
      ·
        refine ⟨112324707839190018611270467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149766277118920024815027289 112324707839190018611270467)
        ·
          refine ⟨168487061758785027916905701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112324707839190018611270467 168487061758785027916905701)
          ·
            refine ⟨31591324079772192734419819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168487061758785027916905701 31591324079772192734419819)
            ·
              refine ⟨47386986119658289101629729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31591324079772192734419819 47386986119658289101629729)
              ·
                refine ⟨35540239589743716826222297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47386986119658289101629729 35540239589743716826222297)
                ·
                  refine ⟨26655179692307787619666723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35540239589743716826222297 26655179692307787619666723)
                  ·
                    refine ⟨39982769538461681429500085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26655179692307787619666723 39982769538461681429500085)
                    ·
                      refine ⟨3748384644230782634015633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39982769538461681429500085 3748384644230782634015633)
                      ·
                        rfl

theorem cell23_7299953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_7299953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7299953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7299953 prefixEnd_7299953 := by exact prefixLift 7299953
  have htrace : WordTrace (prefixWord ++ tailWord_7299953) baseStart_7299953 baseEnd_7299953 := by
    simpa [prefixWord, tailWord_7299953, baseEnd_7299953] using wordTrace_append hprefix tailTrace_7299953
  have hstable : (prefixWord ++ tailWord_7299953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299953).length < 2 ^ (prefixWord ++ tailWord_7299953).sum := by decide
  have hdescent : baseEnd_7299953 < baseStart_7299953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300003 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 4, 5]
def baseStart_7300003 : Nat := 118140960795 + 7300003 * 2 ^ 59
def prefixEnd_7300003 : Nat := 4983230072969 + 3 ^ 40 * 7300003 * 2
def baseEnd_7300003 : Nat := 1249470106087835812796801

theorem tailTrace_7300003 : CollatzResearch.WordTrace tailWord_7300003 prefixEnd_7300003 1249470106087835812796801 := by
  unfold tailWord_7300003
  simp only [CollatzResearch.WordTrace]
  refine ⟨266252982972343347099368663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177501988648228898066245775 266252982972343347099368663)
  ·
    refine ⟨399379474458515020649052995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266252982972343347099368663 399379474458515020649052995)
    ·
      refine ⟨599069211687772530973579493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399379474458515020649052995 599069211687772530973579493)
      ·
        refine ⟨112325477191457349557546155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599069211687772530973579493 112325477191457349557546155)
        ·
          refine ⟨168488215787186024336319233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112325477191457349557546155 168488215787186024336319233)
          ·
            refine ⟨126366161840389518252239425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168488215787186024336319233 126366161840389518252239425)
            ·
              refine ⟨94774621380292138689179569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126366161840389518252239425 94774621380292138689179569)
              ·
                refine ⟨71080966035219104016884677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94774621380292138689179569 71080966035219104016884677)
                ·
                  refine ⟨13327681131603582003165877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71080966035219104016884677 13327681131603582003165877)
                  ·
                    refine ⟨1249470106087835812796801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13327681131603582003165877 1249470106087835812796801)
                    ·
                      rfl

theorem cell23_7300003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 5].length) (baseStart_7300003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300003 prefixEnd_7300003 := by exact prefixLift 7300003
  have htrace : WordTrace (prefixWord ++ tailWord_7300003) baseStart_7300003 baseEnd_7300003 := by
    simpa [prefixWord, tailWord_7300003, baseEnd_7300003] using wordTrace_append hprefix tailTrace_7300003
  have hstable : (prefixWord ++ tailWord_7300003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300003).length < 2 ^ (prefixWord ++ tailWord_7300003).sum := by decide
  have hdescent : baseEnd_7300003 < baseStart_7300003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300022 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7300022 : Nat := 118140960795 + 7300022 * 2 ^ 59
def prefixEnd_7300022 : Nat := 4983230072969 + 3 ^ 40 * 7300022 * 2
def baseEnd_7300022 : Nat := 3748420074395942864052817

theorem tailTrace_7300022 : CollatzResearch.WordTrace tailWord_7300022 prefixEnd_7300022 3748420074395942864052817 := by
  unfold tailWord_7300022
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640854747454657084019395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177502450639516342229540213 16640854747454657084019395)
  ·
    refine ⟨24961282121181985626029093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16640854747454657084019395 24961282121181985626029093)
    ·
      refine ⟨4680240397721622304880455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24961282121181985626029093 4680240397721622304880455)
      ·
        refine ⟨7020360596582433457320683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680240397721622304880455 7020360596582433457320683)
        ·
          refine ⟨10530540894873650185981025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020360596582433457320683 10530540894873650185981025)
          ·
            refine ⟨7897905671155237639485769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10530540894873650185981025 7897905671155237639485769)
            ·
              refine ⟨5923429253366428229614327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7897905671155237639485769 5923429253366428229614327)
              ·
                refine ⟨8885143880049642344421491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923429253366428229614327 8885143880049642344421491)
                ·
                  refine ⟨13327715820074463516632237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8885143880049642344421491 13327715820074463516632237)
                  ·
                    refine ⟨4997893432527923818737089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13327715820074463516632237 4997893432527923818737089)
                    ·
                      refine ⟨3748420074395942864052817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997893432527923818737089 3748420074395942864052817)
                      ·
                        rfl

theorem cell23_7300022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7300022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300022 prefixEnd_7300022 := by exact prefixLift 7300022
  have htrace : WordTrace (prefixWord ++ tailWord_7300022) baseStart_7300022 baseEnd_7300022 := by
    simpa [prefixWord, tailWord_7300022, baseEnd_7300022] using wordTrace_append hprefix tailTrace_7300022
  have hstable : (prefixWord ++ tailWord_7300022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300022).length < 2 ^ (prefixWord ++ tailWord_7300022).sum := by decide
  have hdescent : baseEnd_7300022 < baseStart_7300022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300057 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 2, 4, 2]
def baseStart_7300057 : Nat := 118140960795 + 7300057 * 2 ^ 59
def prefixEnd_7300057 : Nat := 4983230072969 + 3 ^ 40 * 7300057 * 2
def baseEnd_7300057 : Nat := 3748438046218850227115155

theorem tailTrace_7300057 : CollatzResearch.WordTrace tailWord_7300057 prefixEnd_7300057 3748438046218850227115155 := by
  unfold tailWord_7300057
  simp only [CollatzResearch.WordTrace]
  refine ⟨266254952514147714321834425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177503301676098476214556283 266254952514147714321834425)
  ·
    refine ⟨199691214385610785741375819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266254952514147714321834425 199691214385610785741375819)
    ·
      refine ⟨299536821578416178612063729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199691214385610785741375819 299536821578416178612063729)
      ·
        refine ⟨224652616183812133959047797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299536821578416178612063729 224652616183812133959047797)
        ·
          refine ⟨21061182767232387558660731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224652616183812133959047797 21061182767232387558660731)
          ·
            refine ⟨31591774150848581337991097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21061182767232387558660731 31591774150848581337991097)
            ·
              refine ⟨23693830613136436003493323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31591774150848581337991097 23693830613136436003493323)
              ·
                refine ⟨35540745919704654005239985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23693830613136436003493323 35540745919704654005239985)
                ·
                  refine ⟨26655559439778490503929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35540745919704654005239985 26655559439778490503929989)
                  ·
                    refine ⟨4997917394958466969486873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26655559439778490503929989 4997917394958466969486873)
                    ·
                      refine ⟨3748438046218850227115155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4997917394958466969486873 3748438046218850227115155)
                      ·
                        rfl

theorem cell23_7300057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_7300057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300057 prefixEnd_7300057 := by exact prefixLift 7300057
  have htrace : WordTrace (prefixWord ++ tailWord_7300057) baseStart_7300057 baseEnd_7300057 := by
    simpa [prefixWord, tailWord_7300057, baseEnd_7300057] using wordTrace_append hprefix tailTrace_7300057
  have hstable : (prefixWord ++ tailWord_7300057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300057).length < 2 ^ (prefixWord ++ tailWord_7300057).sum := by decide
  have hdescent : baseEnd_7300057 < baseStart_7300057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300127 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 1, 5]
def baseStart_7300127 : Nat := 118140960795 + 7300127 * 2 ^ 59
def prefixEnd_7300127 : Nat := 4983230072969 + 3 ^ 40 * 7300127 * 2
def baseEnd_7300127 : Nat := 1249491329954888317746611

theorem tailTrace_7300127 : CollatzResearch.WordTrace tailWord_7300127 prefixEnd_7300127 1249491329954888317746611 := by
  unfold tailWord_7300127
  simp only [CollatzResearch.WordTrace]
  refine ⟨266257505623894116276882635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177505003749262744184588423 266257505623894116276882635)
  ·
    refine ⟨399386258435841174415323953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266257505623894116276882635 399386258435841174415323953)
    ·
      refine ⟨299539693826880880811492965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399386258435841174415323953 299539693826880880811492965)
      ·
        refine ⟨56163692592540165152154931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299539693826880880811492965 56163692592540165152154931)
        ·
          refine ⟨84245538888810247728232397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56163692592540165152154931 84245538888810247728232397)
          ·
            refine ⟨31592077083303842898087149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84245538888810247728232397 31592077083303842898087149)
            ·
              refine ⟨11847028906238941086782681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31592077083303842898087149 11847028906238941086782681)
              ·
                refine ⟨8885271679679205815087011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11847028906238941086782681 8885271679679205815087011)
                ·
                  refine ⟨13327907519518808722630517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8885271679679205815087011 13327907519518808722630517)
                  ·
                    refine ⟨1249491329954888317746611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13327907519518808722630517 1249491329954888317746611)
                    ·
                      rfl

theorem cell23_7300127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_7300127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300127 prefixEnd_7300127 := by exact prefixLift 7300127
  have htrace : WordTrace (prefixWord ++ tailWord_7300127) baseStart_7300127 baseEnd_7300127 := by
    simpa [prefixWord, tailWord_7300127, baseEnd_7300127] using wordTrace_append hprefix tailTrace_7300127
  have hstable : (prefixWord ++ tailWord_7300127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300127).length < 2 ^ (prefixWord ++ tailWord_7300127).sum := by decide
  have hdescent : baseEnd_7300127 < baseStart_7300127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300140 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_7300140 : Nat := 118140960795 + 7300140 * 2 ^ 59
def prefixEnd_7300140 : Nat := 4983230072969 + 3 ^ 40 * 7300140 * 2
def baseEnd_7300140 : Nat := 1249493555037724467459091

theorem tailTrace_7300140 : CollatzResearch.WordTrace tailWord_7300140 prefixEnd_7300140 1249493555037724467459091 := by
  unfold tailWord_7300140
  simp only [CollatzResearch.WordTrace]
  refine ⟨133128989886423509748552937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177505319848564679664737249 133128989886423509748552937)
  ·
    refine ⟨99846742414817632311414703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133128989886423509748552937 99846742414817632311414703)
    ·
      refine ⟨149770113622226448467122055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99846742414817632311414703 149770113622226448467122055)
      ·
        refine ⟨224655170433339672700683083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149770113622226448467122055 224655170433339672700683083)
        ·
          refine ⟨336982755650009509051024625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224655170433339672700683083 336982755650009509051024625)
          ·
            refine ⟨252737066737507131788268469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336982755650009509051024625 252737066737507131788268469)
            ·
              refine ⟨23694100006641293605150169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252737066737507131788268469 23694100006641293605150169)
              ·
                refine ⟨17770575004980970203862627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23694100006641293605150169 17770575004980970203862627)
                ·
                  refine ⟨26655862507471455305793941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17770575004980970203862627 26655862507471455305793941)
                  ·
                    refine ⟨1249493555037724467459091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26655862507471455305793941 1249493555037724467459091)
                    ·
                      rfl

theorem cell23_7300140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_7300140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300140 prefixEnd_7300140 := by exact prefixLift 7300140
  have htrace : WordTrace (prefixWord ++ tailWord_7300140) baseStart_7300140 baseEnd_7300140 := by
    simpa [prefixWord, tailWord_7300140, baseEnd_7300140] using wordTrace_append hprefix tailTrace_7300140
  have hstable : (prefixWord ++ tailWord_7300140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300140).length < 2 ^ (prefixWord ++ tailWord_7300140).sum := by decide
  have hdescent : baseEnd_7300140 < baseStart_7300140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300158 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_7300158 : Nat := 118140960795 + 7300158 * 2 ^ 59
def prefixEnd_7300158 : Nat := 4983230072969 + 3 ^ 40 * 7300158 * 2
def baseEnd_7300158 : Nat := 3748489907764954331952191

theorem tailTrace_7300158 : CollatzResearch.WordTrace tailWord_7300158 prefixEnd_7300158 3748489907764954331952191 := by
  unfold tailWord_7300158
  simp only [CollatzResearch.WordTrace]
  refine ⟨33282329535847726071407641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177505757524521205714174085 33282329535847726071407641)
  ·
    refine ⟨24961747151885794553555731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33282329535847726071407641 24961747151885794553555731)
    ·
      refine ⟨37442620727828691830333597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24961747151885794553555731 37442620727828691830333597)
      ·
        refine ⟨14040982772935759436375099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37442620727828691830333597 14040982772935759436375099)
        ·
          refine ⟨21061474159403639154562649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14040982772935759436375099 21061474159403639154562649)
          ·
            refine ⟨15796105619552729365921987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21061474159403639154562649 15796105619552729365921987)
            ·
              refine ⟨23694158429329094048882981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796105619552729365921987 23694158429329094048882981)
              ·
                refine ⟨4442654705499205134165559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23694158429329094048882981 4442654705499205134165559)
                ·
                  refine ⟨6663982058248807701248339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442654705499205134165559 6663982058248807701248339)
                  ·
                    refine ⟨9995973087373211551872509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6663982058248807701248339 9995973087373211551872509)
                    ·
                      refine ⟨3748489907764954331952191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9995973087373211551872509 3748489907764954331952191)
                      ·
                        rfl

theorem cell23_7300158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_7300158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300158 prefixEnd_7300158 := by exact prefixLift 7300158
  have htrace : WordTrace (prefixWord ++ tailWord_7300158) baseStart_7300158 baseEnd_7300158 := by
    simpa [prefixWord, tailWord_7300158, baseEnd_7300158] using wordTrace_append hprefix tailTrace_7300158
  have hstable : (prefixWord ++ tailWord_7300158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300158).length < 2 ^ (prefixWord ++ tailWord_7300158).sum := by decide
  have hdescent : baseEnd_7300158 < baseStart_7300158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300160 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_7300160 : Nat := 118140960795 + 7300160 * 2 ^ 59
def prefixEnd_7300160 : Nat := 4983230072969 + 3 ^ 40 * 7300160 * 2
def baseEnd_7300160 : Nat := 3748490934726263324127181

theorem tailTrace_7300160 : CollatzResearch.WordTrace tailWord_7300160 prefixEnd_7300160 3748490934726263324127181 := by
  unfold tailWord_7300160
  simp only [CollatzResearch.WordTrace]
  refine ⟨133129354616387281456416967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177505806155183041941889289 133129354616387281456416967)
  ·
    refine ⟨199694031924580922184625451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133129354616387281456416967 199694031924580922184625451)
    ·
      refine ⟨299541047886871383276938177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199694031924580922184625451 299541047886871383276938177)
      ·
        refine ⟨224655785915153537457703633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299541047886871383276938177 224655785915153537457703633)
        ·
          refine ⟨168491839436365153093277725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224655785915153537457703633 168491839436365153093277725)
          ·
            refine ⟨63184439788636932409979147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168491839436365153093277725 63184439788636932409979147)
            ·
              refine ⟨94776659682955398614968721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63184439788636932409979147 94776659682955398614968721)
              ·
                refine ⟨71082494762216548961226541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94776659682955398614968721 71082494762216548961226541)
                ·
                  refine ⟨26655935535831205860459953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71082494762216548961226541 26655935535831205860459953)
                  ·
                    refine ⟨19991951651873404395344965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26655935535831205860459953 19991951651873404395344965)
                    ·
                      refine ⟨3748490934726263324127181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19991951651873404395344965 3748490934726263324127181)
                      ·
                        rfl

theorem cell23_7300160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_7300160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300160 prefixEnd_7300160 := by exact prefixLift 7300160
  have htrace : WordTrace (prefixWord ++ tailWord_7300160) baseStart_7300160 baseEnd_7300160 := by
    simpa [prefixWord, tailWord_7300160, baseEnd_7300160] using wordTrace_append hprefix tailTrace_7300160
  have hstable : (prefixWord ++ tailWord_7300160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300160).length < 2 ^ (prefixWord ++ tailWord_7300160).sum := by decide
  have hdescent : baseEnd_7300160 < baseStart_7300160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300167 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_7300167 : Nat := 118140960795 + 7300167 * 2 ^ 59
def prefixEnd_7300167 : Nat := 4983230072969 + 3 ^ 40 * 7300167 * 2
def baseEnd_7300167 : Nat := 3748494529090844796739649

theorem tailTrace_7300167 : CollatzResearch.WordTrace tailWord_7300167 prefixEnd_7300167 3748494529090844796739649 := by
  unfold tailWord_7300167
  simp only [CollatzResearch.WordTrace]
  refine ⟨266258964543749203108338755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177505976362499468738892503 266258964543749203108338755)
  ·
    refine ⟨399388446815623804662508133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266258964543749203108338755 399388446815623804662508133)
    ·
      refine ⟨74885333777929463374220275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399388446815623804662508133 74885333777929463374220275)
      ·
        refine ⟨112328000666894195061330413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74885333777929463374220275 112328000666894195061330413)
        ·
          refine ⟨42123000250085323147998905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112328000666894195061330413 42123000250085323147998905)
          ·
            refine ⟨31592250187563992360999179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42123000250085323147998905 31592250187563992360999179)
            ·
              refine ⟨47388375281345988541498769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31592250187563992360999179 47388375281345988541498769)
              ·
                refine ⟨35541281461009491406124077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47388375281345988541498769 35541281461009491406124077)
                ·
                  refine ⟨13327980547878559277296529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35541281461009491406124077 13327980547878559277296529)
                  ·
                    refine ⟨9995985410908919457972397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13327980547878559277296529 9995985410908919457972397)
                    ·
                      refine ⟨3748494529090844796739649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9995985410908919457972397 3748494529090844796739649)
                      ·
                        rfl

theorem cell23_7300167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_7300167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300167 prefixEnd_7300167 := by exact prefixLift 7300167
  have htrace : WordTrace (prefixWord ++ tailWord_7300167) baseStart_7300167 baseEnd_7300167 := by
    simpa [prefixWord, tailWord_7300167, baseEnd_7300167] using wordTrace_append hprefix tailTrace_7300167
  have hstable : (prefixWord ++ tailWord_7300167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300167).length < 2 ^ (prefixWord ++ tailWord_7300167).sum := by decide
  have hdescent : baseEnd_7300167 < baseStart_7300167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300170 : List Nat := [3, 1, 2, 1, 1, 2, 5, 8]
def baseStart_7300170 : Nat := 118140960795 + 7300170 * 2 ^ 59
def prefixEnd_7300170 : Nat := 4983230072969 + 3 ^ 40 * 7300170 * 2
def baseEnd_7300170 : Nat := 138833187760474380926005

theorem tailTrace_7300170 : CollatzResearch.WordTrace tailWord_7300170 prefixEnd_7300170 138833187760474380926005 := by
  unfold tailWord_7300170
  simp only [CollatzResearch.WordTrace]
  refine ⟨66564768490684583655174491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177506049308492223080465309 66564768490684583655174491)
  ·
    refine ⟨99847152736026875482761737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66564768490684583655174491 99847152736026875482761737)
    ·
      refine ⟨74885364552020156612071303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99847152736026875482761737 74885364552020156612071303)
      ·
        refine ⟨112328046828030234918106955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74885364552020156612071303 112328046828030234918106955)
        ·
          refine ⟨168492070242045352377160433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112328046828030234918106955 168492070242045352377160433)
          ·
            refine ⟨126369052681534014282870325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168492070242045352377160433 126369052681534014282870325)
            ·
              refine ⟨11847098688893813839019093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126369052681534014282870325 11847098688893813839019093)
              ·
                refine ⟨138833187760474380926005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11847098688893813839019093 138833187760474380926005)
                ·
                  rfl

theorem cell23_7300170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_7300170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300170 prefixEnd_7300170 := by exact prefixLift 7300170
  have htrace : WordTrace (prefixWord ++ tailWord_7300170) baseStart_7300170 baseEnd_7300170 := by
    simpa [prefixWord, tailWord_7300170, baseEnd_7300170] using wordTrace_append hprefix tailTrace_7300170
  have hstable : (prefixWord ++ tailWord_7300170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300170).length < 2 ^ (prefixWord ++ tailWord_7300170).sum := by decide
  have hdescent : baseEnd_7300170 < baseStart_7300170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300194 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7300194 : Nat := 118140960795 + 7300194 * 2 ^ 59
def prefixEnd_7300194 : Nat := 4983230072969 + 3 ^ 40 * 7300194 * 2
def baseEnd_7300194 : Nat := 3748508393068516191102025

theorem tailTrace_7300194 : CollatzResearch.WordTrace tailWord_7300194 prefixEnd_7300194 3748508393068516191102025 := by
  unfold tailWord_7300194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66564987328662846679892909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177506632876434257813047757 66564987328662846679892909)
  ·
    refine ⟨24961870248248567504959841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66564987328662846679892909 24961870248248567504959841)
    ·
      refine ⟨18721402686186425628719881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24961870248248567504959841 18721402686186425628719881)
      ·
        refine ⟨14041052014639819221539911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18721402686186425628719881 14041052014639819221539911)
        ·
          refine ⟨21061578021959728832309867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14041052014639819221539911 21061578021959728832309867)
          ·
            refine ⟨31592367032939593248464801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21061578021959728832309867 31592367032939593248464801)
            ·
              refine ⟨23694275274704694936348601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31592367032939593248464801 23694275274704694936348601)
              ·
                refine ⟨17770706456028521202261451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23694275274704694936348601 17770706456028521202261451)
                ·
                  refine ⟨26656059684042781803392177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17770706456028521202261451 26656059684042781803392177)
                  ·
                    refine ⟨19992044763032086352544133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26656059684042781803392177 19992044763032086352544133)
                    ·
                      refine ⟨3748508393068516191102025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19992044763032086352544133 3748508393068516191102025)
                      ·
                        rfl

theorem cell23_7300194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7300194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300194 prefixEnd_7300194 := by exact prefixLift 7300194
  have htrace : WordTrace (prefixWord ++ tailWord_7300194) baseStart_7300194 baseEnd_7300194 := by
    simpa [prefixWord, tailWord_7300194, baseEnd_7300194] using wordTrace_append hprefix tailTrace_7300194
  have hstable : (prefixWord ++ tailWord_7300194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300194).length < 2 ^ (prefixWord ++ tailWord_7300194).sum := by decide
  have hdescent : baseEnd_7300194 < baseStart_7300194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300197 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_7300197 : Nat := 118140960795 + 7300197 * 2 ^ 59
def prefixEnd_7300197 : Nat := 4983230072969 + 3 ^ 40 * 7300197 * 2
def baseEnd_7300197 : Nat := 3748509933510479679364511

theorem tailTrace_7300197 : CollatzResearch.WordTrace tailWord_7300197 prefixEnd_7300197 3748509933510479679364511 := by
  unfold tailWord_7300197
  simp only [CollatzResearch.WordTrace]
  refine ⟨266260058733640518231930845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177506705822427012154620563 266260058733640518231930845)
  ·
    refine ⟨99847522025115194336974067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266260058733640518231930845 99847522025115194336974067)
    ·
      refine ⟨149771283037672791505461101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99847522025115194336974067 149771283037672791505461101)
      ·
        refine ⟨56164231139127296814547913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149771283037672791505461101 56164231139127296814547913)
        ·
          refine ⟨42123173354345472610910935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56164231139127296814547913 42123173354345472610910935)
          ·
            refine ⟨63184760031518208916366403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42123173354345472610910935 63184760031518208916366403)
            ·
              refine ⟨94777140047277313374549605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63184760031518208916366403 94777140047277313374549605)
              ·
                refine ⟨17770713758864496257728051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94777140047277313374549605 17770713758864496257728051)
                ·
                  refine ⟨26656070638296744386592077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17770713758864496257728051 26656070638296744386592077)
                  ·
                    refine ⟨9996026489361279144972029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26656070638296744386592077 9996026489361279144972029)
                    ·
                      refine ⟨3748509933510479679364511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996026489361279144972029 3748509933510479679364511)
                      ·
                        rfl

theorem cell23_7300197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_7300197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300197 prefixEnd_7300197 := by exact prefixLift 7300197
  have htrace : WordTrace (prefixWord ++ tailWord_7300197) baseStart_7300197 baseEnd_7300197 := by
    simpa [prefixWord, tailWord_7300197, baseEnd_7300197] using wordTrace_append hprefix tailTrace_7300197
  have hstable : (prefixWord ++ tailWord_7300197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300197).length < 2 ^ (prefixWord ++ tailWord_7300197).sum := by decide
  have hdescent : baseEnd_7300197 < baseStart_7300197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300201 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 1, 2, 3]
def baseStart_7300201 : Nat := 118140960795 + 7300201 * 2 ^ 59
def prefixEnd_7300201 : Nat := 4983230072969 + 3 ^ 40 * 7300201 * 2
def baseEnd_7300201 : Nat := 3748511987433097663714493

theorem tailTrace_7300201 : CollatzResearch.WordTrace tailWord_7300201 prefixEnd_7300201 3748511987433097663714493 := by
  unfold tailWord_7300201
  simp only [CollatzResearch.WordTrace]
  refine ⟨266260204625626026915076457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177506803083750684610050971 266260204625626026915076457)
  ·
    refine ⟨199695153469219520186307343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266260204625626026915076457 199695153469219520186307343)
    ·
      refine ⟨299542730203829280279461015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199695153469219520186307343 299542730203829280279461015)
      ·
        refine ⟨449314095305743920419191523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299542730203829280279461015 449314095305743920419191523)
        ·
          refine ⟨673971142958615880628787285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449314095305743920419191523 673971142958615880628787285)
          ·
            refine ⟨7898099331546279851118601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 673971142958615880628787285 7898099331546279851118601)
            ·
              refine ⟨5923574498659709888338951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7898099331546279851118601 5923574498659709888338951)
              ·
                refine ⟨8885361747989564832508427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923574498659709888338951 8885361747989564832508427)
                ·
                  refine ⟨13328042621984347248762641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8885361747989564832508427 13328042621984347248762641)
                  ·
                    refine ⟨9996031966488260436571981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13328042621984347248762641 9996031966488260436571981)
                    ·
                      refine ⟨3748511987433097663714493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996031966488260436571981 3748511987433097663714493)
                      ·
                        rfl

theorem cell23_7300201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 2, 3].length) (baseStart_7300201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300201 prefixEnd_7300201 := by exact prefixLift 7300201
  have htrace : WordTrace (prefixWord ++ tailWord_7300201) baseStart_7300201 baseEnd_7300201 := by
    simpa [prefixWord, tailWord_7300201, baseEnd_7300201] using wordTrace_append hprefix tailTrace_7300201
  have hstable : (prefixWord ++ tailWord_7300201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300201).length < 2 ^ (prefixWord ++ tailWord_7300201).sum := by decide
  have hdescent : baseEnd_7300201 < baseStart_7300201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
