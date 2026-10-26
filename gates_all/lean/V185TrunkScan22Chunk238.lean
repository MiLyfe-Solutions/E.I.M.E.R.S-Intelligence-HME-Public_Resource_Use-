import V185TrunkScan22Chunk237

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2122431 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 4]
def baseStart_2122431 : Nat := 118140960795 + 2122431 * 2 ^ 59
def prefixEnd_2122431 : Nat := 4983230072969 + 3 ^ 40 * 2122431 * 2
def baseEnd_2122431 : Nat := 242183835333975713922583

theorem tailTrace_2122431 : CollatzResearch.WordTrace tailWord_2122431 prefixEnd_2122431 242183835333975713922583 := by
  unfold tailWord_2122431
  simp only [CollatzResearch.WordTrace]
  refine ⟨77411418173802444201215147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51607612115868296134143431 77411418173802444201215147)
  ·
    refine ⟨116117127260703666301822721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77411418173802444201215147 116117127260703666301822721)
    ·
      refine ⟨87087845445527749726367041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116117127260703666301822721 87087845445527749726367041)
      ·
        refine ⟨65315884084145812294775281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87087845445527749726367041 65315884084145812294775281)
        ·
          refine ⟨48986913063109359221081461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65315884084145812294775281 48986913063109359221081461)
          ·
            refine ⟨4592523099666502426976387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48986913063109359221081461 4592523099666502426976387)
            ·
              refine ⟨6888784649499753640464581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4592523099666502426976387 6888784649499753640464581)
              ·
                refine ⟨1291647121781203807587109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6888784649499753640464581 1291647121781203807587109)
                ·
                  refine ⟨242183835333975713922583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291647121781203807587109 242183835333975713922583)
                  ·
                    rfl

theorem cell22_2122431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 4].length) (baseStart_2122431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122431 prefixEnd_2122431 := by exact prefixLift 2122431
  have htrace : WordTrace (prefixWord ++ tailWord_2122431) baseStart_2122431 baseEnd_2122431 := by
    simpa [prefixWord, tailWord_2122431, baseEnd_2122431] using wordTrace_append hprefix tailTrace_2122431
  have hstable : (prefixWord ++ tailWord_2122431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122431).length < 2 ^ (prefixWord ++ tailWord_2122431).sum := by decide
  have hdescent : baseEnd_2122431 < baseStart_2122431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122446 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2122446 : Nat := 118140960795 + 2122446 * 2 ^ 59
def prefixEnd_2122446 : Nat := 4983230072969 + 3 ^ 40 * 2122446 * 2
def baseEnd_2122446 : Nat := 726556640808472102642703

theorem tailTrace_2122446 : CollatzResearch.WordTrace tailWord_2122446 prefixEnd_2122446 726556640808472102642703 := by
  unfold tailWord_2122446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676495658593512720376399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51607976845832067842007461 9676495658593512720376399)
  ·
    refine ⟨14514743487890269080564599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9676495658593512720376399 14514743487890269080564599)
    ·
      refine ⟨21772115231835403620846899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14514743487890269080564599 21772115231835403620846899)
      ·
        refine ⟨32658172847753105431270349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21772115231835403620846899 32658172847753105431270349)
        ·
          refine ⟨12246814817907414536726381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32658172847753105431270349 12246814817907414536726381)
          ·
            refine ⟨4592555556715280451272393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12246814817907414536726381 4592555556715280451272393)
            ·
              refine ⟨3444416667536460338454295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592555556715280451272393 3444416667536460338454295)
              ·
                refine ⟨5166625001304690507681443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444416667536460338454295 5166625001304690507681443)
                ·
                  refine ⟨7749937501957035761522165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166625001304690507681443 7749937501957035761522165)
                  ·
                    refine ⟨726556640808472102642703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7749937501957035761522165 726556640808472102642703)
                    ·
                      rfl

theorem cell22_2122446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2122446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122446 prefixEnd_2122446 := by exact prefixLift 2122446
  have htrace : WordTrace (prefixWord ++ tailWord_2122446) baseStart_2122446 baseEnd_2122446 := by
    simpa [prefixWord, tailWord_2122446, baseEnd_2122446] using wordTrace_append hprefix tailTrace_2122446
  have hstable : (prefixWord ++ tailWord_2122446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122446).length < 2 ^ (prefixWord ++ tailWord_2122446).sum := by decide
  have hdescent : baseEnd_2122446 < baseStart_2122446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122579 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_2122579 : Nat := 118140960795 + 2122579 * 2 ^ 59
def prefixEnd_2122579 : Nat := 4983230072969 + 3 ^ 40 * 2122579 * 2
def baseEnd_2122579 : Nat := 726602169426504089067295

theorem tailTrace_2122579 : CollatzResearch.WordTrace tailWord_2122579 prefixEnd_2122579 726602169426504089067295 := by
  unfold tailWord_2122579
  simp only [CollatzResearch.WordTrace]
  refine ⟨77416816177266265477602791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51611210784844176985068527 77416816177266265477602791)
  ·
    refine ⟨116125224265899398216404187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77416816177266265477602791 116125224265899398216404187)
    ·
      refine ⟨174187836398849097324606281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116125224265899398216404187 174187836398849097324606281)
      ·
        refine ⟨130640877299136822993454711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174187836398849097324606281 130640877299136822993454711)
        ·
          refine ⟨195961315948705234490182067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130640877299136822993454711 195961315948705234490182067)
          ·
            refine ⟨293941973923057851735273101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195961315948705234490182067 293941973923057851735273101)
            ·
              refine ⟨110228240221146694400727413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293941973923057851735273101 110228240221146694400727413)
              ·
                refine ⟨10333897520732502600068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110228240221146694400727413 10333897520732502600068195)
                ·
                  refine ⟨15500846281098753900102293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10333897520732502600068195 15500846281098753900102293)
                  ·
                    refine ⟨726602169426504089067295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15500846281098753900102293 726602169426504089067295)
                    ·
                      rfl

theorem cell22_2122579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_2122579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122579 prefixEnd_2122579 := by exact prefixLift 2122579
  have htrace : WordTrace (prefixWord ++ tailWord_2122579) baseStart_2122579 baseEnd_2122579 := by
    simpa [prefixWord, tailWord_2122579, baseEnd_2122579] using wordTrace_append hprefix tailTrace_2122579
  have hstable : (prefixWord ++ tailWord_2122579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122579).length < 2 ^ (prefixWord ++ tailWord_2122579).sum := by decide
  have hdescent : baseEnd_2122579 < baseStart_2122579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122581 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2122581 : Nat := 118140960795 + 2122581 * 2 ^ 59
def prefixEnd_2122581 : Nat := 4983230072969 + 3 ^ 40 * 2122581 * 2
def baseEnd_2122581 : Nat := 726602854067376750517289

theorem tailTrace_2122581 : CollatzResearch.WordTrace tailWord_2122581 prefixEnd_2122581 726602854067376750517289 := by
  unfold tailWord_2122581
  simp only [CollatzResearch.WordTrace]
  refine ⟨77416889123259019819175597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51611259415506013212783731 77416889123259019819175597)
  ·
    refine ⟨29031333421222132432190849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77416889123259019819175597 29031333421222132432190849)
    ·
      refine ⟨21773500065916599324143137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29031333421222132432190849 21773500065916599324143137)
      ·
        refine ⟨16330125049437449493107353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21773500065916599324143137 16330125049437449493107353)
        ·
          refine ⟨12247593787078087119830515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16330125049437449493107353 12247593787078087119830515)
          ·
            refine ⟨18371390680617130679745773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12247593787078087119830515 18371390680617130679745773)
            ·
              refine ⟨6889271505231424004904665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18371390680617130679745773 6889271505231424004904665)
              ·
                refine ⟨5166953628923568003678499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6889271505231424004904665 5166953628923568003678499)
                ·
                  refine ⟨7750430443385352005517749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166953628923568003678499 7750430443385352005517749)
                  ·
                    refine ⟨726602854067376750517289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7750430443385352005517749 726602854067376750517289)
                    ·
                      rfl

theorem cell22_2122581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2122581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122581 prefixEnd_2122581 := by exact prefixLift 2122581
  have htrace : WordTrace (prefixWord ++ tailWord_2122581) baseStart_2122581 baseEnd_2122581 := by
    simpa [prefixWord, tailWord_2122581, baseEnd_2122581] using wordTrace_append hprefix tailTrace_2122581
  have hstable : (prefixWord ++ tailWord_2122581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122581).length < 2 ^ (prefixWord ++ tailWord_2122581).sum := by decide
  have hdescent : baseEnd_2122581 < baseStart_2122581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122600 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 4]
def baseStart_2122600 : Nat := 118140960795 + 2122600 * 2 ^ 59
def prefixEnd_2122600 : Nat := 4983230072969 + 3 ^ 40 * 2122600 * 2
def baseEnd_2122600 : Nat := 242203119385222344764077

theorem tailTrace_2122600 : CollatzResearch.WordTrace tailWord_2122600 prefixEnd_2122600 242203119385222344764077 := by
  unfold tailWord_2122600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38708791055095093032058627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51611721406793457376078169 38708791055095093032058627)
  ·
    refine ⟨58063186582642639548087941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38708791055095093032058627 58063186582642639548087941)
    ·
      refine ⟨10886847484245494915266489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58063186582642639548087941 10886847484245494915266489)
      ·
        refine ⟨8165135613184121186449867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10886847484245494915266489 8165135613184121186449867)
        ·
          refine ⟨12247703419776181779674801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8165135613184121186449867 12247703419776181779674801)
          ·
            refine ⟨9185777564832136334756101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12247703419776181779674801 9185777564832136334756101)
            ·
              refine ⟨1722333293406025562766769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9185777564832136334756101 1722333293406025562766769)
              ·
                refine ⟨1291749970054519172075077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722333293406025562766769 1291749970054519172075077)
                ·
                  refine ⟨242203119385222344764077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291749970054519172075077 242203119385222344764077)
                  ·
                    rfl

theorem cell22_2122600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_2122600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122600 prefixEnd_2122600 := by exact prefixLift 2122600
  have htrace : WordTrace (prefixWord ++ tailWord_2122600) baseStart_2122600 baseEnd_2122600 := by
    simpa [prefixWord, tailWord_2122600, baseEnd_2122600] using wordTrace_append hprefix tailTrace_2122600
  have hstable : (prefixWord ++ tailWord_2122600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122600).length < 2 ^ (prefixWord ++ tailWord_2122600).sum := by decide
  have hdescent : baseEnd_2122600 < baseStart_2122600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122660 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_2122660 : Nat := 118140960795 + 2122660 * 2 ^ 59
def prefixEnd_2122660 : Nat := 4983230072969 + 3 ^ 40 * 2122660 * 2
def baseEnd_2122660 : Nat := 726629897381846877792047

theorem tailTrace_2122660 : CollatzResearch.WordTrace tailWord_2122660 prefixEnd_2122660 726629897381846877792047 := by
  unfold tailWord_2122660
  simp only [CollatzResearch.WordTrace]
  refine ⟨38709885244986408155650717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51613180326648544207534289 38709885244986408155650717)
  ·
    refine ⟨14516206966869903058369019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38709885244986408155650717 14516206966869903058369019)
    ·
      refine ⟨21774310450304854587553529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14516206966869903058369019 21774310450304854587553529)
      ·
        refine ⟨16330732837728640940665147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21774310450304854587553529 16330732837728640940665147)
        ·
          refine ⟨24496099256592961410997721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16330732837728640940665147 24496099256592961410997721)
          ·
            refine ⟨18372074442444721058248291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24496099256592961410997721 18372074442444721058248291)
            ·
              refine ⟨27558111663667081587372437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18372074442444721058248291 27558111663667081587372437)
              ·
                refine ⟨1291786484234394449408083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27558111663667081587372437 1291786484234394449408083)
                ·
                  refine ⟨1937679726351591674112125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291786484234394449408083 1937679726351591674112125)
                  ·
                    refine ⟨726629897381846877792047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937679726351591674112125 726629897381846877792047)
                    ·
                      rfl

theorem cell22_2122660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_2122660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122660 prefixEnd_2122660 := by exact prefixLift 2122660
  have htrace : WordTrace (prefixWord ++ tailWord_2122660) baseStart_2122660 baseEnd_2122660 := by
    simpa [prefixWord, tailWord_2122660, baseEnd_2122660] using wordTrace_append hprefix tailTrace_2122660
  have hstable : (prefixWord ++ tailWord_2122660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122660).length < 2 ^ (prefixWord ++ tailWord_2122660).sum := by decide
  have hdescent : baseEnd_2122660 < baseStart_2122660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122703 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 1, 4]
def baseStart_2122703 : Nat := 118140960795 + 2122703 * 2 ^ 59
def prefixEnd_2122703 : Nat := 4983230072969 + 3 ^ 40 * 2122703 * 2
def baseEnd_2122703 : Nat := 726644617160609098966915

theorem tailTrace_2122703 : CollatzResearch.WordTrace tailWord_2122703 prefixEnd_2122703 726644617160609098966915 := by
  unfold tailWord_2122703
  simp only [CollatzResearch.WordTrace]
  refine ⟨77421338828817034655116763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51614225885878023103411175 77421338828817034655116763)
  ·
    refine ⟨116132008243225551982675145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77421338828817034655116763 116132008243225551982675145)
    ·
      refine ⟨87099006182419163987006359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116132008243225551982675145 87099006182419163987006359)
      ·
        refine ⟨130648509273628745980509539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87099006182419163987006359 130648509273628745980509539)
        ·
          refine ⟨195972763910443118970764309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130648509273628745980509539 195972763910443118970764309)
          ·
            refine ⟨9186223308302021201754577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 195972763910443118970764309 9186223308302021201754577)
            ·
              refine ⟨6889667481226515901315933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186223308302021201754577 6889667481226515901315933)
              ·
                refine ⟨2583625305459943462993475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6889667481226515901315933 2583625305459943462993475)
                ·
                  refine ⟨3875437958189915194490213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583625305459943462993475 3875437958189915194490213)
                  ·
                    refine ⟨726644617160609098966915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875437958189915194490213 726644617160609098966915)
                    ·
                      rfl

theorem cell22_2122703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_2122703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122703 prefixEnd_2122703 := by exact prefixLift 2122703
  have htrace : WordTrace (prefixWord ++ tailWord_2122703) baseStart_2122703 baseEnd_2122703 := by
    simpa [prefixWord, tailWord_2122703, baseEnd_2122703] using wordTrace_append hprefix tailTrace_2122703
  have hstable : (prefixWord ++ tailWord_2122703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122703).length < 2 ^ (prefixWord ++ tailWord_2122703).sum := by decide
  have hdescent : baseEnd_2122703 < baseStart_2122703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122748 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_2122748 : Nat := 118140960795 + 2122748 * 2 ^ 59
def prefixEnd_2122748 : Nat := 4983230072969 + 3 ^ 40 * 2122748 * 2
def baseEnd_2122748 : Nat := 726660021580243981591777

theorem tailTrace_2122748 : CollatzResearch.WordTrace tailWord_2122748 prefixEnd_2122748 726660021580243981591777 := by
  unfold tailWord_2122748
  simp only [CollatzResearch.WordTrace]
  refine ⟨38711490056827003670252449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51615320075769338227003265 38711490056827003670252449)
  ·
    refine ⟨29033617542620252752689337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38711490056827003670252449 29033617542620252752689337)
    ·
      refine ⟨21775213156965189564517003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29033617542620252752689337 21775213156965189564517003)
      ·
        refine ⟨32662819735447784346775505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21775213156965189564517003 32662819735447784346775505)
        ·
          refine ⟨24497114801585838260081629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32662819735447784346775505 24497114801585838260081629)
          ·
            refine ⟨9186418050594689347530611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24497114801585838260081629 9186418050594689347530611)
            ·
              refine ⟨13779627075892034021295917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186418050594689347530611 13779627075892034021295917)
              ·
                refine ⟨5167360153459512757985969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13779627075892034021295917 5167360153459512757985969)
                ·
                  refine ⟨3875520115094634568489477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5167360153459512757985969 3875520115094634568489477)
                  ·
                    refine ⟨726660021580243981591777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875520115094634568489477 726660021580243981591777)
                    ·
                      rfl

theorem cell22_2122748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_2122748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122748 prefixEnd_2122748 := by exact prefixLift 2122748
  have htrace : WordTrace (prefixWord ++ tailWord_2122748) baseStart_2122748 baseEnd_2122748 := by
    simpa [prefixWord, tailWord_2122748, baseEnd_2122748] using wordTrace_append hprefix tailTrace_2122748
  have hstable : (prefixWord ++ tailWord_2122748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122748).length < 2 ^ (prefixWord ++ tailWord_2122748).sum := by decide
  have hdescent : baseEnd_2122748 < baseStart_2122748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122780 : List Nat := [2, 2, 3, 1, 4, 2, 1, 7]
def baseStart_2122780 : Nat := 118140960795 + 2122780 * 2 ^ 59
def prefixEnd_2122780 : Nat := 4983230072969 + 3 ^ 40 * 2122780 * 2
def baseEnd_2122780 : Nat := 80741219537134062754631

theorem tailTrace_2122780 : CollatzResearch.WordTrace tailWord_2122780 prefixEnd_2122780 80741219537134062754631 := by
  unfold tailWord_2122780
  simp only [CollatzResearch.WordTrace]
  refine ⟨38712073624769038402834897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51616098166358717870446529 38712073624769038402834897)
  ·
    refine ⟨29034055218576778802126173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38712073624769038402834897 29034055218576778802126173)
    ·
      refine ⟨10887770706966292050797315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29034055218576778802126173 10887770706966292050797315)
      ·
        refine ⟨16331656060449438076195973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10887770706966292050797315 16331656060449438076195973)
        ·
          refine ⟨3062185511334269639286745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16331656060449438076195973 3062185511334269639286745)
          ·
            refine ⟨2296639133500702229465059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3062185511334269639286745 2296639133500702229465059)
            ·
              refine ⟨3444958700251053344197589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296639133500702229465059 3444958700251053344197589)
              ·
                refine ⟨80741219537134062754631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3444958700251053344197589 80741219537134062754631)
                ·
                  rfl

theorem cell22_2122780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 7].length) (baseStart_2122780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122780 prefixEnd_2122780 := by exact prefixLift 2122780
  have htrace : WordTrace (prefixWord ++ tailWord_2122780) baseStart_2122780 baseEnd_2122780 := by
    simpa [prefixWord, tailWord_2122780, baseEnd_2122780] using wordTrace_append hprefix tailTrace_2122780
  have hstable : (prefixWord ++ tailWord_2122780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122780).length < 2 ^ (prefixWord ++ tailWord_2122780).sum := by decide
  have hdescent : baseEnd_2122780 < baseStart_2122780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122812 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_2122812 : Nat := 118140960795 + 2122812 * 2 ^ 59
def prefixEnd_2122812 : Nat := 4983230072969 + 3 ^ 40 * 2122812 * 2
def baseEnd_2122812 : Nat := 726681930088169147991581

theorem tailTrace_2122812 : CollatzResearch.WordTrace tailWord_2122812 prefixEnd_2122812 726681930088169147991581 := by
  unfold tailWord_2122812
  simp only [CollatzResearch.WordTrace]
  refine ⟨38712657192711073135417345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51616876256948097513889793 38712657192711073135417345)
  ·
    refine ⟨29034492894533304851563009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38712657192711073135417345 29034492894533304851563009)
    ·
      refine ⟨21775869670899978638672257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29034492894533304851563009 21775869670899978638672257)
      ·
        refine ⟨16331902253174983979004193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21775869670899978638672257 16331902253174983979004193)
        ·
          refine ⟨12248926689881237984253145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16331902253174983979004193 12248926689881237984253145)
          ·
            refine ⟨9186695017410928488189859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12248926689881237984253145 9186695017410928488189859)
            ·
              refine ⟨13780042526116392732284789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186695017410928488189859 13780042526116392732284789)
              ·
                refine ⟨1291878986823411818651699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13780042526116392732284789 1291878986823411818651699)
                ·
                  refine ⟨1937818480235117727977549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291878986823411818651699 1937818480235117727977549)
                  ·
                    refine ⟨726681930088169147991581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937818480235117727977549 726681930088169147991581)
                    ·
                      rfl

theorem cell22_2122812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_2122812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122812 prefixEnd_2122812 := by exact prefixLift 2122812
  have htrace : WordTrace (prefixWord ++ tailWord_2122812) baseStart_2122812 baseEnd_2122812 := by
    simpa [prefixWord, tailWord_2122812, baseEnd_2122812] using wordTrace_append hprefix tailTrace_2122812
  have hstable : (prefixWord ++ tailWord_2122812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122812).length < 2 ^ (prefixWord ++ tailWord_2122812).sum := by decide
  have hdescent : baseEnd_2122812 < baseStart_2122812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122823 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2122823 : Nat := 118140960795 + 2122823 * 2 ^ 59
def prefixEnd_2122823 : Nat := 4983230072969 + 3 ^ 40 * 2122823 * 2
def baseEnd_2122823 : Nat := 726685695612968785966547

theorem tailTrace_2122823 : CollatzResearch.WordTrace tailWord_2122823 prefixEnd_2122823 726685695612968785966547 := by
  unfold tailWord_2122823
  simp only [CollatzResearch.WordTrace]
  refine ⟨77425715588382295149485123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51617143725588196766323415 77425715588382295149485123)
  ·
    refine ⟨116138573382573442724227685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77425715588382295149485123 116138573382573442724227685)
    ·
      refine ⟨21775982509232520510792691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116138573382573442724227685 21775982509232520510792691)
      ·
        refine ⟨32663973763848780766189037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21775982509232520510792691 32663973763848780766189037)
        ·
          refine ⟨12248990161443292787320889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32663973763848780766189037 12248990161443292787320889)
          ·
            refine ⟨9186742621082469590490667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12248990161443292787320889 9186742621082469590490667)
            ·
              refine ⟨13780113931623704385736001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186742621082469590490667 13780113931623704385736001)
              ·
                refine ⟨10335085448717778289302001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13780113931623704385736001 10335085448717778289302001)
                ·
                  refine ⟨7751314086538333716976501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10335085448717778289302001 7751314086538333716976501)
                  ·
                    refine ⟨726685695612968785966547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7751314086538333716976501 726685695612968785966547)
                    ·
                      rfl

theorem cell22_2122823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2122823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122823 prefixEnd_2122823 := by exact prefixLift 2122823
  have htrace : WordTrace (prefixWord ++ tailWord_2122823) baseStart_2122823 baseEnd_2122823 := by
    simpa [prefixWord, tailWord_2122823, baseEnd_2122823] using wordTrace_append hprefix tailTrace_2122823
  have hstable : (prefixWord ++ tailWord_2122823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122823).length < 2 ^ (prefixWord ++ tailWord_2122823).sum := by decide
  have hdescent : baseEnd_2122823 < baseStart_2122823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122829 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2122829 : Nat := 118140960795 + 2122829 * 2 ^ 59
def prefixEnd_2122829 : Nat := 4983230072969 + 3 ^ 40 * 2122829 * 2
def baseEnd_2122829 : Nat := 726687749535586770316529

theorem tailTrace_2122829 : CollatzResearch.WordTrace tailWord_2122829 prefixEnd_2122829 726687749535586770316529 := by
  unfold tailWord_2122829
  simp only [CollatzResearch.WordTrace]
  refine ⟨77425934426360558174203541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51617289617573705449469027 77425934426360558174203541)
  ·
    refine ⟨3629340676235651164415791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77425934426360558174203541 3629340676235651164415791)
    ·
      refine ⟨5444011014353476746623687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3629340676235651164415791 5444011014353476746623687)
      ·
        refine ⟨8166016521530215119935531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5444011014353476746623687 8166016521530215119935531)
        ·
          refine ⟨12249024782295322679903297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8166016521530215119935531 12249024782295322679903297)
          ·
            refine ⟨9186768586721492009927473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12249024782295322679903297 9186768586721492009927473)
            ·
              refine ⟨6890076440041119007445605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186768586721492009927473 6890076440041119007445605)
              ·
                refine ⟨1291889332507709813896051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6890076440041119007445605 1291889332507709813896051)
                ·
                  refine ⟨1937833998761564720844077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291889332507709813896051 1937833998761564720844077)
                  ·
                    refine ⟨726687749535586770316529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937833998761564720844077 726687749535586770316529)
                    ·
                      rfl

theorem cell22_2122829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2122829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122829 prefixEnd_2122829 := by exact prefixLift 2122829
  have htrace : WordTrace (prefixWord ++ tailWord_2122829) baseStart_2122829 baseEnd_2122829 := by
    simpa [prefixWord, tailWord_2122829, baseEnd_2122829] using wordTrace_append hprefix tailTrace_2122829
  have hstable : (prefixWord ++ tailWord_2122829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122829).length < 2 ^ (prefixWord ++ tailWord_2122829).sum := by decide
  have hdescent : baseEnd_2122829 < baseStart_2122829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122853 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 6]
def baseStart_2122853 : Nat := 118140960795 + 2122853 * 2 ^ 59
def prefixEnd_2122853 : Nat := 4983230072969 + 3 ^ 40 * 2122853 * 2
def baseEnd_2122853 : Nat := 242231988408686235905485

theorem tailTrace_2122853 : CollatzResearch.WordTrace tailWord_2122853 prefixEnd_2122853 242231988408686235905485 := by
  unfold tailWord_2122853
  simp only [CollatzResearch.WordTrace]
  refine ⟨77426809778273610273077213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51617873185515740182051475 77426809778273610273077213)
  ·
    refine ⟨29035053666852603852403955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77426809778273610273077213 29035053666852603852403955)
    ·
      refine ⟨43552580500278905778605933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29035053666852603852403955 43552580500278905778605933)
      ·
        refine ⟨16332217687604589666977225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43552580500278905778605933 16332217687604589666977225)
        ·
          refine ⟨12249163265703442250232919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16332217687604589666977225 12249163265703442250232919)
          ·
            refine ⟨18373744898555163375349379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12249163265703442250232919 18373744898555163375349379)
            ·
              refine ⟨27560617347832745063024069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18373744898555163375349379 27560617347832745063024069)
              ·
                refine ⟨5167615752718639699317013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27560617347832745063024069 5167615752718639699317013)
                ·
                  refine ⟨242231988408686235905485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5167615752718639699317013 242231988408686235905485)
                  ·
                    rfl

theorem cell22_2122853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_2122853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122853 prefixEnd_2122853 := by exact prefixLift 2122853
  have htrace : WordTrace (prefixWord ++ tailWord_2122853) baseStart_2122853 baseEnd_2122853 := by
    simpa [prefixWord, tailWord_2122853, baseEnd_2122853] using wordTrace_append hprefix tailTrace_2122853
  have hstable : (prefixWord ++ tailWord_2122853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122853).length < 2 ^ (prefixWord ++ tailWord_2122853).sum := by decide
  have hdescent : baseEnd_2122853 < baseStart_2122853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122855 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2122855 : Nat := 118140960795 + 2122855 * 2 ^ 59
def prefixEnd_2122855 : Nat := 4983230072969 + 3 ^ 40 * 2122855 * 2
def baseEnd_2122855 : Nat := 726696649866931369166449

theorem tailTrace_2122855 : CollatzResearch.WordTrace tailWord_2122855 prefixEnd_2122855 726696649866931369166449 := by
  unfold tailWord_2122855
  simp only [CollatzResearch.WordTrace]
  refine ⟨77426882724266364614650019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51617921816177576409766679 77426882724266364614650019)
  ·
    refine ⟨116140324086399546921975029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77426882724266364614650019 116140324086399546921975029)
    ·
      refine ⟨10888155383099957523935159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116140324086399546921975029 10888155383099957523935159)
      ·
        refine ⟨16332233074649936285902739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10888155383099957523935159 16332233074649936285902739)
        ·
          refine ⟨24498349611974904428854109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16332233074649936285902739 24498349611974904428854109)
          ·
            refine ⟨9186881104490589160820291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24498349611974904428854109 9186881104490589160820291)
            ·
              refine ⟨13780321656735883741230437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186881104490589160820291 13780321656735883741230437)
              ·
                refine ⟨2583810310637978201480707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13780321656735883741230437 2583810310637978201480707)
                ·
                  refine ⟨3875715465956967302221061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583810310637978201480707 3875715465956967302221061)
                  ·
                    refine ⟨726696649866931369166449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875715465956967302221061 726696649866931369166449)
                    ·
                      rfl

theorem cell22_2122855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2122855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122855 prefixEnd_2122855 := by exact prefixLift 2122855
  have htrace : WordTrace (prefixWord ++ tailWord_2122855) baseStart_2122855 baseEnd_2122855 := by
    simpa [prefixWord, tailWord_2122855, baseEnd_2122855] using wordTrace_append hprefix tailTrace_2122855
  have hstable : (prefixWord ++ tailWord_2122855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122855).length < 2 ^ (prefixWord ++ tailWord_2122855).sum := by decide
  have hdescent : baseEnd_2122855 < baseStart_2122855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122943 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 7]
def baseStart_2122943 : Nat := 118140960795 + 2122943 * 2 ^ 59
def prefixEnd_2122943 : Nat := 4983230072969 + 3 ^ 40 * 2122943 * 2
def baseEnd_2122943 : Nat := 242242258021776157655393

theorem tailTrace_2122943 : CollatzResearch.WordTrace tailWord_2122943 prefixEnd_2122943 242242258021776157655393 := by
  unfold tailWord_2122943
  simp only [CollatzResearch.WordTrace]
  refine ⟨77430092347947555643853483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51620061565298370429235655 77430092347947555643853483)
  ·
    refine ⟨116145138521921333465780225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77430092347947555643853483 116145138521921333465780225)
    ·
      refine ⟨87108853891441000099335169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116145138521921333465780225 87108853891441000099335169)
      ·
        refine ⟨65331640418580750074501377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87108853891441000099335169 65331640418580750074501377)
        ·
          refine ⟨48998730313935562555876033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65331640418580750074501377 48998730313935562555876033)
          ·
            refine ⟨36749047735451671916907025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48998730313935562555876033 36749047735451671916907025)
            ·
              refine ⟨27561785801588753937680269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36749047735451671916907025 27561785801588753937680269)
              ·
                refine ⟨10335669675595782726630101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27561785801588753937680269 10335669675595782726630101)
                ·
                  refine ⟨242242258021776157655393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10335669675595782726630101 242242258021776157655393)
                  ·
                    rfl

theorem cell22_2122943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_2122943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122943 prefixEnd_2122943 := by exact prefixLift 2122943
  have htrace : WordTrace (prefixWord ++ tailWord_2122943) baseStart_2122943 baseEnd_2122943 := by
    simpa [prefixWord, tailWord_2122943, baseEnd_2122943] using wordTrace_append hprefix tailTrace_2122943
  have hstable : (prefixWord ++ tailWord_2122943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122943).length < 2 ^ (prefixWord ++ tailWord_2122943).sum := by decide
  have hdescent : baseEnd_2122943 < baseStart_2122943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122981 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_2122981 : Nat := 118140960795 + 2122981 * 2 ^ 59
def prefixEnd_2122981 : Nat := 4983230072969 + 3 ^ 40 * 2122981 * 2
def baseEnd_2122981 : Nat := 726739782241909040516063

theorem tailTrace_2122981 : CollatzResearch.WordTrace tailWord_2122981 prefixEnd_2122981 726739782241909040516063 := by
  unfold tailWord_2122981
  simp only [CollatzResearch.WordTrace]
  refine ⟨77431478321809888133736797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51620985547873258755824531 77431478321809888133736797)
  ·
    refine ⟨29036804370678708050151299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77431478321809888133736797 29036804370678708050151299)
    ·
      refine ⟨43555206556018062075226949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29036804370678708050151299 43555206556018062075226949)
      ·
        refine ⟨8166601229253386639105053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43555206556018062075226949 8166601229253386639105053)
        ·
          refine ⟨3062475460970019989664395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8166601229253386639105053 3062475460970019989664395)
          ·
            refine ⟨4593713191455029984496593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062475460970019989664395 4593713191455029984496593)
            ·
              refine ⟨3445284893591272488372445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593713191455029984496593 3445284893591272488372445)
              ·
                refine ⟨1291981835096727183139667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3445284893591272488372445 1291981835096727183139667)
                ·
                  refine ⟨1937972752645090774709501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291981835096727183139667 1937972752645090774709501)
                  ·
                    refine ⟨726739782241909040516063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937972752645090774709501 726739782241909040516063)
                    ·
                      rfl

theorem cell22_2122981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_2122981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122981 prefixEnd_2122981 := by exact prefixLift 2122981
  have htrace : WordTrace (prefixWord ++ tailWord_2122981) baseStart_2122981 baseEnd_2122981 := by
    simpa [prefixWord, tailWord_2122981, baseEnd_2122981] using wordTrace_append hprefix tailTrace_2122981
  have hstable : (prefixWord ++ tailWord_2122981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122981).length < 2 ^ (prefixWord ++ tailWord_2122981).sum := by decide
  have hdescent : baseEnd_2122981 < baseStart_2122981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122994 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_2122994 : Nat := 118140960795 + 2122994 * 2 ^ 59
def prefixEnd_2122994 : Nat := 4983230072969 + 3 ^ 40 * 2122994 * 2
def baseEnd_2122994 : Nat := 242248077469193779980341

theorem tailTrace_2122994 : CollatzResearch.WordTrace tailWord_2122994 prefixEnd_2122994 242248077469193779980341 := by
  unfold tailWord_2122994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19357988117690697838490009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51621301647175194235973357 19357988117690697838490009)
  ·
    refine ⟨14518491088268023378867507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19357988117690697838490009 14518491088268023378867507)
    ·
      refine ⟨21777736632402035068301261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14518491088268023378867507 21777736632402035068301261)
      ·
        refine ⟨8166651237150763150612973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21777736632402035068301261 8166651237150763150612973)
        ·
          refine ⟨3062494213931536181479865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8166651237150763150612973 3062494213931536181479865)
          ·
            refine ⟨2296870660448652136109899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3062494213931536181479865 2296870660448652136109899)
            ·
              refine ⟨3445305990672978204164849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296870660448652136109899 3445305990672978204164849)
              ·
                refine ⟨2583979493004733653123637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445305990672978204164849 2583979493004733653123637)
                ·
                  refine ⟨242248077469193779980341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2583979493004733653123637 242248077469193779980341)
                  ·
                    rfl

theorem cell22_2122994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_2122994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122994 prefixEnd_2122994 := by exact prefixLift 2122994
  have htrace : WordTrace (prefixWord ++ tailWord_2122994) baseStart_2122994 baseEnd_2122994 := by
    simpa [prefixWord, tailWord_2122994, baseEnd_2122994] using wordTrace_append hprefix tailTrace_2122994
  have hstable : (prefixWord ++ tailWord_2122994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122994).length < 2 ^ (prefixWord ++ tailWord_2122994).sum := by decide
  have hdescent : baseEnd_2122994 < baseStart_2122994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123003 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_2123003 : Nat := 118140960795 + 2123003 * 2 ^ 59
def prefixEnd_2123003 : Nat := 4983230072969 + 3 ^ 40 * 2123003 * 2
def baseEnd_2123003 : Nat := 726747313291508316465995

theorem tailTrace_2123003 : CollatzResearch.WordTrace tailWord_2123003 prefixEnd_2123003 726747313291508316465995 := by
  unfold tailWord_2123003
  simp only [CollatzResearch.WordTrace]
  refine ⟨77432280727730185891037663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51621520485153457260691775 77432280727730185891037663)
  ·
    refine ⟨116148421091595278836556495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77432280727730185891037663 116148421091595278836556495)
    ·
      refine ⟨174222631637392918254834743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116148421091595278836556495 174222631637392918254834743)
      ·
        refine ⟨261333947456089377382252115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174222631637392918254834743 261333947456089377382252115)
        ·
          refine ⟨392000921184134066073378173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261333947456089377382252115 392000921184134066073378173)
          ·
            refine ⟨147000345444050274777516815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392000921184134066073378173 147000345444050274777516815)
            ·
              refine ⟨220500518166075412166275223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147000345444050274777516815 220500518166075412166275223)
              ·
                refine ⟨330750777249113118249412835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220500518166075412166275223 330750777249113118249412835)
                ·
                  refine ⟨496126165873669677374119253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330750777249113118249412835 496126165873669677374119253)
                  ·
                    refine ⟨726747313291508316465995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 496126165873669677374119253 726747313291508316465995)
                    ·
                      rfl

theorem cell22_2123003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_2123003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123003 prefixEnd_2123003 := by exact prefixLift 2123003
  have htrace : WordTrace (prefixWord ++ tailWord_2123003) baseStart_2123003 baseEnd_2123003 := by
    simpa [prefixWord, tailWord_2123003, baseEnd_2123003] using wordTrace_append hprefix tailTrace_2123003
  have hstable : (prefixWord ++ tailWord_2123003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123003).length < 2 ^ (prefixWord ++ tailWord_2123003).sum := by decide
  have hdescent : baseEnd_2123003 < baseStart_2123003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123035 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 2, 4]
def baseStart_2123035 : Nat := 118140960795 + 2123035 * 2 ^ 59
def prefixEnd_2123035 : Nat := 4983230072969 + 3 ^ 40 * 2123035 * 2
def baseEnd_2123035 : Nat := 726758267545470899665897

theorem tailTrace_2123035 : CollatzResearch.WordTrace tailWord_2123035 prefixEnd_2123035 726758267545470899665897 := by
  unfold tailWord_2123035
  simp only [CollatzResearch.WordTrace]
  refine ⟨77433447863614255356202559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51622298575742836904135039 77433447863614255356202559)
  ·
    refine ⟨116150171795421383034303839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77433447863614255356202559 116150171795421383034303839)
    ·
      refine ⟨174225257693132074551455759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116150171795421383034303839 174225257693132074551455759)
      ·
        refine ⟨261337886539698111827183639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174225257693132074551455759 261337886539698111827183639)
        ·
          refine ⟨392006829809547167740775459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261337886539698111827183639 392006829809547167740775459)
          ·
            refine ⟨588010244714320751611163189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392006829809547167740775459 588010244714320751611163189)
            ·
              refine ⟨55125960441967570463546549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 588010244714320751611163189 55125960441967570463546549)
              ·
                refine ⟨5168058791434459730957489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55125960441967570463546549 5168058791434459730957489)
                ·
                  refine ⟨3876044093575844798218117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5168058791434459730957489 3876044093575844798218117)
                  ·
                    refine ⟨726758267545470899665897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3876044093575844798218117 726758267545470899665897)
                    ·
                      rfl

theorem cell22_2123035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_2123035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123035 prefixEnd_2123035 := by exact prefixLift 2123035
  have htrace : WordTrace (prefixWord ++ tailWord_2123035) baseStart_2123035 baseEnd_2123035 := by
    simpa [prefixWord, tailWord_2123035, baseEnd_2123035] using wordTrace_append hprefix tailTrace_2123035
  have hstable : (prefixWord ++ tailWord_2123035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123035).length < 2 ^ (prefixWord ++ tailWord_2123035).sum := by decide
  have hdescent : baseEnd_2123035 < baseStart_2123035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123071 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 2, 3]
def baseStart_2123071 : Nat := 118140960795 + 2123071 * 2 ^ 59
def prefixEnd_2123071 : Nat := 4983230072969 + 3 ^ 40 * 2123071 * 2
def baseEnd_2123071 : Nat := 726770591081178805765787

theorem tailTrace_2123071 : CollatzResearch.WordTrace tailWord_2123071 prefixEnd_2123071 726770591081178805765787 := by
  unfold tailWord_2123071
  simp only [CollatzResearch.WordTrace]
  refine ⟨77434760891483833504513067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51623173927655889003008711 77434760891483833504513067)
  ·
    refine ⟨116152141337225750256769601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77434760891483833504513067 116152141337225750256769601)
    ·
      refine ⟨87114106002919312692577201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116152141337225750256769601 87114106002919312692577201)
      ·
        refine ⟨65335579502189484519432901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87114106002919312692577201 65335579502189484519432901)
        ·
          refine ⟨12250421156660528347393669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65335579502189484519432901 12250421156660528347393669)
          ·
            refine ⟨2296953966873849065136313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12250421156660528347393669 2296953966873849065136313)
            ·
              refine ⟨1722715475155386798852235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296953966873849065136313 1722715475155386798852235)
              ·
                refine ⟨2584073212733080198278353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722715475155386798852235 2584073212733080198278353)
                ·
                  refine ⟨1938054909549810148708765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2584073212733080198278353 1938054909549810148708765)
                  ·
                    refine ⟨726770591081178805765787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938054909549810148708765 726770591081178805765787)
                    ·
                      rfl

theorem cell22_2123071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_2123071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123071 prefixEnd_2123071 := by exact prefixLift 2123071
  have htrace : WordTrace (prefixWord ++ tailWord_2123071) baseStart_2123071 baseEnd_2123071 := by
    simpa [prefixWord, tailWord_2123071, baseEnd_2123071] using wordTrace_append hprefix tailTrace_2123071
  have hstable : (prefixWord ++ tailWord_2123071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123071).length < 2 ^ (prefixWord ++ tailWord_2123071).sum := by decide
  have hdescent : baseEnd_2123071 < baseStart_2123071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123082 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_2123082 : Nat := 118140960795 + 2123082 * 2 ^ 59
def prefixEnd_2123082 : Nat := 4983230072969 + 3 ^ 40 * 2123082 * 2
def baseEnd_2123082 : Nat := 726774356605978443740753

theorem tailTrace_2123082 : CollatzResearch.WordTrace tailWord_2123082 prefixEnd_2123082 726774356605978443740753 := by
  unfold tailWord_2123082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19358790523610995595790875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51623441396295988255442333 19358790523610995595790875)
  ·
    refine ⟨29038185785416493393686313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19358790523610995595790875 29038185785416493393686313)
    ·
      refine ⟨21778639339062370045264735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29038185785416493393686313 21778639339062370045264735)
      ·
        refine ⟨32667959008593555067897103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21778639339062370045264735 32667959008593555067897103)
        ·
          refine ⟨49001938512890332601845655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32667959008593555067897103 49001938512890332601845655)
          ·
            refine ⟨73502907769335498902768483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49001938512890332601845655 73502907769335498902768483)
            ·
              refine ⟨110254361654003248354152725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73502907769335498902768483 110254361654003248354152725)
              ·
                refine ⟨5168173202531402266600909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110254361654003248354152725 5168173202531402266600909)
                ·
                  refine ⟨1938064950949275849975341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5168173202531402266600909 1938064950949275849975341)
                  ·
                    refine ⟨726774356605978443740753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938064950949275849975341 726774356605978443740753)
                    ·
                      rfl

theorem cell22_2123082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_2123082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123082 prefixEnd_2123082 := by exact prefixLift 2123082
  have htrace : WordTrace (prefixWord ++ tailWord_2123082) baseStart_2123082 baseEnd_2123082 := by
    simpa [prefixWord, tailWord_2123082, baseEnd_2123082] using wordTrace_append hprefix tailTrace_2123082
  have hstable : (prefixWord ++ tailWord_2123082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123082).length < 2 ^ (prefixWord ++ tailWord_2123082).sum := by decide
  have hdescent : baseEnd_2123082 < baseStart_2123082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123101 : List Nat := [1, 4, 5, 1, 2, 9]
def baseStart_2123101 : Nat := 118140960795 + 2123101 * 2 ^ 59
def prefixEnd_2123101 : Nat := 4983230072969 + 3 ^ 40 * 2123101 * 2
def baseEnd_2123101 : Nat := 8972603218447762068095

theorem tailTrace_2123101 : CollatzResearch.WordTrace tailWord_2123101 prefixEnd_2123101 8972603218447762068095 := by
  unfold tailWord_2123101
  simp only [CollatzResearch.WordTrace]
  refine ⟨77435855081375148628105157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51623903387583432418736771 77435855081375148628105157)
  ·
    refine ⟨14519222827757840367769717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77435855081375148628105157 14519222827757840367769717)
    ·
      refine ⟨1361177140102297534478411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14519222827757840367769717 1361177140102297534478411)
      ·
        refine ⟨2041765710153446301717617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361177140102297534478411 2041765710153446301717617)
        ·
          refine ⟨1531324282615084726288213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2041765710153446301717617 1531324282615084726288213)
          ·
            refine ⟨8972603218447762068095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1531324282615084726288213 8972603218447762068095)
            ·
              rfl

theorem cell22_2123101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 9].length) (baseStart_2123101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123101 prefixEnd_2123101 := by exact prefixLift 2123101
  have htrace : WordTrace (prefixWord ++ tailWord_2123101) baseStart_2123101 baseEnd_2123101 := by
    simpa [prefixWord, tailWord_2123101, baseEnd_2123101] using wordTrace_append hprefix tailTrace_2123101
  have hstable : (prefixWord ++ tailWord_2123101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123101).length < 2 ^ (prefixWord ++ tailWord_2123101).sum := by decide
  have hdescent : baseEnd_2123101 < baseStart_2123101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123116 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_2123116 : Nat := 118140960795 + 2123116 * 2 ^ 59
def prefixEnd_2123116 : Nat := 4983230072969 + 3 ^ 40 * 2123116 * 2
def baseEnd_2123116 : Nat := 726785995500813688390649

theorem tailTrace_2123116 : CollatzResearch.WordTrace tailWord_2123116 prefixEnd_2123116 726785995500813688390649 := by
  unfold tailWord_2123116
  simp only [CollatzResearch.WordTrace]
  refine ⟨38718201088160403094950601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51624268117547204126600801 38718201088160403094950601)
  ·
    refine ⟨29038650816120302321212951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38718201088160403094950601 29038650816120302321212951)
    ·
      refine ⟨43557976224180453481819427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29038650816120302321212951 43557976224180453481819427)
      ·
        refine ⟨65336964336270680222729141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43557976224180453481819427 65336964336270680222729141)
        ·
          refine ⟨6125340406525376270880857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65336964336270680222729141 6125340406525376270880857)
          ·
            refine ⟨4594005304894032203160643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6125340406525376270880857 4594005304894032203160643)
            ·
              refine ⟨6891007957341048304740965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594005304894032203160643 6891007957341048304740965)
              ·
                refine ⟨1292063992001446557138931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6891007957341048304740965 1292063992001446557138931)
                ·
                  refine ⟨1938095988002169835708397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292063992001446557138931 1938095988002169835708397)
                  ·
                    refine ⟨726785995500813688390649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938095988002169835708397 726785995500813688390649)
                    ·
                      rfl

theorem cell22_2123116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_2123116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123116 prefixEnd_2123116 := by exact prefixLift 2123116
  have htrace : WordTrace (prefixWord ++ tailWord_2123116) baseStart_2123116 baseEnd_2123116 := by
    simpa [prefixWord, tailWord_2123116, baseEnd_2123116] using wordTrace_append hprefix tailTrace_2123116
  have hstable : (prefixWord ++ tailWord_2123116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123116).length < 2 ^ (prefixWord ++ tailWord_2123116).sum := by decide
  have hdescent : baseEnd_2123116 < baseStart_2123116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123189 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2123189 : Nat := 118140960795 + 2123189 * 2 ^ 59
def prefixEnd_2123189 : Nat := 4983230072969 + 3 ^ 40 * 2123189 * 2
def baseEnd_2123189 : Nat := 726810984892665831315425

theorem tailTrace_2123189 : CollatzResearch.WordTrace tailWord_2123189 prefixEnd_2123189 726810984892665831315425 := by
  unfold tailWord_2123189
  simp only [CollatzResearch.WordTrace]
  refine ⟨77439064705056339657308621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51626043136704226438205747 77439064705056339657308621)
  ·
    refine ⟨29039649264396127371490733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77439064705056339657308621 29039649264396127371490733)
    ·
      refine ⟨10889868474148547764309025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29039649264396127371490733 10889868474148547764309025)
      ·
        refine ⟨8167401355611410823231769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10889868474148547764309025 8167401355611410823231769)
        ·
          refine ⟨6125551016708558117423827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8167401355611410823231769 6125551016708558117423827)
          ·
            refine ⟨9188326525062837176135741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6125551016708558117423827 9188326525062837176135741)
            ·
              refine ⟨3445622446898563941050903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9188326525062837176135741 3445622446898563941050903)
              ·
                refine ⟨5168433670347845911576355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445622446898563941050903 5168433670347845911576355)
                ·
                  refine ⟨7752650505521768867364533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5168433670347845911576355 7752650505521768867364533)
                  ·
                    refine ⟨726810984892665831315425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7752650505521768867364533 726810984892665831315425)
                    ·
                      rfl

theorem cell22_2123189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2123189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123189 prefixEnd_2123189 := by exact prefixLift 2123189
  have htrace : WordTrace (prefixWord ++ tailWord_2123189) baseStart_2123189 baseEnd_2123189 := by
    simpa [prefixWord, tailWord_2123189, baseEnd_2123189] using wordTrace_append hprefix tailTrace_2123189
  have hstable : (prefixWord ++ tailWord_2123189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123189).length < 2 ^ (prefixWord ++ tailWord_2123189).sum := by decide
  have hdescent : baseEnd_2123189 < baseStart_2123189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123204 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2123204 : Nat := 118140960795 + 2123204 * 2 ^ 59
def prefixEnd_2123204 : Nat := 4983230072969 + 3 ^ 40 * 2123204 * 2
def baseEnd_2123204 : Nat := 726816119699210792190379

theorem tailTrace_2123204 : CollatzResearch.WordTrace tailWord_2123204 prefixEnd_2123204 726816119699210792190379 := by
  unfold tailWord_2123204
  simp only [CollatzResearch.WordTrace]
  refine ⟨38719805900000998609552333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51626407866667998146069777 38719805900000998609552333)
  ·
    refine ⟨14519927212500374478582125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38719805900000998609552333 14519927212500374478582125)
    ·
      refine ⟨5444972704687640429468297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14519927212500374478582125 5444972704687640429468297)
      ·
        refine ⟨4083729528515730322101223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5444972704687640429468297 4083729528515730322101223)
        ·
          refine ⟨6125594292773595483151835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083729528515730322101223 6125594292773595483151835)
          ·
            refine ⟨9188391439160393224727753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6125594292773595483151835 9188391439160393224727753)
            ·
              refine ⟨6891293579370294918545815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9188391439160393224727753 6891293579370294918545815)
              ·
                refine ⟨10336940369055442377818723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891293579370294918545815 10336940369055442377818723)
                ·
                  refine ⟨15505410553583163566728085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10336940369055442377818723 15505410553583163566728085)
                  ·
                    refine ⟨726816119699210792190379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15505410553583163566728085 726816119699210792190379)
                    ·
                      rfl

theorem cell22_2123204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2123204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123204 prefixEnd_2123204 := by exact prefixLift 2123204
  have htrace : WordTrace (prefixWord ++ tailWord_2123204) baseStart_2123204 baseEnd_2123204 := by
    simpa [prefixWord, tailWord_2123204, baseEnd_2123204] using wordTrace_append hprefix tailTrace_2123204
  have hstable : (prefixWord ++ tailWord_2123204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123204).length < 2 ^ (prefixWord ++ tailWord_2123204).sum := by decide
  have hdescent : baseEnd_2123204 < baseStart_2123204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123285 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_2123285 : Nat := 118140960795 + 2123285 * 2 ^ 59
def prefixEnd_2123285 : Nat := 4983230072969 + 3 ^ 40 * 2123285 * 2
def baseEnd_2123285 : Nat := 726843847654553580915131

theorem tailTrace_2123285 : CollatzResearch.WordTrace tailWord_2123285 prefixEnd_2123285 726843847654553580915131 := by
  unfold tailWord_2123285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77442566112708548052803309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51628377408472365368535539 77442566112708548052803309)
  ·
    refine ⟨29040962292265705519801241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77442566112708548052803309 29040962292265705519801241)
    ·
      refine ⟨21780721719199279139850931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29040962292265705519801241 21780721719199279139850931)
      ·
        refine ⟨32671082578798918709776397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21780721719199279139850931 32671082578798918709776397)
        ·
          refine ⟨12251655967049594516166149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32671082578798918709776397 12251655967049594516166149)
          ·
            refine ⟨2297185493821798971781153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12251655967049594516166149 2297185493821798971781153)
            ·
              refine ⟨1722889120366349228835865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297185493821798971781153 1722889120366349228835865)
              ·
                refine ⟨1292166840274761921626899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722889120366349228835865 1292166840274761921626899)
                ·
                  refine ⟨1938250260412142882440349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292166840274761921626899 1938250260412142882440349)
                  ·
                    refine ⟨726843847654553580915131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938250260412142882440349 726843847654553580915131)
                    ·
                      rfl

theorem cell22_2123285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_2123285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123285 prefixEnd_2123285 := by exact prefixLift 2123285
  have htrace : WordTrace (prefixWord ++ tailWord_2123285) baseStart_2123285 baseEnd_2123285 := by
    simpa [prefixWord, tailWord_2123285, baseEnd_2123285] using wordTrace_append hprefix tailTrace_2123285
  have hstable : (prefixWord ++ tailWord_2123285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123285).length < 2 ^ (prefixWord ++ tailWord_2123285).sum := by decide
  have hdescent : baseEnd_2123285 < baseStart_2123285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123399 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 7]
def baseStart_2123399 : Nat := 118140960795 + 2123399 * 2 ^ 59
def prefixEnd_2123399 : Nat := 4983230072969 + 3 ^ 40 * 2123399 * 2
def baseEnd_2123399 : Nat := 242294290728098427854927

theorem tailTrace_2123399 : CollatzResearch.WordTrace tailWord_2123399 prefixEnd_2123399 242294290728098427854927 := by
  unfold tailWord_2123399
  simp only [CollatzResearch.WordTrace]
  refine ⟨77446724034295545522453251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51631149356197030348302167 77446724034295545522453251)
  ·
    refine ⟨116170086051443318283679877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77446724034295545522453251 116170086051443318283679877)
    ·
      refine ⟨21781891134645622178189977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116170086051443318283679877 21781891134645622178189977)
      ·
        refine ⟨16336418350984216633642483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21781891134645622178189977 16336418350984216633642483)
        ·
          refine ⟨24504627526476324950463725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16336418350984216633642483 24504627526476324950463725)
          ·
            refine ⟨9189235322428621856423897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24504627526476324950463725 9189235322428621856423897)
            ·
              refine ⟨6891926491821466392317923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9189235322428621856423897 6891926491821466392317923)
              ·
                refine ⟨10337889737732199588476885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891926491821466392317923 10337889737732199588476885)
                ·
                  refine ⟨242294290728098427854927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10337889737732199588476885 242294290728098427854927)
                  ·
                    rfl

theorem cell22_2123399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 7].length) (baseStart_2123399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123399 prefixEnd_2123399 := by exact prefixLift 2123399
  have htrace : WordTrace (prefixWord ++ tailWord_2123399) baseStart_2123399 baseEnd_2123399 := by
    simpa [prefixWord, tailWord_2123399, baseEnd_2123399] using wordTrace_append hprefix tailTrace_2123399
  have hstable : (prefixWord ++ tailWord_2123399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123399).length < 2 ^ (prefixWord ++ tailWord_2123399).sum := by decide
  have hdescent : baseEnd_2123399 < baseStart_2123399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123416 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_2123416 : Nat := 118140960795 + 2123416 * 2 ^ 59
def prefixEnd_2123416 : Nat := 4983230072969 + 3 ^ 40 * 2123416 * 2
def baseEnd_2123416 : Nat := 242296230543904301963243

theorem tailTrace_2123416 : CollatzResearch.WordTrace tailWord_2123416 prefixEnd_2123416 242296230543904301963243 := by
  unfold tailWord_2123416
  simp only [CollatzResearch.WordTrace]
  refine ⟨38723672037616978712911051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51631562716822638283881401 38723672037616978712911051)
  ·
    refine ⟨58085508056425468069366577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38723672037616978712911051 58085508056425468069366577)
    ·
      refine ⟨43564131042319101052024933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58085508056425468069366577 43564131042319101052024933)
      ·
        refine ⟨8168274570434831447254675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43564131042319101052024933 8168274570434831447254675)
        ·
          refine ⟨12252411855652247170882013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168274570434831447254675 12252411855652247170882013)
          ·
            refine ⟨4594654445869592689080755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12252411855652247170882013 4594654445869592689080755)
            ·
              refine ⟨6891981668804389033621133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594654445869592689080755 6891981668804389033621133)
              ·
                refine ⟨2584493125801645887607925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6891981668804389033621133 2584493125801645887607925)
                ·
                  refine ⟨242296230543904301963243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2584493125801645887607925 242296230543904301963243)
                  ·
                    rfl

theorem cell22_2123416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_2123416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123416 prefixEnd_2123416 := by exact prefixLift 2123416
  have htrace : WordTrace (prefixWord ++ tailWord_2123416) baseStart_2123416 baseEnd_2123416 := by
    simpa [prefixWord, tailWord_2123416, baseEnd_2123416] using wordTrace_append hprefix tailTrace_2123416
  have hstable : (prefixWord ++ tailWord_2123416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123416).length < 2 ^ (prefixWord ++ tailWord_2123416).sum := by decide
  have hdescent : baseEnd_2123416 < baseStart_2123416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123461 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 4]
def baseStart_2123461 : Nat := 118140960795 + 2123461 * 2 ^ 59
def prefixEnd_2123461 : Nat := 4983230072969 + 3 ^ 40 * 2123461 * 2
def baseEnd_2123461 : Nat := 242301365350449262838197

theorem tailTrace_2123461 : CollatzResearch.WordTrace tailWord_2123461 prefixEnd_2123461 242301365350449262838197 := by
  unfold tailWord_2123461
  simp only [CollatzResearch.WordTrace]
  refine ⟨77448985360070930111210237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51632656906713953407473491 77448985360070930111210237)
  ·
    refine ⟨29043369510026598791703839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77448985360070930111210237 29043369510026598791703839)
    ·
      refine ⟨43565054265039898187555759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29043369510026598791703839 43565054265039898187555759)
      ·
        refine ⟨65347581397559847281333639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43565054265039898187555759 65347581397559847281333639)
        ·
          refine ⟨98021372096339770922000459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65347581397559847281333639 98021372096339770922000459)
          ·
            refine ⟨147032058144509656383000689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98021372096339770922000459 147032058144509656383000689)
            ·
              refine ⟨110274043608382242287250517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147032058144509656383000689 110274043608382242287250517)
              ·
                refine ⟨1292273948535729401803717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 110274043608382242287250517 1292273948535729401803717)
                ·
                  refine ⟨242301365350449262838197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292273948535729401803717 242301365350449262838197)
                  ·
                    rfl

theorem cell22_2123461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_2123461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123461 prefixEnd_2123461 := by exact prefixLift 2123461
  have htrace : WordTrace (prefixWord ++ tailWord_2123461) baseStart_2123461 baseEnd_2123461 := by
    simpa [prefixWord, tailWord_2123461, baseEnd_2123461] using wordTrace_append hprefix tailTrace_2123461
  have hstable : (prefixWord ++ tailWord_2123461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123461).length < 2 ^ (prefixWord ++ tailWord_2123461).sum := by decide
  have hdescent : baseEnd_2123461 < baseStart_2123461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123510 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_2123510 : Nat := 118140960795 + 2123510 * 2 ^ 59
def prefixEnd_2123510 : Nat := 4983230072969 + 3 ^ 40 * 2123510 * 2
def baseEnd_2123510 : Nat := 726920869752727994039441

theorem tailTrace_2123510 : CollatzResearch.WordTrace tailWord_2123510 prefixEnd_2123510 726920869752727994039441 := by
  unfold tailWord_2123510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840673283555838217483999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51633848357928940986495989 4840673283555838217483999)
  ·
    refine ⟨7261009925333757326225999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4840673283555838217483999 7261009925333757326225999)
    ·
      refine ⟨10891514888000635989338999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7261009925333757326225999 10891514888000635989338999)
      ·
        refine ⟨16337272332000953984008499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10891514888000635989338999 16337272332000953984008499)
        ·
          refine ⟨24505908498001430976012749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16337272332000953984008499 24505908498001430976012749)
          ·
            refine ⟨9189715686750536616004781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24505908498001430976012749 9189715686750536616004781)
            ·
              refine ⟨3446143382531451231001793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9189715686750536616004781 3446143382531451231001793)
              ·
                refine ⟨2584607536898588423251345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3446143382531451231001793 2584607536898588423251345)
                ·
                  refine ⟨1938455652673941317438509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2584607536898588423251345 1938455652673941317438509)
                  ·
                    refine ⟨726920869752727994039441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938455652673941317438509 726920869752727994039441)
                    ·
                      rfl

theorem cell22_2123510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_2123510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123510 prefixEnd_2123510 := by exact prefixLift 2123510
  have htrace : WordTrace (prefixWord ++ tailWord_2123510) baseStart_2123510 baseEnd_2123510 := by
    simpa [prefixWord, tailWord_2123510, baseEnd_2123510] using wordTrace_append hprefix tailTrace_2123510
  have hstable : (prefixWord ++ tailWord_2123510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123510).length < 2 ^ (prefixWord ++ tailWord_2123510).sum := by decide
  have hdescent : baseEnd_2123510 < baseStart_2123510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123519 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_2123519 : Nat := 118140960795 + 2123519 * 2 ^ 59
def prefixEnd_2123519 : Nat := 4983230072969 + 3 ^ 40 * 2123519 * 2
def baseEnd_2123519 : Nat := 726923950636654970564413

theorem tailTrace_2123519 : CollatzResearch.WordTrace tailWord_2123519 prefixEnd_2123519 726923950636654970564413 := by
  unfold tailWord_2123519
  simp only [CollatzResearch.WordTrace]
  refine ⟨77451100793860806016821611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51634067195907204011214407 77451100793860806016821611)
  ·
    refine ⟨116176651190791209025232417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77451100793860806016821611 116176651190791209025232417)
    ·
      refine ⟨87132488393093406768924313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116176651190791209025232417 87132488393093406768924313)
      ·
        refine ⟨65349366294820055076693235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87132488393093406768924313 65349366294820055076693235)
        ·
          refine ⟨98024049442230082615039853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65349366294820055076693235 98024049442230082615039853)
          ·
            refine ⟨36759018540836280980639945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98024049442230082615039853 36759018540836280980639945)
            ·
              refine ⟨27569263905627210735479959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36759018540836280980639945 27569263905627210735479959)
              ·
                refine ⟨41353895858440816103219939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27569263905627210735479959 41353895858440816103219939)
                ·
                  refine ⟨62030843787661224154829909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41353895858440816103219939 62030843787661224154829909)
                  ·
                    refine ⟨726923950636654970564413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62030843787661224154829909 726923950636654970564413)
                    ·
                      rfl

theorem cell22_2123519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_2123519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123519 prefixEnd_2123519 := by exact prefixLift 2123519
  have htrace : WordTrace (prefixWord ++ tailWord_2123519) baseStart_2123519 baseEnd_2123519 := by
    simpa [prefixWord, tailWord_2123519, baseEnd_2123519] using wordTrace_append hprefix tailTrace_2123519
  have hstable : (prefixWord ++ tailWord_2123519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123519).length < 2 ^ (prefixWord ++ tailWord_2123519).sum := by decide
  have hdescent : baseEnd_2123519 < baseStart_2123519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123527 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2123527 : Nat := 118140960795 + 2123527 * 2 ^ 59
def prefixEnd_2123527 : Nat := 4983230072969 + 3 ^ 40 * 2123527 * 2
def baseEnd_2123527 : Nat := 726926689200145616364389

theorem tailTrace_2123527 : CollatzResearch.WordTrace tailWord_2123527 prefixEnd_2123527 726926689200145616364389 := by
  unfold tailWord_2123527
  simp only [CollatzResearch.WordTrace]
  refine ⟨77451392577831823383112835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51634261718554548922075223 77451392577831823383112835)
  ·
    refine ⟨116177088866747735074669253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77451392577831823383112835 116177088866747735074669253)
    ·
      refine ⟨21783204162515200326500485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116177088866747735074669253 21783204162515200326500485)
      ·
        refine ⟨4084350780471600061218841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21783204162515200326500485 4084350780471600061218841)
        ·
          refine ⟨3063263085353700045914131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4084350780471600061218841 3063263085353700045914131)
          ·
            refine ⟨4594894628030550068871197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063263085353700045914131 4594894628030550068871197)
            ·
              refine ⟨1723085485511456275826699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4594894628030550068871197 1723085485511456275826699)
              ·
                refine ⟨2584628228267184413740049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723085485511456275826699 2584628228267184413740049)
                ·
                  refine ⟨1938471171200388310305037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2584628228267184413740049 1938471171200388310305037)
                  ·
                    refine ⟨726926689200145616364389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938471171200388310305037 726926689200145616364389)
                    ·
                      rfl

theorem cell22_2123527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2123527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123527 prefixEnd_2123527 := by exact prefixLift 2123527
  have htrace : WordTrace (prefixWord ++ tailWord_2123527) baseStart_2123527 baseEnd_2123527 := by
    simpa [prefixWord, tailWord_2123527, baseEnd_2123527] using wordTrace_append hprefix tailTrace_2123527
  have hstable : (prefixWord ++ tailWord_2123527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123527).length < 2 ^ (prefixWord ++ tailWord_2123527).sum := by decide
  have hdescent : baseEnd_2123527 < baseStart_2123527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123555 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 1, 3]
def baseStart_2123555 : Nat := 118140960795 + 2123555 * 2 ^ 59
def prefixEnd_2123555 : Nat := 4983230072969 + 3 ^ 40 * 2123555 * 2
def baseEnd_2123555 : Nat := 726936274172362876664303

theorem tailTrace_2123555 : CollatzResearch.WordTrace tailWord_2123555 prefixEnd_2123555 726936274172362876664303 := by
  unfold tailWord_2123555
  simp only [CollatzResearch.WordTrace]
  refine ⟨77452413821730384165132119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51634942547820256110088079 77452413821730384165132119)
  ·
    refine ⟨116178620732595576247698179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77452413821730384165132119 116178620732595576247698179)
    ·
      refine ⟨174267931098893364371547269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116178620732595576247698179 174267931098893364371547269)
      ·
        refine ⟨32675237081042505819665113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174267931098893364371547269 32675237081042505819665113)
        ·
          refine ⟨24506427810781879364748835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32675237081042505819665113 24506427810781879364748835)
          ·
            refine ⟨36759641716172819047123253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24506427810781879364748835 36759641716172819047123253)
            ·
              refine ⟨3446216410891201785667805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36759641716172819047123253 3446216410891201785667805)
              ·
                refine ⟨1292331154084200669625427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3446216410891201785667805 1292331154084200669625427)
                ·
                  refine ⟨1938496731126301004438141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292331154084200669625427 1938496731126301004438141)
                  ·
                    refine ⟨726936274172362876664303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938496731126301004438141 726936274172362876664303)
                    ·
                      rfl

theorem cell22_2123555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 3].length) (baseStart_2123555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123555 prefixEnd_2123555 := by exact prefixLift 2123555
  have htrace : WordTrace (prefixWord ++ tailWord_2123555) baseStart_2123555 baseEnd_2123555 := by
    simpa [prefixWord, tailWord_2123555, baseEnd_2123555] using wordTrace_append hprefix tailTrace_2123555
  have hstable : (prefixWord ++ tailWord_2123555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123555).length < 2 ^ (prefixWord ++ tailWord_2123555).sum := by decide
  have hdescent : baseEnd_2123555 < baseStart_2123555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123572 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2123572 : Nat := 118140960795 + 2123572 * 2 ^ 59
def prefixEnd_2123572 : Nat := 4983230072969 + 3 ^ 40 * 2123572 * 2
def baseEnd_2123572 : Nat := 726942093619780498989251

theorem tailTrace_2123572 : CollatzResearch.WordTrace tailWord_2123572 prefixEnd_2123572 726942093619780498989251 := by
  unfold tailWord_2123572
  simp only [CollatzResearch.WordTrace]
  refine ⟨38726516931334398034250485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51635355908445864045667313 38726516931334398034250485)
  ·
    refine ⟨3630610962312599815710983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38726516931334398034250485 3630610962312599815710983)
    ·
      refine ⟨5445916443468899723566475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630610962312599815710983 5445916443468899723566475)
      ·
        refine ⟨8168874665203349585349713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5445916443468899723566475 8168874665203349585349713)
        ·
          refine ⟨6126655998902512189012285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8168874665203349585349713 6126655998902512189012285)
          ·
            refine ⟨2297495999588442070879607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6126655998902512189012285 2297495999588442070879607)
            ·
              refine ⟨3446243999382663106319411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297495999588442070879607 3446243999382663106319411)
              ·
                refine ⟨5169365999073994659479117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446243999382663106319411 5169365999073994659479117)
                ·
                  refine ⟨1938512249652747997304669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5169365999073994659479117 1938512249652747997304669)
                  ·
                    refine ⟨726942093619780498989251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938512249652747997304669 726942093619780498989251)
                    ·
                      rfl

theorem cell22_2123572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2123572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123572 prefixEnd_2123572 := by exact prefixLift 2123572
  have htrace : WordTrace (prefixWord ++ tailWord_2123572) baseStart_2123572 baseEnd_2123572 := by
    simpa [prefixWord, tailWord_2123572, baseEnd_2123572] using wordTrace_append hprefix tailTrace_2123572
  have hstable : (prefixWord ++ tailWord_2123572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123572).length < 2 ^ (prefixWord ++ tailWord_2123572).sum := by decide
  have hdescent : baseEnd_2123572 < baseStart_2123572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123615 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 1, 4]
def baseStart_2123615 : Nat := 118140960795 + 2123615 * 2 ^ 59
def prefixEnd_2123615 : Nat := 4983230072969 + 3 ^ 40 * 2123615 * 2
def baseEnd_2123615 : Nat := 726956813398542720164119

theorem tailTrace_2123615 : CollatzResearch.WordTrace tailWord_2123615 prefixEnd_2123615 726956813398542720164119 := by
  unfold tailWord_2123615
  simp only [CollatzResearch.WordTrace]
  refine ⟨77454602201513014412316299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51636401467675342941544199 77454602201513014412316299)
  ·
    refine ⟨116181903302269521618474449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77454602201513014412316299 116181903302269521618474449)
    ·
      refine ⟨87136427476702141213855837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116181903302269521618474449 87136427476702141213855837)
      ·
        refine ⟨32676160303763302955195939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87136427476702141213855837 32676160303763302955195939)
        ·
          refine ⟨49014240455644954432793909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32676160303763302955195939 49014240455644954432793909)
          ·
            refine ⟨4595085042716714478074429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49014240455644954432793909 4595085042716714478074429)
            ·
              refine ⟨1723156891018767929277911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4595085042716714478074429 1723156891018767929277911)
              ·
                refine ⟨2584735336528151893916867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723156891018767929277911 2584735336528151893916867)
                ·
                  refine ⟨3877103004792227840875301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584735336528151893916867 3877103004792227840875301)
                  ·
                    refine ⟨726956813398542720164119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3877103004792227840875301 726956813398542720164119)
                    ·
                      rfl

theorem cell22_2123615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_2123615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123615 prefixEnd_2123615 := by exact prefixLift 2123615
  have htrace : WordTrace (prefixWord ++ tailWord_2123615) baseStart_2123615 baseEnd_2123615 := by
    simpa [prefixWord, tailWord_2123615, baseEnd_2123615] using wordTrace_append hprefix tailTrace_2123615
  have hstable : (prefixWord ++ tailWord_2123615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123615).length < 2 ^ (prefixWord ++ tailWord_2123615).sum := by decide
  have hdescent : baseEnd_2123615 < baseStart_2123615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123679 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 2, 3]
def baseStart_2123679 : Nat := 118140960795 + 2123679 * 2 ^ 59
def prefixEnd_2123679 : Nat := 4983230072969 + 3 ^ 40 * 2123679 * 2
def baseEnd_2123679 : Nat := 726978721906467886563923

theorem tailTrace_2123679 : CollatzResearch.WordTrace tailWord_2123679 prefixEnd_2123679 726978721906467886563923 := by
  unfold tailWord_2123679
  simp only [CollatzResearch.WordTrace]
  refine ⟨77456936473281153342646091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51637957648854102228430727 77456936473281153342646091)
  ·
    refine ⟨116185404709921730013969137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77456936473281153342646091 116185404709921730013969137)
    ·
      refine ⟨87139053532441297510476853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116185404709921730013969137 87139053532441297510476853)
      ·
        refine ⟨8169286268666371641607205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87139053532441297510476853 8169286268666371641607205)
        ·
          refine ⟨1531741175374944682801351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8169286268666371641607205 1531741175374944682801351)
          ·
            refine ⟨2297611763062417024202027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531741175374944682801351 2297611763062417024202027)
            ·
              refine ⟨3446417644593625536303041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297611763062417024202027 3446417644593625536303041)
              ·
                refine ⟨2584813233445219152227281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3446417644593625536303041 2584813233445219152227281)
                ·
                  refine ⟨1938609925083914364170461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2584813233445219152227281 1938609925083914364170461)
                  ·
                    refine ⟨726978721906467886563923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938609925083914364170461 726978721906467886563923)
                    ·
                      rfl

theorem cell22_2123679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_2123679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123679 prefixEnd_2123679 := by exact prefixLift 2123679
  have htrace : WordTrace (prefixWord ++ tailWord_2123679) baseStart_2123679 baseEnd_2123679 := by
    simpa [prefixWord, tailWord_2123679, baseEnd_2123679] using wordTrace_append hprefix tailTrace_2123679
  have hstable : (prefixWord ++ tailWord_2123679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123679).length < 2 ^ (prefixWord ++ tailWord_2123679).sum := by decide
  have hdescent : baseEnd_2123679 < baseStart_2123679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123724 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_2123724 : Nat := 118140960795 + 2123724 * 2 ^ 59
def prefixEnd_2123724 : Nat := 4983230072969 + 3 ^ 40 * 2123724 * 2
def baseEnd_2123724 : Nat := 726994126326102769188785

theorem tailTrace_2123724 : CollatzResearch.WordTrace tailWord_2123724 prefixEnd_2123724 726994126326102769188785 := by
  unfold tailWord_2123724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38729288879059063014017113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51639051838745417352022817 38729288879059063014017113)
  ·
    refine ⟨29046966659294297260512835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38729288879059063014017113 29046966659294297260512835)
    ·
      refine ⟨43570449988941445890769253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29046966659294297260512835 43570449988941445890769253)
      ·
        refine ⟨8169459372926521104519235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43570449988941445890769253 8169459372926521104519235)
        ·
          refine ⟨12254189059389781656778853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169459372926521104519235 12254189059389781656778853)
          ·
            refine ⟨2297660448635584060646035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12254189059389781656778853 2297660448635584060646035)
            ·
              refine ⟨3446490672953376090969053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297660448635584060646035 3446490672953376090969053)
              ·
                refine ⟨1292434002357516034113395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3446490672953376090969053 1292434002357516034113395)
                ·
                  refine ⟨1938651003536274051170093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292434002357516034113395 1938651003536274051170093)
                  ·
                    refine ⟨726994126326102769188785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938651003536274051170093 726994126326102769188785)
                    ·
                      rfl

theorem cell22_2123724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_2123724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123724 prefixEnd_2123724 := by exact prefixLift 2123724
  have htrace : WordTrace (prefixWord ++ tailWord_2123724) baseStart_2123724 baseEnd_2123724 := by
    simpa [prefixWord, tailWord_2123724, baseEnd_2123724] using wordTrace_append hprefix tailTrace_2123724
  have hstable : (prefixWord ++ tailWord_2123724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123724).length < 2 ^ (prefixWord ++ tailWord_2123724).sum := by decide
  have hdescent : baseEnd_2123724 < baseStart_2123724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123741 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2123741 : Nat := 118140960795 + 2123741 * 2 ^ 59
def prefixEnd_2123741 : Nat := 4983230072969 + 3 ^ 40 * 2123741 * 2
def baseEnd_2123741 : Nat := 726999945773520391513733

theorem tailTrace_2123741 : CollatzResearch.WordTrace tailWord_2123741 prefixEnd_2123741 726999945773520391513733 := by
  unfold tailWord_2123741
  simp only [CollatzResearch.WordTrace]
  refine ⟨77459197799056537931403077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51639465199371025287602051 77459197799056537931403077)
  ·
    refine ⟨14523599587323100862138077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77459197799056537931403077 14523599587323100862138077)
    ·
      refine ⟨5446349845246162823301779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14523599587323100862138077 5446349845246162823301779)
      ·
        refine ⟨8169524767869244234952669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446349845246162823301779 8169524767869244234952669)
        ·
          refine ⟨3063571787950966588107251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8169524767869244234952669 3063571787950966588107251)
          ·
            refine ⟨4595357681926449882160877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063571787950966588107251 4595357681926449882160877)
            ·
              refine ⟨1723259130722418705810329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4595357681926449882160877 1723259130722418705810329)
              ·
                refine ⟨1292444348041814029357747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723259130722418705810329 1292444348041814029357747)
                ·
                  refine ⟨1938666522062721044036621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292444348041814029357747 1938666522062721044036621)
                  ·
                    refine ⟨726999945773520391513733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938666522062721044036621 726999945773520391513733)
                    ·
                      rfl

theorem cell22_2123741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2123741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123741 prefixEnd_2123741 := by exact prefixLift 2123741
  have htrace : WordTrace (prefixWord ++ tailWord_2123741) baseStart_2123741 baseEnd_2123741 := by
    simpa [prefixWord, tailWord_2123741, baseEnd_2123741] using wordTrace_append hprefix tailTrace_2123741
  have hstable : (prefixWord ++ tailWord_2123741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123741).length < 2 ^ (prefixWord ++ tailWord_2123741).sum := by decide
  have hdescent : baseEnd_2123741 < baseStart_2123741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123825 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_2123825 : Nat := 118140960795 + 2123825 * 2 ^ 59
def prefixEnd_2123825 : Nat := 4983230072969 + 3 ^ 40 * 2123825 * 2
def baseEnd_2123825 : Nat := 727028700690172172413475

theorem tailTrace_2123825 : CollatzResearch.WordTrace tailWord_2123825 prefixEnd_2123825 727028700690172172413475 := by
  unfold tailWord_2123825
  simp only [CollatzResearch.WordTrace]
  refine ⟨77462261530752220277460929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51641507687168146851640619 77462261530752220277460929)
  ·
    refine ⟨58096696148064165208095697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77462261530752220277460929 58096696148064165208095697)
    ·
      refine ⟨43572522111048123906071773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58096696148064165208095697 43572522111048123906071773)
      ·
        refine ⟨16339695791643046464776915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43572522111048123906071773 16339695791643046464776915)
        ·
          refine ⟨24509543687464569697165373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16339695791643046464776915 24509543687464569697165373)
          ·
            refine ⟨9191078882799213636437015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24509543687464569697165373 9191078882799213636437015)
            ·
              refine ⟨13786618324198820454655523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191078882799213636437015 13786618324198820454655523)
              ·
                refine ⟨20679927486298230681983285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13786618324198820454655523 20679927486298230681983285)
                ·
                  refine ⟨1938743201840459126435933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20679927486298230681983285 1938743201840459126435933)
                  ·
                    refine ⟨727028700690172172413475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938743201840459126435933 727028700690172172413475)
                    ·
                      rfl

theorem cell22_2123825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_2123825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123825 prefixEnd_2123825 := by exact prefixLift 2123825
  have htrace : WordTrace (prefixWord ++ tailWord_2123825) baseStart_2123825 baseEnd_2123825 := by
    simpa [prefixWord, tailWord_2123825, baseEnd_2123825] using wordTrace_append hprefix tailTrace_2123825
  have hstable : (prefixWord ++ tailWord_2123825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123825).length < 2 ^ (prefixWord ++ tailWord_2123825).sum := by decide
  have hdescent : baseEnd_2123825 < baseStart_2123825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123872 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 5]
def baseStart_2123872 : Nat := 118140960795 + 2123872 * 2 ^ 59
def prefixEnd_2123872 : Nat := 4983230072969 + 3 ^ 40 * 2123872 * 2
def baseEnd_2123872 : Nat := 242348263250226572162777

theorem tailTrace_2123872 : CollatzResearch.WordTrace tailWord_2123872 prefixEnd_2123872 242348263250226572162777 := by
  unfold tailWord_2123872
  simp only [CollatzResearch.WordTrace]
  refine ⟨38731987880790973652210935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51642650507721298202947913 38731987880790973652210935)
  ·
    refine ⟨58097981821186460478316403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38731987880790973652210935 58097981821186460478316403)
    ·
      refine ⟨87146972731779690717474605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58097981821186460478316403 87146972731779690717474605)
      ·
        refine ⟨32680114774417384019052977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87146972731779690717474605 32680114774417384019052977)
        ·
          refine ⟨24510086080813038014289733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32680114774417384019052977 24510086080813038014289733)
          ·
            refine ⟨4595641140152444627679325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24510086080813038014289733 4595641140152444627679325)
            ·
              refine ⟨1723365427557166735379747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4595641140152444627679325 1723365427557166735379747)
              ·
                refine ⟨2585048141335750103069621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723365427557166735379747 2585048141335750103069621)
                ·
                  refine ⟨242348263250226572162777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2585048141335750103069621 242348263250226572162777)
                  ·
                    rfl

theorem cell22_2123872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_2123872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123872 prefixEnd_2123872 := by exact prefixLift 2123872
  have htrace : WordTrace (prefixWord ++ tailWord_2123872) baseStart_2123872 baseEnd_2123872 := by
    simpa [prefixWord, tailWord_2123872, baseEnd_2123872] using wordTrace_append hprefix tailTrace_2123872
  have hstable : (prefixWord ++ tailWord_2123872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123872).length < 2 ^ (prefixWord ++ tailWord_2123872).sum := by decide
  have hdescent : baseEnd_2123872 < baseStart_2123872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123966 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2123966 : Nat := 118140960795 + 2123966 * 2 ^ 59
def prefixEnd_2123966 : Nat := 4983230072969 + 3 ^ 40 * 2123966 * 2
def baseEnd_2123966 : Nat := 727076967871694804638043

theorem tailTrace_2123966 : CollatzResearch.WordTrace tailWord_2123966 prefixEnd_2123966 727076967871694804638043 := by
  unfold tailWord_2123966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9683425527905175169792969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51644936148827600905562501 9683425527905175169792969)
  ·
    refine ⟨7262569145928881377344727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9683425527905175169792969 7262569145928881377344727)
    ·
      refine ⟨10893853718893322066017091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7262569145928881377344727 10893853718893322066017091)
      ·
        refine ⟨16340780578339983099025637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10893853718893322066017091 16340780578339983099025637)
        ·
          refine ⟨3063896358438746831067307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16340780578339983099025637 3063896358438746831067307)
          ·
            refine ⟨4595844537658120246600961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063896358438746831067307 4595844537658120246600961)
            ·
              refine ⟨3446883403243590184950721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4595844537658120246600961 3446883403243590184950721)
              ·
                refine ⟨2585162552432692638713041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3446883403243590184950721 2585162552432692638713041)
                ·
                  refine ⟨1938871914324519479034781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585162552432692638713041 1938871914324519479034781)
                  ·
                    refine ⟨727076967871694804638043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938871914324519479034781 727076967871694804638043)
                    ·
                      rfl

theorem cell22_2123966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2123966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123966 prefixEnd_2123966 := by exact prefixLift 2123966
  have htrace : WordTrace (prefixWord ++ tailWord_2123966) baseStart_2123966 baseEnd_2123966 := by
    simpa [prefixWord, tailWord_2123966, baseEnd_2123966] using wordTrace_append hprefix tailTrace_2123966
  have hstable : (prefixWord ++ tailWord_2123966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123966).length < 2 ^ (prefixWord ++ tailWord_2123966).sum := by decide
  have hdescent : baseEnd_2123966 < baseStart_2123966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123996 : List Nat := [2, 2, 5, 2, 1, 1, 3, 6]
def baseStart_2123996 : Nat := 118140960795 + 2123996 * 2 ^ 59
def prefixEnd_2123996 : Nat := 4983230072969 + 3 ^ 40 * 2123996 * 2
def baseEnd_2123996 : Nat := 80787470831642747376439

theorem tailTrace_2123996 : CollatzResearch.WordTrace tailWord_2123996 prefixEnd_2123996 80787470831642747376439 := by
  unfold tailWord_2123996
  simp only [CollatzResearch.WordTrace]
  refine ⟨38734249206566358240967921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51645665608755144321290561 38734249206566358240967921)
  ·
    refine ⟨29050686904924768680725941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38734249206566358240967921 29050686904924768680725941)
    ·
      refine ⟨2723501897336697063818057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29050686904924768680725941 2723501897336697063818057)
      ·
        refine ⟨2042626423002522797863543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2723501897336697063818057 2042626423002522797863543)
        ·
          refine ⟨3063939634503784196795315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042626423002522797863543 3063939634503784196795315)
          ·
            refine ⟨4595909451755676295192973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063939634503784196795315 4595909451755676295192973)
            ·
              refine ⟨1723466044408378610697365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4595909451755676295192973 1723466044408378610697365)
              ·
                refine ⟨80787470831642747376439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1723466044408378610697365 80787470831642747376439)
                ·
                  rfl

theorem cell22_2123996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 6].length) (baseStart_2123996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2123996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2123996 prefixEnd_2123996 := by exact prefixLift 2123996
  have htrace : WordTrace (prefixWord ++ tailWord_2123996) baseStart_2123996 baseEnd_2123996 := by
    simpa [prefixWord, tailWord_2123996, baseEnd_2123996] using wordTrace_append hprefix tailTrace_2123996
  have hstable : (prefixWord ++ tailWord_2123996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123996).length < 2 ^ (prefixWord ++ tailWord_2123996).sum := by decide
  have hdescent : baseEnd_2123996 < baseStart_2123996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124022 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2124022 : Nat := 118140960795 + 2124022 * 2 ^ 59
def prefixEnd_2124022 : Nat := 4983230072969 + 3 ^ 40 * 2124022 * 2
def baseEnd_2124022 : Nat := 727096137816129325237871

theorem tailTrace_2124022 : CollatzResearch.WordTrace tailWord_2124022 prefixEnd_2124022 727096137816129325237871 := by
  unfold tailWord_2124022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841840419439907682648895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51646297807359015281588213 4841840419439907682648895)
  ·
    refine ⟨7262760629159861523973343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4841840419439907682648895 7262760629159861523973343)
    ·
      refine ⟨10894140943739792285960015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7262760629159861523973343 10894140943739792285960015)
      ·
        refine ⟨16341211415609688428940023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10894140943739792285960015 16341211415609688428940023)
        ·
          refine ⟨24511817123414532643410035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16341211415609688428940023 24511817123414532643410035)
          ·
            refine ⟨36767725685121798965115053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24511817123414532643410035 36767725685121798965115053)
            ·
              refine ⟨13787897131920674611918145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36767725685121798965115053 13787897131920674611918145)
              ·
                refine ⟨10340922848940505958938609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13787897131920674611918145 10340922848940505958938609)
                ·
                  refine ⟨7755692136705379469203957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10340922848940505958938609 7755692136705379469203957)
                  ·
                    refine ⟨727096137816129325237871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7755692136705379469203957 727096137816129325237871)
                    ·
                      rfl

theorem cell22_2124022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2124022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124022 prefixEnd_2124022 := by exact prefixLift 2124022
  have htrace : WordTrace (prefixWord ++ tailWord_2124022) baseStart_2124022 baseEnd_2124022 := by
    simpa [prefixWord, tailWord_2124022, baseEnd_2124022] using wordTrace_append hprefix tailTrace_2124022
  have hstable : (prefixWord ++ tailWord_2124022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124022).length < 2 ^ (prefixWord ++ tailWord_2124022).sum := by decide
  have hdescent : baseEnd_2124022 < baseStart_2124022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124067 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 6, 3]
def baseStart_2124067 : Nat := 118140960795 + 2124067 * 2 ^ 59
def prefixEnd_2124067 : Nat := 4983230072969 + 3 ^ 40 * 2124067 * 2
def baseEnd_2124067 : Nat := 727111542235764207862733

theorem tailTrace_2124067 : CollatzResearch.WordTrace tailWord_2124067 prefixEnd_2124067 727111542235764207862733 := by
  unfold tailWord_2124067
  simp only [CollatzResearch.WordTrace]
  refine ⟨77471087995875495607770455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51647391997250330405180303 77471087995875495607770455)
  ·
    refine ⟨116206631993813243411655683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77471087995875495607770455 116206631993813243411655683)
    ·
      refine ⟨174309947990719865117483525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116206631993813243411655683 174309947990719865117483525)
      ·
        refine ⟨32683115248259974709528161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174309947990719865117483525 32683115248259974709528161)
        ·
          refine ⟨24512336436194981032146121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32683115248259974709528161 24512336436194981032146121)
          ·
            refine ⟨18384252327146235774109591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24512336436194981032146121 18384252327146235774109591)
            ·
              refine ⟨27576378490719353661164387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18384252327146235774109591 27576378490719353661164387)
              ·
                refine ⟨41364567736079030491746581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27576378490719353661164387 41364567736079030491746581)
                ·
                  refine ⟨1938964112628704554300621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41364567736079030491746581 1938964112628704554300621)
                  ·
                    refine ⟨727111542235764207862733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938964112628704554300621 727111542235764207862733)
                    ·
                      rfl

theorem cell22_2124067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 3].length) (baseStart_2124067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124067 prefixEnd_2124067 := by exact prefixLift 2124067
  have htrace : WordTrace (prefixWord ++ tailWord_2124067) baseStart_2124067 baseEnd_2124067 := by
    simpa [prefixWord, tailWord_2124067, baseEnd_2124067] using wordTrace_append hprefix tailTrace_2124067
  have hstable : (prefixWord ++ tailWord_2124067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124067).length < 2 ^ (prefixWord ++ tailWord_2124067).sum := by decide
  have hdescent : baseEnd_2124067 < baseStart_2124067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124157 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2124157 : Nat := 118140960795 + 2124157 * 2 ^ 59
def prefixEnd_2124157 : Nat := 4983230072969 + 3 ^ 40 * 2124157 * 2
def baseEnd_2124157 : Nat := 727142351075033973112457

theorem tailTrace_2124157 : CollatzResearch.WordTrace tailWord_2124157 prefixEnd_2124157 727142351075033973112457 := by
  unfold tailWord_2124157
  simp only [CollatzResearch.WordTrace]
  refine ⟨77474370565549440978546725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51649580377032960652364483 77474370565549440978546725)
  ·
    refine ⟨14526444481040520183477511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77474370565549440978546725 14526444481040520183477511)
    ·
      refine ⟨21789666721560780275216267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14526444481040520183477511 21789666721560780275216267)
      ·
        refine ⟨32684500082341170412824401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21789666721560780275216267 32684500082341170412824401)
        ·
          refine ⟨24513375061755877809618301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32684500082341170412824401 24513375061755877809618301)
          ·
            refine ⟨9192515648158454178606863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24513375061755877809618301 9192515648158454178606863)
            ·
              refine ⟨13788773472237681267910295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9192515648158454178606863 13788773472237681267910295)
              ·
                refine ⟨20683160208356521901865443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13788773472237681267910295 20683160208356521901865443)
                ·
                  refine ⟨31024740312534782852798165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20683160208356521901865443 31024740312534782852798165)
                  ·
                    refine ⟨727142351075033973112457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31024740312534782852798165 727142351075033973112457)
                    ·
                      rfl

theorem cell22_2124157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2124157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124157 prefixEnd_2124157 := by exact prefixLift 2124157
  have htrace : WordTrace (prefixWord ++ tailWord_2124157) baseStart_2124157 baseEnd_2124157 := by
    simpa [prefixWord, tailWord_2124157, baseEnd_2124157] using wordTrace_append hprefix tailTrace_2124157
  have hstable : (prefixWord ++ tailWord_2124157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124157).length < 2 ^ (prefixWord ++ tailWord_2124157).sum := by decide
  have hdescent : baseEnd_2124157 < baseStart_2124157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124180 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2124180 : Nat := 118140960795 + 2124180 * 2 ^ 59
def prefixEnd_2124180 : Nat := 4983230072969 + 3 ^ 40 * 2124180 * 2
def baseEnd_2124180 : Nat := 727150224445069579787387

theorem tailTrace_2124180 : CollatzResearch.WordTrace tailWord_2124180 prefixEnd_2124180 727150224445069579787387 := by
  unfold tailWord_2124180
  simp only [CollatzResearch.WordTrace]
  refine ⟨38737604722233057953316997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51650139629644077271089329 38737604722233057953316997)
  ·
    refine ⟨7263300885418698366246937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38737604722233057953316997 7263300885418698366246937)
    ·
      refine ⟨5447475664064023774685203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7263300885418698366246937 5447475664064023774685203)
      ·
        refine ⟨8171213496096035662027805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5447475664064023774685203 8171213496096035662027805)
        ·
          refine ⟨3064205061036013373260427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8171213496096035662027805 3064205061036013373260427)
          ·
            refine ⟨4596307591554020059890641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064205061036013373260427 4596307591554020059890641)
            ·
              refine ⟨3447230693665515044917981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4596307591554020059890641 3447230693665515044917981)
              ·
                refine ⟨1292711510124568141844243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447230693665515044917981 1292711510124568141844243)
                ·
                  refine ⟨1939067265186852212766365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292711510124568141844243 1939067265186852212766365)
                  ·
                    refine ⟨727150224445069579787387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939067265186852212766365 727150224445069579787387)
                    ·
                      rfl

theorem cell22_2124180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2124180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124180 prefixEnd_2124180 := by exact prefixLift 2124180
  have htrace : WordTrace (prefixWord ++ tailWord_2124180) baseStart_2124180 baseEnd_2124180 := by
    simpa [prefixWord, tailWord_2124180, baseEnd_2124180] using wordTrace_append hprefix tailTrace_2124180
  have hstable : (prefixWord ++ tailWord_2124180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124180).length < 2 ^ (prefixWord ++ tailWord_2124180).sum := by decide
  have hdescent : baseEnd_2124180 < baseStart_2124180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124193 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 5]
def baseStart_2124193 : Nat := 118140960795 + 2124193 * 2 ^ 59
def prefixEnd_2124193 : Nat := 4983230072969 + 3 ^ 40 * 2124193 * 2
def baseEnd_2124193 : Nat := 242384891536913959737449

theorem tailTrace_2124193 : CollatzResearch.WordTrace tailWord_2124193 prefixEnd_2124193 242384891536913959737449 := by
  unfold tailWord_2124193
  simp only [CollatzResearch.WordTrace]
  refine ⟨77475683593419019126857233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51650455728946012751238155 77475683593419019126857233)
  ·
    refine ⟨58106762695064264345142925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77475683593419019126857233 58106762695064264345142925)
    ·
      refine ⟨21790036010649099129428597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58106762695064264345142925 21790036010649099129428597)
      ·
        refine ⟨2042815875998353043383931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21790036010649099129428597 2042815875998353043383931)
        ·
          refine ⟨3064223813997529565075897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042815875998353043383931 3064223813997529565075897)
          ·
            refine ⟨2298167860498147173806923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3064223813997529565075897 2298167860498147173806923)
            ·
              refine ⟨3447251790747220760710385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298167860498147173806923 3447251790747220760710385)
              ·
                refine ⟨2585438843060415570532789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3447251790747220760710385 2585438843060415570532789)
                ·
                  refine ⟨242384891536913959737449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2585438843060415570532789 242384891536913959737449)
                  ·
                    rfl

theorem cell22_2124193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_2124193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124193 prefixEnd_2124193 := by exact prefixLift 2124193
  have htrace : WordTrace (prefixWord ++ tailWord_2124193) baseStart_2124193 baseEnd_2124193 := by
    simpa [prefixWord, tailWord_2124193, baseEnd_2124193] using wordTrace_append hprefix tailTrace_2124193
  have hstable : (prefixWord ++ tailWord_2124193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124193).length < 2 ^ (prefixWord ++ tailWord_2124193).sum := by decide
  have hdescent : baseEnd_2124193 < baseStart_2124193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124234 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2124234 : Nat := 118140960795 + 2124234 * 2 ^ 59
def prefixEnd_2124234 : Nat := 4983230072969 + 3 ^ 40 * 2124234 * 2
def baseEnd_2124234 : Nat := 727168709748631438937221

theorem tailTrace_2124234 : CollatzResearch.WordTrace tailWord_2124234 prefixEnd_2124234 727168709748631438937221 := by
  unfold tailWord_2124234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369294746567620782274939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51651452657513655419399837 19369294746567620782274939)
  ·
    refine ⟨29053942119851431173412409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19369294746567620782274939 29053942119851431173412409)
    ·
      refine ⟨21790456589888573380059307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29053942119851431173412409 21790456589888573380059307)
      ·
        refine ⟨32685684884832860070088961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21790456589888573380059307 32685684884832860070088961)
        ·
          refine ⟨24514263663624645052566721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32685684884832860070088961 24514263663624645052566721)
          ·
            refine ⟨18385697747718483789425041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24514263663624645052566721 18385697747718483789425041)
            ·
              refine ⟨13789273310788862842068781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18385697747718483789425041 13789273310788862842068781)
              ·
                refine ⟨5170977491545823565775793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13789273310788862842068781 5170977491545823565775793)
                ·
                  refine ⟨3878233118659367674331845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5170977491545823565775793 3878233118659367674331845)
                  ·
                    refine ⟨727168709748631438937221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878233118659367674331845 727168709748631438937221)
                    ·
                      rfl

theorem cell22_2124234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2124234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124234 prefixEnd_2124234 := by exact prefixLift 2124234
  have htrace : WordTrace (prefixWord ++ tailWord_2124234) baseStart_2124234 baseEnd_2124234 := by
    simpa [prefixWord, tailWord_2124234, baseEnd_2124234] using wordTrace_append hprefix tailTrace_2124234
  have hstable : (prefixWord ++ tailWord_2124234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124234).length < 2 ^ (prefixWord ++ tailWord_2124234).sum := by decide
  have hdescent : baseEnd_2124234 < baseStart_2124234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124270 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2124270 : Nat := 118140960795 + 2124270 * 2 ^ 59
def prefixEnd_2124270 : Nat := 4983230072969 + 3 ^ 40 * 2124270 * 2
def baseEnd_2124270 : Nat := 727181033284339345037111

theorem tailTrace_2124270 : CollatzResearch.WordTrace tailWord_2124270 prefixEnd_2124270 727181033284339345037111 := by
  unfold tailWord_2124270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684811501767507659676283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51652328009426707518273509 9684811501767507659676283)
  ·
    refine ⟨14527217252651261489514425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9684811501767507659676283 14527217252651261489514425)
    ·
      refine ⟨10895412939488446117135819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14527217252651261489514425 10895412939488446117135819)
      ·
        refine ⟨16343119409232669175703729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10895412939488446117135819 16343119409232669175703729)
        ·
          refine ⟨12257339556924501881777797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16343119409232669175703729 12257339556924501881777797)
          ·
            refine ⟨2298251166923344102833337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12257339556924501881777797 2298251166923344102833337)
            ·
              refine ⟨1723688375192508077125003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298251166923344102833337 1723688375192508077125003)
              ·
                refine ⟨2585532562788762115687505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723688375192508077125003 2585532562788762115687505)
                ·
                  refine ⟨1939149422091571586765629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585532562788762115687505 1939149422091571586765629)
                  ·
                    refine ⟨727181033284339345037111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939149422091571586765629 727181033284339345037111)
                    ·
                      rfl

theorem cell22_2124270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2124270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124270 prefixEnd_2124270 := by exact prefixLift 2124270
  have htrace : WordTrace (prefixWord ++ tailWord_2124270) baseStart_2124270 baseEnd_2124270 := by
    simpa [prefixWord, tailWord_2124270, baseEnd_2124270] using wordTrace_append hprefix tailTrace_2124270
  have hstable : (prefixWord ++ tailWord_2124270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124270).length < 2 ^ (prefixWord ++ tailWord_2124270).sum := by decide
  have hdescent : baseEnd_2124270 < baseStart_2124270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124298 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_2124298 : Nat := 118140960795 + 2124298 * 2 ^ 59
def prefixEnd_2124298 : Nat := 4983230072969 + 3 ^ 40 * 2124298 * 2
def baseEnd_2124298 : Nat := 727190618256556605337025

theorem tailTrace_2124298 : CollatzResearch.WordTrace tailWord_2124298 prefixEnd_2124298 727190618256556605337025 := by
  unfold tailWord_2124298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369878314509655514857387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51653008838692414706286365 19369878314509655514857387)
  ·
    refine ⟨29054817471764483272286081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19369878314509655514857387 29054817471764483272286081)
    ·
      refine ⟨21791113103823362454214561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29054817471764483272286081 21791113103823362454214561)
      ·
        refine ⟨16343334827867521840660921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21791113103823362454214561 16343334827867521840660921)
        ·
          refine ⟨12257501120900641380495691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16343334827867521840660921 12257501120900641380495691)
          ·
            refine ⟨18386251681350962070743537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12257501120900641380495691 18386251681350962070743537)
            ·
              refine ⟨13789688761013221553057653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18386251681350962070743537 13789688761013221553057653)
              ·
                refine ⟨1292783321344989520599155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13789688761013221553057653 1292783321344989520599155)
                ·
                  refine ⟨1939174982017484280898733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292783321344989520599155 1939174982017484280898733)
                  ·
                    refine ⟨727190618256556605337025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939174982017484280898733 727190618256556605337025)
                    ·
                      rfl

theorem cell22_2124298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_2124298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124298 prefixEnd_2124298 := by exact prefixLift 2124298
  have htrace : WordTrace (prefixWord ++ tailWord_2124298) baseStart_2124298 baseEnd_2124298 := by
    simpa [prefixWord, tailWord_2124298, baseEnd_2124298] using wordTrace_append hprefix tailTrace_2124298
  have hstable : (prefixWord ++ tailWord_2124298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124298).length < 2 ^ (prefixWord ++ tailWord_2124298).sum := by decide
  have hdescent : baseEnd_2124298 < baseStart_2124298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124309 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2124309 : Nat := 118140960795 + 2124309 * 2 ^ 59
def prefixEnd_2124309 : Nat := 4983230072969 + 3 ^ 40 * 2124309 * 2
def baseEnd_2124309 : Nat := 727194383781356243311991

theorem tailTrace_2124309 : CollatzResearch.WordTrace tailWord_2124309 prefixEnd_2124309 727194383781356243311991 := by
  unfold tailWord_2124309
  simp only [CollatzResearch.WordTrace]
  refine ⟨77479914460998770938079981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51653276307332513958719987 77479914460998770938079981)
  ·
    refine ⟨29054967922874539101779993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77479914460998770938079981 29054967922874539101779993)
    ·
      refine ⟨21791225942155904326334995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29054967922874539101779993 21791225942155904326334995)
      ·
        refine ⟨32686838913233856489502493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21791225942155904326334995 32686838913233856489502493)
        ·
          refine ⟨12257564592462696183563435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32686838913233856489502493 12257564592462696183563435)
          ·
            refine ⟨18386346888694044275345153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12257564592462696183563435 18386346888694044275345153)
            ·
              refine ⟨13789760166520533206508865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18386346888694044275345153 13789760166520533206508865)
              ·
                refine ⟨10342320124890399904881649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13789760166520533206508865 10342320124890399904881649)
                ·
                  refine ⟨7756740093667799928661237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10342320124890399904881649 7756740093667799928661237)
                  ·
                    refine ⟨727194383781356243311991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7756740093667799928661237 727194383781356243311991)
                    ·
                      rfl

theorem cell22_2124309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2124309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124309 prefixEnd_2124309 := by exact prefixLift 2124309
  have htrace : WordTrace (prefixWord ++ tailWord_2124309) baseStart_2124309 baseEnd_2124309 := by
    simpa [prefixWord, tailWord_2124309, baseEnd_2124309] using wordTrace_append hprefix tailTrace_2124309
  have hstable : (prefixWord ++ tailWord_2124309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124309).length < 2 ^ (prefixWord ++ tailWord_2124309).sum := by decide
  have hdescent : baseEnd_2124309 < baseStart_2124309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124339 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 6]
def baseStart_2124339 : Nat := 118140960795 + 2124339 * 2 ^ 59
def prefixEnd_2124339 : Nat := 4983230072969 + 3 ^ 40 * 2124339 * 2
def baseEnd_2124339 : Nat := 242401551131482055020633

theorem tailTrace_2124339 : CollatzResearch.WordTrace tailWord_2124339 prefixEnd_2124339 242401551131482055020633 := by
  unfold tailWord_2124339
  simp only [CollatzResearch.WordTrace]
  refine ⟨77481008650890086061672071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51654005767260057374448047 77481008650890086061672071)
  ·
    refine ⟨116221512976335129092508107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77481008650890086061672071 116221512976335129092508107)
    ·
      refine ⟨174332269464502693638762161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116221512976335129092508107 174332269464502693638762161)
      ·
        refine ⟨130749202098377020229071621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174332269464502693638762161 130749202098377020229071621)
        ·
          refine ⟨24515475393445691292950929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130749202098377020229071621 24515475393445691292950929)
          ·
            refine ⟨18386606545084268469713197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24515475393445691292950929 18386606545084268469713197)
            ·
              refine ⟨6894977454406600676142449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18386606545084268469713197 6894977454406600676142449)
              ·
                refine ⟨5171233090804950507106837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6894977454406600676142449 5171233090804950507106837)
                ·
                  refine ⟨242401551131482055020633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5171233090804950507106837 242401551131482055020633)
                  ·
                    rfl

theorem cell22_2124339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_2124339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124339 prefixEnd_2124339 := by exact prefixLift 2124339
  have htrace : WordTrace (prefixWord ++ tailWord_2124339) baseStart_2124339 baseEnd_2124339 := by
    simpa [prefixWord, tailWord_2124339, baseEnd_2124339] using wordTrace_append hprefix tailTrace_2124339
  have hstable : (prefixWord ++ tailWord_2124339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124339).length < 2 ^ (prefixWord ++ tailWord_2124339).sum := by decide
  have hdescent : baseEnd_2124339 < baseStart_2124339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124341 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2124341 : Nat := 118140960795 + 2124341 * 2 ^ 59
def prefixEnd_2124341 : Nat := 4983230072969 + 3 ^ 40 * 2124341 * 2
def baseEnd_2124341 : Nat := 727205338035318826511893

theorem tailTrace_2124341 : CollatzResearch.WordTrace tailWord_2124341 prefixEnd_2124341 727205338035318826511893 := by
  unfold tailWord_2124341
  simp only [CollatzResearch.WordTrace]
  refine ⟨77481081596882840403244877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51654054397921893602163251 77481081596882840403244877)
  ·
    refine ⟨29055405598831065151216829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77481081596882840403244877 29055405598831065151216829)
    ·
      refine ⟨10895777099561649431706311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29055405598831065151216829 10895777099561649431706311)
      ·
        refine ⟨16343665649342474147559467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10895777099561649431706311 16343665649342474147559467)
        ·
          refine ⟨24515498474013711221339201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16343665649342474147559467 24515498474013711221339201)
          ·
            refine ⟨18386623855510283416004401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24515498474013711221339201 18386623855510283416004401)
            ·
              refine ⟨13789967891632712562003301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18386623855510283416004401 13789967891632712562003301)
              ·
                refine ⟨2585618979681133605375619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13789967891632712562003301 2585618979681133605375619)
                ·
                  refine ⟨3878428469521700408063429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585618979681133605375619 3878428469521700408063429)
                  ·
                    refine ⟨727205338035318826511893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878428469521700408063429 727205338035318826511893)
                    ·
                      rfl

theorem cell22_2124341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2124341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124341 prefixEnd_2124341 := by exact prefixLift 2124341
  have htrace : WordTrace (prefixWord ++ tailWord_2124341) baseStart_2124341 baseEnd_2124341 := by
    simpa [prefixWord, tailWord_2124341, baseEnd_2124341] using wordTrace_append hprefix tailTrace_2124341
  have hstable : (prefixWord ++ tailWord_2124341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124341).length < 2 ^ (prefixWord ++ tailWord_2124341).sum := by decide
  have hdescent : baseEnd_2124341 < baseStart_2124341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124484 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2124484 : Nat := 118140960795 + 2124484 * 2 ^ 59
def prefixEnd_2124484 : Nat := 4983230072969 + 3 ^ 40 * 2124484 * 2
def baseEnd_2124484 : Nat := 727254289857714120186455

theorem tailTrace_2124484 : CollatzResearch.WordTrace tailWord_2124484 prefixEnd_2124484 727254289857714120186455 := by
  unfold tailWord_2124484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38743148617682387912850253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51657531490243183883800337 38743148617682387912850253)
  ·
    refine ⟨14528680731630895467318845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38743148617682387912850253 14528680731630895467318845)
    ·
      refine ⟨5448255274361585800244567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14528680731630895467318845 5448255274361585800244567)
      ·
        refine ⟨8172382911542378700366851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5448255274361585800244567 8172382911542378700366851)
        ·
          refine ⟨12258574367313568050550277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8172382911542378700366851 12258574367313568050550277)
          ·
            refine ⟨2298482693871294009478177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12258574367313568050550277 2298482693871294009478177)
            ·
              refine ⟨1723862020403470507108633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298482693871294009478177 1723862020403470507108633)
              ·
                refine ⟨1292896515302602880331475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723862020403470507108633 1292896515302602880331475)
                ·
                  refine ⟨1939344772953904320497213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292896515302602880331475 1939344772953904320497213)
                  ·
                    refine ⟨727254289857714120186455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939344772953904320497213 727254289857714120186455)
                    ·
                      rfl

theorem cell22_2124484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2124484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124484 prefixEnd_2124484 := by exact prefixLift 2124484
  have htrace : WordTrace (prefixWord ++ tailWord_2124484) baseStart_2124484 baseEnd_2124484 := by
    simpa [prefixWord, tailWord_2124484, baseEnd_2124484] using wordTrace_append hprefix tailTrace_2124484
  have hstable : (prefixWord ++ tailWord_2124484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124484).length < 2 ^ (prefixWord ++ tailWord_2124484).sum := by decide
  have hdescent : baseEnd_2124484 < baseStart_2124484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124508 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_2124508 : Nat := 118140960795 + 2124508 * 2 ^ 59
def prefixEnd_2124508 : Nat := 4983230072969 + 3 ^ 40 * 2124508 * 2
def baseEnd_2124508 : Nat := 242420835182728685862127

theorem tailTrace_2124508 : CollatzResearch.WordTrace tailWord_2124508 prefixEnd_2124508 242420835182728685862127 := by
  unfold tailWord_2124508
  simp only [CollatzResearch.WordTrace]
  refine ⟨38743586293638913962287089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51658115058185218616382785 38743586293638913962287089)
  ·
    refine ⟨29057689720229185471715317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38743586293638913962287089 29057689720229185471715317)
    ·
      refine ⟨2724158411271486137973311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29057689720229185471715317 2724158411271486137973311)
      ·
        refine ⟨4086237616907229206959967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724158411271486137973311 4086237616907229206959967)
        ·
          refine ⟨6129356425360843810439951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086237616907229206959967 6129356425360843810439951)
          ·
            refine ⟨9194034638041265715659927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6129356425360843810439951 9194034638041265715659927)
            ·
              refine ⟨13791051957061898573489891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9194034638041265715659927 13791051957061898573489891)
              ·
                refine ⟨20686577935592847860234837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13791051957061898573489891 20686577935592847860234837)
                ·
                  refine ⟨242420835182728685862127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20686577935592847860234837 242420835182728685862127)
                  ·
                    rfl

theorem cell22_2124508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_2124508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124508 prefixEnd_2124508 := by exact prefixLift 2124508
  have htrace : WordTrace (prefixWord ++ tailWord_2124508) baseStart_2124508 baseEnd_2124508 := by
    simpa [prefixWord, tailWord_2124508, baseEnd_2124508] using wordTrace_append hprefix tailTrace_2124508
  have hstable : (prefixWord ++ tailWord_2124508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124508).length < 2 ^ (prefixWord ++ tailWord_2124508).sum := by decide
  have hdescent : baseEnd_2124508 < baseStart_2124508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124525 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2124525 : Nat := 118140960795 + 2124525 * 2 ^ 59
def prefixEnd_2124525 : Nat := 4983230072969 + 3 ^ 40 * 2124525 * 2
def baseEnd_2124525 : Nat := 242422774998534559970443

theorem tailTrace_2124525 : CollatzResearch.WordTrace tailWord_2124525 prefixEnd_2124525 242422774998534559970443 := by
  unfold tailWord_2124525
  simp only [CollatzResearch.WordTrace]
  refine ⟨77487792628216239827943029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51658528418810826551962019 77487792628216239827943029)
  ·
    refine ⟨7264480558895272483869659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77487792628216239827943029 7264480558895272483869659)
    ·
      refine ⟨10896720838342908725804489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7264480558895272483869659 10896720838342908725804489)
      ·
        refine ⟨8172540628757181544353367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10896720838342908725804489 8172540628757181544353367)
        ·
          refine ⟨12258810943135772316530051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8172540628757181544353367 12258810943135772316530051)
          ·
            refine ⟨18388216414703658474795077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12258810943135772316530051 18388216414703658474795077)
            ·
              refine ⟨3447790577756935964024077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18388216414703658474795077 3447790577756935964024077)
              ·
                refine ⟨1292921466658850986509029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447790577756935964024077 1292921466658850986509029)
                ·
                  refine ⟨242422774998534559970443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292921466658850986509029 242422774998534559970443)
                  ·
                    rfl

theorem cell22_2124525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2124525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124525 prefixEnd_2124525 := by exact prefixLift 2124525
  have htrace : WordTrace (prefixWord ++ tailWord_2124525) baseStart_2124525 baseEnd_2124525 := by
    simpa [prefixWord, tailWord_2124525, baseEnd_2124525] using wordTrace_append hprefix tailTrace_2124525
  have hstable : (prefixWord ++ tailWord_2124525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124525).length < 2 ^ (prefixWord ++ tailWord_2124525).sum := by decide
  have hdescent : baseEnd_2124525 < baseStart_2124525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124540 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_2124540 : Nat := 118140960795 + 2124540 * 2 ^ 59
def prefixEnd_2124540 : Nat := 4983230072969 + 3 ^ 40 * 2124540 * 2
def baseEnd_2124540 : Nat := 727273459802148640786283

theorem tailTrace_2124540 : CollatzResearch.WordTrace tailWord_2124540 prefixEnd_2124540 727273459802148640786283 := by
  unfold tailWord_2124540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38744169861580948694869537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51658893148774598259826049 38744169861580948694869537)
  ·
    refine ⟨29058127396185711521152153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38744169861580948694869537 29058127396185711521152153)
    ·
      refine ⟨21793595547139283640864115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29058127396185711521152153 21793595547139283640864115)
      ·
        refine ⟨32690393320708925461296173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21793595547139283640864115 32690393320708925461296173)
        ·
          refine ⟨12258897495265847047986065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32690393320708925461296173 12258897495265847047986065)
          ·
            refine ⟨9194173121449385285989549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12258897495265847047986065 9194173121449385285989549)
            ·
              refine ⟨3447814920543519482246081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9194173121449385285989549 3447814920543519482246081)
              ·
                refine ⟨2585861190407639611684561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3447814920543519482246081 2585861190407639611684561)
                ·
                  refine ⟨1939395892805729708763421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585861190407639611684561 1939395892805729708763421)
                  ·
                    refine ⟨727273459802148640786283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939395892805729708763421 727273459802148640786283)
                    ·
                      rfl

theorem cell22_2124540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_2124540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124540 prefixEnd_2124540 := by exact prefixLift 2124540
  have htrace : WordTrace (prefixWord ++ tailWord_2124540) baseStart_2124540 baseEnd_2124540 := by
    simpa [prefixWord, tailWord_2124540, baseEnd_2124540] using wordTrace_append hprefix tailTrace_2124540
  have hstable : (prefixWord ++ tailWord_2124540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124540).length < 2 ^ (prefixWord ++ tailWord_2124540).sum := by decide
  have hdescent : baseEnd_2124540 < baseStart_2124540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124581 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 9]
def baseStart_2124581 : Nat := 118140960795 + 2124581 * 2 ^ 59
def prefixEnd_2124581 : Nat := 4983230072969 + 3 ^ 40 * 2124581 * 2
def baseEnd_2124581 : Nat := 242429164980012733503719

theorem tailTrace_2124581 : CollatzResearch.WordTrace tailWord_2124581 prefixEnd_2124581 242429164980012733503719 := by
  unfold tailWord_2124581
  simp only [CollatzResearch.WordTrace]
  refine ⟨77489835116013361391981597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51659890077342240927987731 77489835116013361391981597)
  ·
    refine ⟨29058688168505010521993099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77489835116013361391981597 29058688168505010521993099)
    ·
      refine ⟨43588032252757515782989649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29058688168505010521993099 43588032252757515782989649)
      ·
        refine ⟨32691024189568136837242237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43588032252757515782989649 32691024189568136837242237)
        ·
          refine ⟨12259134071088051313965839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32691024189568136837242237 12259134071088051313965839)
          ·
            refine ⟨18388701106632076970948759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12259134071088051313965839 18388701106632076970948759)
            ·
              refine ⟨27583051659948115456423139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18388701106632076970948759 27583051659948115456423139)
              ·
                refine ⟨41374577489922173184634709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27583051659948115456423139 41374577489922173184634709)
                ·
                  refine ⟨242429164980012733503719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41374577489922173184634709 242429164980012733503719)
                  ·
                    rfl

theorem cell22_2124581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_2124581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124581 prefixEnd_2124581 := by exact prefixLift 2124581
  have htrace : WordTrace (prefixWord ++ tailWord_2124581) baseStart_2124581 baseEnd_2124581 := by
    simpa [prefixWord, tailWord_2124581, baseEnd_2124581] using wordTrace_append hprefix tailTrace_2124581
  have hstable : (prefixWord ++ tailWord_2124581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124581).length < 2 ^ (prefixWord ++ tailWord_2124581).sum := by decide
  have hdescent : baseEnd_2124581 < baseStart_2124581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124602 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_2124602 : Nat := 118140960795 + 2124602 * 2 ^ 59
def prefixEnd_2124602 : Nat := 4983230072969 + 3 ^ 40 * 2124602 * 2
def baseEnd_2124602 : Nat := 727294683669201145736093

theorem tailTrace_2124602 : CollatzResearch.WordTrace tailWord_2124602 prefixEnd_2124602 727294683669201145736093 := by
  unfold tailWord_2124602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19372650262234320494624015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51660400699291521318997373 19372650262234320494624015)
  ·
    refine ⟨29058975393351480741936023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19372650262234320494624015 29058975393351480741936023)
    ·
      refine ⟨43588463090027221112904035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29058975393351480741936023 43588463090027221112904035)
      ·
        refine ⟨65382694635040831669356053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43588463090027221112904035 65382694635040831669356053)
        ·
          refine ⟨3064813811017538984501065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65382694635040831669356053 3064813811017538984501065)
          ·
            refine ⟨2298610358263154238375799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3064813811017538984501065 2298610358263154238375799)
            ·
              refine ⟨3447915537394731357563699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298610358263154238375799 3447915537394731357563699)
              ·
                refine ⟨5171873306092097036345549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447915537394731357563699 5171873306092097036345549)
                ·
                  refine ⟨1939452489784536388629581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5171873306092097036345549 1939452489784536388629581)
                  ·
                    refine ⟨727294683669201145736093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939452489784536388629581 727294683669201145736093)
                    ·
                      rfl

theorem cell22_2124602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_2124602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124602 prefixEnd_2124602 := by exact prefixLift 2124602
  have htrace : WordTrace (prefixWord ++ tailWord_2124602) baseStart_2124602 baseEnd_2124602 := by
    simpa [prefixWord, tailWord_2124602, baseEnd_2124602] using wordTrace_append hprefix tailTrace_2124602
  have hstable : (prefixWord ++ tailWord_2124602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124602).length < 2 ^ (prefixWord ++ tailWord_2124602).sum := by decide
  have hdescent : baseEnd_2124602 < baseStart_2124602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124675 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 2, 3]
def baseStart_2124675 : Nat := 118140960795 + 2124675 * 2 ^ 59
def prefixEnd_2124675 : Nat := 4983230072969 + 3 ^ 40 * 2124675 * 2
def baseEnd_2124675 : Nat := 727319673061053288660869

theorem tailTrace_2124675 : CollatzResearch.WordTrace tailWord_2124675 prefixEnd_2124675 727319673061053288660869 := by
  unfold tailWord_2124675
  simp only [CollatzResearch.WordTrace]
  refine ⟨77493263577672815445903479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51662175718448543630602319 77493263577672815445903479)
  ·
    refine ⟨116239895366509223168855219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77493263577672815445903479 116239895366509223168855219)
    ·
      refine ⟨174359843049763834753282829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116239895366509223168855219 174359843049763834753282829)
      ·
        refine ⟨65384941143661438032481061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174359843049763834753282829 65384941143661438032481061)
        ·
          refine ⟨12259676464436519631090199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65384941143661438032481061 12259676464436519631090199)
          ·
            refine ⟨18389514696654779446635299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12259676464436519631090199 18389514696654779446635299)
            ·
              refine ⟨27584272044982169169952949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18389514696654779446635299 27584272044982169169952949)
              ·
                refine ⟨2586025504217078359683089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27584272044982169169952949 2586025504217078359683089)
                ·
                  refine ⟨1939519128162808769762317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2586025504217078359683089 1939519128162808769762317)
                  ·
                    refine ⟨727319673061053288660869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939519128162808769762317 727319673061053288660869)
                    ·
                      rfl

theorem cell22_2124675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 3].length) (baseStart_2124675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124675 prefixEnd_2124675 := by exact prefixLift 2124675
  have htrace : WordTrace (prefixWord ++ tailWord_2124675) baseStart_2124675 baseEnd_2124675 := by
    simpa [prefixWord, tailWord_2124675, baseEnd_2124675] using wordTrace_append hprefix tailTrace_2124675
  have hstable : (prefixWord ++ tailWord_2124675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124675).length < 2 ^ (prefixWord ++ tailWord_2124675).sum := by decide
  have hdescent : baseEnd_2124675 < baseStart_2124675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124810 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2124810 : Nat := 118140960795 + 2124810 * 2 ^ 59
def prefixEnd_2124810 : Nat := 4983230072969 + 3 ^ 40 * 2124810 * 2
def baseEnd_2124810 : Nat := 727365886319957936535455

theorem tailTrace_2124810 : CollatzResearch.WordTrace tailWord_2124810 prefixEnd_2124810 727365886319957936535455 := by
  unfold tailWord_2124810
  simp only [CollatzResearch.WordTrace]
  refine ⟨19374546858045933375516971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51665458288122489001378589 19374546858045933375516971)
  ·
    refine ⟨29061820287068900063275457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19374546858045933375516971 29061820287068900063275457)
    ·
      refine ⟨21796365215301675047456593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29061820287068900063275457 21796365215301675047456593)
      ·
        refine ⟨16347273911476256285592445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21796365215301675047456593 16347273911476256285592445)
        ·
          refine ⟨6130227716803596107097167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16347273911476256285592445 6130227716803596107097167)
          ·
            refine ⟨9195341575205394160645751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130227716803596107097167 9195341575205394160645751)
            ·
              refine ⟨13793012362808091240968627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9195341575205394160645751 13793012362808091240968627)
              ·
                refine ⟨20689518544212136861452941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13793012362808091240968627 20689518544212136861452941)
                ·
                  refine ⟨7758569454079551323044853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20689518544212136861452941 7758569454079551323044853)
                  ·
                    refine ⟨727365886319957936535455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7758569454079551323044853 727365886319957936535455)
                    ·
                      rfl

theorem cell22_2124810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2124810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124810 prefixEnd_2124810 := by exact prefixLift 2124810
  have htrace : WordTrace (prefixWord ++ tailWord_2124810) baseStart_2124810 baseEnd_2124810 := by
    simpa [prefixWord, tailWord_2124810, baseEnd_2124810] using wordTrace_append hprefix tailTrace_2124810
  have hstable : (prefixWord ++ tailWord_2124810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124810).length < 2 ^ (prefixWord ++ tailWord_2124810).sum := by decide
  have hdescent : baseEnd_2124810 < baseStart_2124810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124814 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2124814 : Nat := 118140960795 + 2124814 * 2 ^ 59
def prefixEnd_2124814 : Nat := 4983230072969 + 3 ^ 40 * 2124814 * 2
def baseEnd_2124814 : Nat := 727367255601703259435443

theorem tailTrace_2124814 : CollatzResearch.WordTrace tailWord_2124814 prefixEnd_2124814 727367255601703259435443 := by
  unfold tailWord_2124814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9687291665521155273151687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51665555549446161456808997 9687291665521155273151687)
  ·
    refine ⟨14530937498281732909727531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9687291665521155273151687 14530937498281732909727531)
    ·
      refine ⟨21796406247422599364591297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14530937498281732909727531 21796406247422599364591297)
      ·
        refine ⟨16347304685566949523443473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21796406247422599364591297 16347304685566949523443473)
        ·
          refine ⟨12260478514175212142582605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16347304685566949523443473 12260478514175212142582605)
          ·
            refine ⟨4597679442815704553468477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12260478514175212142582605 4597679442815704553468477)
            ·
              refine ⟨1724129791055889207550679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4597679442815704553468477 1724129791055889207550679)
              ·
                refine ⟨2586194686583833811326019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724129791055889207550679 2586194686583833811326019)
                ·
                  refine ⟨3879292029875750716989029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586194686583833811326019 3879292029875750716989029)
                  ·
                    refine ⟨727367255601703259435443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879292029875750716989029 727367255601703259435443)
                    ·
                      rfl

theorem cell22_2124814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2124814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124814 prefixEnd_2124814 := by exact prefixLift 2124814
  have htrace : WordTrace (prefixWord ++ tailWord_2124814) baseStart_2124814 baseEnd_2124814 := by
    simpa [prefixWord, tailWord_2124814, baseEnd_2124814] using wordTrace_append hprefix tailTrace_2124814
  have hstable : (prefixWord ++ tailWord_2124814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124814).length < 2 ^ (prefixWord ++ tailWord_2124814).sum := by decide
  have hdescent : baseEnd_2124814 < baseStart_2124814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124825 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_2124825 : Nat := 118140960795 + 2124825 * 2 ^ 59
def prefixEnd_2124825 : Nat := 4983230072969 + 3 ^ 40 * 2124825 * 2
def baseEnd_2124825 : Nat := 727371021126502897410409

theorem tailTrace_2124825 : CollatzResearch.WordTrace tailWord_2124825 prefixEnd_2124825 727371021126502897410409 := by
  unfold tailWord_2124825
  simp only [CollatzResearch.WordTrace]
  refine ⟨77498734527129391063863929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51665823018086260709242619 77498734527129391063863929)
  ·
    refine ⟨58124050895347043297897947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77498734527129391063863929 58124050895347043297897947)
    ·
      refine ⟨87186076343020564946846921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58124050895347043297897947 87186076343020564946846921)
      ·
        refine ⟨65389557257265423710135191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87186076343020564946846921 65389557257265423710135191)
        ·
          refine ⟨98084335885898135565202787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65389557257265423710135191 98084335885898135565202787)
          ·
            refine ⟨147126503828847203347804181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98084335885898135565202787 147126503828847203347804181)
            ·
              refine ⟨6896554866977212656928321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147126503828847203347804181 6896554866977212656928321)
              ·
                refine ⟨5172416150232909492696241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6896554866977212656928321 5172416150232909492696241)
                ·
                  refine ⟨3879312112674682119522181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5172416150232909492696241 3879312112674682119522181)
                  ·
                    refine ⟨727371021126502897410409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879312112674682119522181 727371021126502897410409)
                    ·
                      rfl

theorem cell22_2124825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_2124825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124825 prefixEnd_2124825 := by exact prefixLift 2124825
  have htrace : WordTrace (prefixWord ++ tailWord_2124825) baseStart_2124825 baseEnd_2124825 := by
    simpa [prefixWord, tailWord_2124825, baseEnd_2124825] using wordTrace_append hprefix tailTrace_2124825
  have hstable : (prefixWord ++ tailWord_2124825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124825).length < 2 ^ (prefixWord ++ tailWord_2124825).sum := by decide
  have hdescent : baseEnd_2124825 < baseStart_2124825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124829 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 4]
def baseStart_2124829 : Nat := 118140960795 + 2124829 * 2 ^ 59
def prefixEnd_2124829 : Nat := 4983230072969 + 3 ^ 40 * 2124829 * 2
def baseEnd_2124829 : Nat := 242457463469416073436799

theorem tailTrace_2124829 : CollatzResearch.WordTrace tailWord_2124829 prefixEnd_2124829 242457463469416073436799 := by
  unfold tailWord_2124829
  simp only [CollatzResearch.WordTrace]
  refine ⟨77498880419114899747009541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51665920279409933164673027 77498880419114899747009541)
  ·
    refine ⟨14531040078584043702564289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77498880419114899747009541 14531040078584043702564289)
    ·
      refine ⟨10898280058938032776923217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14531040078584043702564289 10898280058938032776923217)
      ·
        refine ⟨8173710044203524582692413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10898280058938032776923217 8173710044203524582692413)
        ·
          refine ⟨3065141266576321718509655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8173710044203524582692413 3065141266576321718509655)
          ·
            refine ⟨4597711899864482577764483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065141266576321718509655 4597711899864482577764483)
            ·
              refine ⟨6896567849796723866646725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597711899864482577764483 6896567849796723866646725)
              ·
                refine ⟨1293106471836885724996261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6896567849796723866646725 1293106471836885724996261)
                ·
                  refine ⟨242457463469416073436799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293106471836885724996261 242457463469416073436799)
                  ·
                    rfl

theorem cell22_2124829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_2124829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124829 prefixEnd_2124829 := by exact prefixLift 2124829
  have htrace : WordTrace (prefixWord ++ tailWord_2124829) baseStart_2124829 baseEnd_2124829 := by
    simpa [prefixWord, tailWord_2124829, baseEnd_2124829] using wordTrace_append hprefix tailTrace_2124829
  have hstable : (prefixWord ++ tailWord_2124829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124829).length < 2 ^ (prefixWord ++ tailWord_2124829).sum := by decide
  have hdescent : baseEnd_2124829 < baseStart_2124829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124857 : List Nat := [1, 2, 1, 5, 2, 2, 3, 6]
def baseStart_2124857 : Nat := 118140960795 + 2124857 * 2 ^ 59
def prefixEnd_2124857 : Nat := 4983230072969 + 3 ^ 40 * 2124857 * 2
def baseEnd_2124857 : Nat := 80820219486718386734479

theorem tailTrace_2124857 : CollatzResearch.WordTrace tailWord_2124857 prefixEnd_2124857 80820219486718386734479 := by
  unfold tailWord_2124857
  simp only [CollatzResearch.WordTrace]
  refine ⟨77499901663013460529028825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51666601108675640352685883 77499901663013460529028825)
  ·
    refine ⟨58124926247260095396771619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77499901663013460529028825 58124926247260095396771619)
    ·
      refine ⟨87187389370890143095157429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58124926247260095396771619 87187389370890143095157429)
      ·
        refine ⟨8173817753520950915171009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87187389370890143095157429 8173817753520950915171009)
        ·
          refine ⟨6130363315140713186378257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8173817753520950915171009 6130363315140713186378257)
          ·
            refine ⟨4597772486355534889783693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6130363315140713186378257 4597772486355534889783693)
            ·
              refine ⟨1724164682383325583668885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4597772486355534889783693 1724164682383325583668885)
              ·
                refine ⟨80820219486718386734479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1724164682383325583668885 80820219486718386734479)
                ·
                  rfl

theorem cell22_2124857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 6].length) (baseStart_2124857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124857 prefixEnd_2124857 := by exact prefixLift 2124857
  have htrace : WordTrace (prefixWord ++ tailWord_2124857) baseStart_2124857 baseEnd_2124857 := by
    simpa [prefixWord, tailWord_2124857, baseEnd_2124857] using wordTrace_append hprefix tailTrace_2124857
  have hstable : (prefixWord ++ tailWord_2124857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124857).length < 2 ^ (prefixWord ++ tailWord_2124857).sum := by decide
  have hdescent : baseEnd_2124857 < baseStart_2124857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124885 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 7]
def baseStart_2124885 : Nat := 118140960795 + 2124885 * 2 ^ 59
def prefixEnd_2124885 : Nat := 4983230072969 + 3 ^ 40 * 2124885 * 2
def baseEnd_2124885 : Nat := 242463853450894246970075

theorem tailTrace_2124885 : CollatzResearch.WordTrace tailWord_2124885 prefixEnd_2124885 242463853450894246970075 := by
  unfold tailWord_2124885
  simp only [CollatzResearch.WordTrace]
  refine ⟨77500922906912021311048109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51667281937941347540698739 77500922906912021311048109)
  ·
    refine ⟨29062846090092007991643041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77500922906912021311048109 29062846090092007991643041)
    ·
      refine ⟨21797134567569005993732281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29062846090092007991643041 21797134567569005993732281)
      ·
        refine ⟨16347850925676754495299211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21797134567569005993732281 16347850925676754495299211)
        ·
          refine ⟨24521776388515131742948817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16347850925676754495299211 24521776388515131742948817)
          ·
            refine ⟨18391332291386348807211613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24521776388515131742948817 18391332291386348807211613)
            ·
              refine ⟨6896749609269880802704355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18391332291386348807211613 6896749609269880802704355)
              ·
                refine ⟨10345124413904821204056533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6896749609269880802704355 10345124413904821204056533)
                ·
                  refine ⟨242463853450894246970075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10345124413904821204056533 242463853450894246970075)
                  ·
                    rfl

theorem cell22_2124885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_2124885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124885 prefixEnd_2124885 := by exact prefixLift 2124885
  have htrace : WordTrace (prefixWord ++ tailWord_2124885) baseStart_2124885 baseEnd_2124885 := by
    simpa [prefixWord, tailWord_2124885, baseEnd_2124885] using wordTrace_append hprefix tailTrace_2124885
  have hstable : (prefixWord ++ tailWord_2124885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124885).length < 2 ^ (prefixWord ++ tailWord_2124885).sum := by decide
  have hdescent : baseEnd_2124885 < baseStart_2124885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124947 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 4]
def baseStart_2124947 : Nat := 118140960795 + 2124947 * 2 ^ 59
def prefixEnd_2124947 : Nat := 4983230072969 + 3 ^ 40 * 2124947 * 2
def baseEnd_2124947 : Nat := 242470928073245081953345

theorem tailTrace_2124947 : CollatzResearch.WordTrace tailWord_2124947 prefixEnd_2124947 242470928073245081953345 := by
  unfold tailWord_2124947
  simp only [CollatzResearch.WordTrace]
  refine ⟨77503184232687405899805095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51668789488458270599870063 77503184232687405899805095)
  ·
    refine ⟨116254776349031108849707643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77503184232687405899805095 116254776349031108849707643)
    ·
      refine ⟨174382164523546663274561465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116254776349031108849707643 174382164523546663274561465)
      ·
        refine ⟨130786623392659997455921099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174382164523546663274561465 130786623392659997455921099)
        ·
          refine ⟨196179935088989996183881649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130786623392659997455921099 196179935088989996183881649)
          ·
            refine ⟨147134951316742497137911237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196179935088989996183881649 147134951316742497137911237)
            ·
              refine ⟨27587803371889218213358357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147134951316742497137911237 27587803371889218213358357)
              ·
                refine ⟨1293178283057307103751173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27587803371889218213358357 1293178283057307103751173)
                ·
                  refine ⟨242470928073245081953345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293178283057307103751173 242470928073245081953345)
                  ·
                    rfl

theorem cell22_2124947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 4].length) (baseStart_2124947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124947 prefixEnd_2124947 := by exact prefixLift 2124947
  have htrace : WordTrace (prefixWord ++ tailWord_2124947) baseStart_2124947 baseEnd_2124947 := by
    simpa [prefixWord, tailWord_2124947, baseEnd_2124947] using wordTrace_append hprefix tailTrace_2124947
  have hstable : (prefixWord ++ tailWord_2124947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124947).length < 2 ^ (prefixWord ++ tailWord_2124947).sum := by decide
  have hdescent : baseEnd_2124947 < baseStart_2124947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124975 : List Nat := [1, 1, 2, 1, 2, 3, 4, 8]
def baseStart_2124975 : Nat := 118140960795 + 2124975 * 2 ^ 59
def prefixEnd_2124975 : Nat := 4983230072969 + 3 ^ 40 * 2124975 * 2
def baseEnd_2124975 : Nat := 80824707687994722906661

theorem tailTrace_2124975 : CollatzResearch.WordTrace tailWord_2124975 prefixEnd_2124975 80824707687994722906661 := by
  unfold tailWord_2124975
  simp only [CollatzResearch.WordTrace]
  refine ⟨77504205476585966681824379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51669470317723977787882919 77504205476585966681824379)
  ·
    refine ⟨116256308214878950022736569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77504205476585966681824379 116256308214878950022736569)
    ·
      refine ⟨87192231161159212517052427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116256308214878950022736569 87192231161159212517052427)
      ·
        refine ⟨130788346741738818775578641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87192231161159212517052427 130788346741738818775578641)
        ·
          refine ⟨98091260056304114081683981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130788346741738818775578641 98091260056304114081683981)
          ·
            refine ⟨36784222521114042780631493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98091260056304114081683981 36784222521114042780631493)
            ·
              refine ⟨6897041722708883021368405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36784222521114042780631493 6897041722708883021368405)
              ·
                refine ⟨80824707687994722906661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6897041722708883021368405 80824707687994722906661)
                ·
                  rfl

theorem cell22_2124975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 8].length) (baseStart_2124975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124975 prefixEnd_2124975 := by exact prefixLift 2124975
  have htrace : WordTrace (prefixWord ++ tailWord_2124975) baseStart_2124975 baseEnd_2124975 := by
    simpa [prefixWord, tailWord_2124975, baseEnd_2124975] using wordTrace_append hprefix tailTrace_2124975
  have hstable : (prefixWord ++ tailWord_2124975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124975).length < 2 ^ (prefixWord ++ tailWord_2124975).sum := by decide
  have hdescent : baseEnd_2124975 < baseStart_2124975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124992 : List Nat := [2, 1, 1, 2, 7, 9]
def baseStart_2124992 : Nat := 118140960795 + 2124992 * 2 ^ 59
def prefixEnd_2124992 : Nat := 4983230072969 + 3 ^ 40 * 2124992 * 2
def baseEnd_2124992 : Nat := 8980594921473705289937

theorem tailTrace_2124992 : CollatzResearch.WordTrace tailWord_2124992 prefixEnd_2124992 8980594921473705289937 := by
  unfold tailWord_2124992
  simp only [CollatzResearch.WordTrace]
  refine ⟨38752412758762189292596615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51669883678349585723462153 38752412758762189292596615)
  ·
    refine ⟨58128619138143283938894923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38752412758762189292596615 58128619138143283938894923)
    ·
      refine ⟨87192928707214925908342385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58128619138143283938894923 87192928707214925908342385)
      ·
        refine ⟨65394696530411194431256789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87192928707214925908342385 65394696530411194431256789)
        ·
          refine ⟨1532688199931512369482581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65394696530411194431256789 1532688199931512369482581)
          ·
            refine ⟨8980594921473705289937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1532688199931512369482581 8980594921473705289937)
            ·
              rfl

theorem cell22_2124992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 9].length) (baseStart_2124992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2124992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2124992 prefixEnd_2124992 := by exact prefixLift 2124992
  have htrace : WordTrace (prefixWord ++ tailWord_2124992) baseStart_2124992 baseEnd_2124992 := by
    simpa [prefixWord, tailWord_2124992, baseEnd_2124992] using wordTrace_append hprefix tailTrace_2124992
  have hstable : (prefixWord ++ tailWord_2124992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124992).length < 2 ^ (prefixWord ++ tailWord_2124992).sum := by decide
  have hdescent : baseEnd_2124992 < baseStart_2124992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125024 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_2125024 : Nat := 118140960795 + 2125024 * 2 ^ 59
def prefixEnd_2125024 : Nat := 4983230072969 + 3 ^ 40 * 2125024 * 2
def baseEnd_2125024 : Nat := 727439142893332711684799

theorem tailTrace_2125024 : CollatzResearch.WordTrace tailWord_2125024 prefixEnd_2125024 727439142893332711684799 := by
  unfold tailWord_2125024
  simp only [CollatzResearch.WordTrace]
  refine ⟨38752996326704224025179063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51670661768938965366905417 38752996326704224025179063)
  ·
    refine ⟨58129494490056336037768595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38752996326704224025179063 58129494490056336037768595)
    ·
      refine ⟨87194241735084504056652893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58129494490056336037768595 87194241735084504056652893)
      ·
        refine ⟨32697840650656689021244835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87194241735084504056652893 32697840650656689021244835)
        ·
          refine ⟨49046760975985033531867253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32697840650656689021244835 49046760975985033531867253)
          ·
            refine ⟨4598133841498596893612555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49046760975985033531867253 4598133841498596893612555)
            ·
              refine ⟨6897200762247895340418833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598133841498596893612555 6897200762247895340418833)
              ·
                refine ⟨5172900571685921505314125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6897200762247895340418833 5172900571685921505314125)
                ·
                  refine ⟨1939837714382220564492797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5172900571685921505314125 1939837714382220564492797)
                  ·
                    refine ⟨727439142893332711684799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939837714382220564492797 727439142893332711684799)
                    ·
                      rfl

theorem cell22_2125024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_2125024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125024 prefixEnd_2125024 := by exact prefixLift 2125024
  have htrace : WordTrace (prefixWord ++ tailWord_2125024) baseStart_2125024 baseEnd_2125024 := by
    simpa [prefixWord, tailWord_2125024, baseEnd_2125024] using wordTrace_append hprefix tailTrace_2125024
  have hstable : (prefixWord ++ tailWord_2125024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125024).length < 2 ^ (prefixWord ++ tailWord_2125024).sum := by decide
  have hdescent : baseEnd_2125024 < baseStart_2125024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125054 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2125054 : Nat := 118140960795 + 2125054 * 2 ^ 59
def prefixEnd_2125054 : Nat := 4983230072969 + 3 ^ 40 * 2125054 * 2
def baseEnd_2125054 : Nat := 242483137502140877811569

theorem tailTrace_2125054 : CollatzResearch.WordTrace tailWord_2125054 prefixEnd_2125054 242483137502140877811569 := by
  unfold tailWord_2125054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688385855412470396743777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51671391228866508782633477 9688385855412470396743777)
  ·
    refine ⟨7266289391559352797557833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9688385855412470396743777 7266289391559352797557833)
    ·
      refine ⟨5449717043669514598168375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7266289391559352797557833 5449717043669514598168375)
      ·
        refine ⟨8174575565504271897252563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5449717043669514598168375 8174575565504271897252563)
        ·
          refine ⟨12261863348256407845878845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8174575565504271897252563 12261863348256407845878845)
          ·
            refine ⟨4598198755596152942204567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12261863348256407845878845 4598198755596152942204567)
            ·
              refine ⟨6897298133394229413306851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598198755596152942204567 6897298133394229413306851)
              ·
                refine ⟨10345947200091344119960277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6897298133394229413306851 10345947200091344119960277)
                ·
                  refine ⟨242483137502140877811569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10345947200091344119960277 242483137502140877811569)
                  ·
                    rfl

theorem cell22_2125054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2125054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125054 prefixEnd_2125054 := by exact prefixLift 2125054
  have htrace : WordTrace (prefixWord ++ tailWord_2125054) baseStart_2125054 baseEnd_2125054 := by
    simpa [prefixWord, tailWord_2125054, baseEnd_2125054] using wordTrace_append hprefix tailTrace_2125054
  have hstable : (prefixWord ++ tailWord_2125054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125054).length < 2 ^ (prefixWord ++ tailWord_2125054).sum := by decide
  have hdescent : baseEnd_2125054 < baseStart_2125054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125058 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2125058 : Nat := 118140960795 + 2125058 * 2 ^ 59
def prefixEnd_2125058 : Nat := 4983230072969 + 3 ^ 40 * 2125058 * 2
def baseEnd_2125058 : Nat := 727450781788167956334695

theorem tailTrace_2125058 : CollatzResearch.WordTrace tailWord_2125058 prefixEnd_2125058 727450781788167956334695 := by
  unfold tailWord_2125058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19376808183821317964273957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51671488490190181238063885 19376808183821317964273957)
  ·
    refine ⟨3633151534466497118301367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19376808183821317964273957 3633151534466497118301367)
    ·
      refine ⟨5449727301699745677452051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3633151534466497118301367 5449727301699745677452051)
      ·
        refine ⟨8174590952549618516178077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5449727301699745677452051 8174590952549618516178077)
        ·
          refine ⟨3065471607206106943566779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8174590952549618516178077 3065471607206106943566779)
          ·
            refine ⟨4598207410809160415350169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065471607206106943566779 4598207410809160415350169)
            ·
              refine ⟨3448655558106870311512627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4598207410809160415350169 3448655558106870311512627)
              ·
                refine ⟨5172983337160305467268941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448655558106870311512627 5172983337160305467268941)
                ·
                  refine ⟨1939868751435114550225853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5172983337160305467268941 1939868751435114550225853)
                  ·
                    refine ⟨727450781788167956334695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939868751435114550225853 727450781788167956334695)
                    ·
                      rfl

theorem cell22_2125058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2125058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125058 prefixEnd_2125058 := by exact prefixLift 2125058
  have htrace : WordTrace (prefixWord ++ tailWord_2125058) baseStart_2125058 baseEnd_2125058 := by
    simpa [prefixWord, tailWord_2125058, baseEnd_2125058] using wordTrace_append hprefix tailTrace_2125058
  have hstable : (prefixWord ++ tailWord_2125058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125058).length < 2 ^ (prefixWord ++ tailWord_2125058).sum := by decide
  have hdescent : baseEnd_2125058 < baseStart_2125058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125084 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2125084 : Nat := 118140960795 + 2125084 * 2 ^ 59
def prefixEnd_2125084 : Nat := 4983230072969 + 3 ^ 40 * 2125084 * 2
def baseEnd_2125084 : Nat := 727459682119512555184615

theorem tailTrace_2125084 : CollatzResearch.WordTrace tailWord_2125084 prefixEnd_2125084 727459682119512555184615 := by
  unfold tailWord_2125084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38754090516595539148771153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51672120688794052198361537 38754090516595539148771153)
  ·
    refine ⟨29065567887446654361578365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38754090516595539148771153 29065567887446654361578365)
    ·
      refine ⟨10899587957792495385591887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29065567887446654361578365 10899587957792495385591887)
      ·
        refine ⟨16349381936688743078387831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10899587957792495385591887 16349381936688743078387831)
        ·
          refine ⟨24524072905033114617581747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16349381936688743078387831 24524072905033114617581747)
          ·
            refine ⟨36786109357549671926372621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24524072905033114617581747 36786109357549671926372621)
            ·
              refine ⟨13794791009081126972389733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36786109357549671926372621 13794791009081126972389733)
              ·
                refine ⟨2586523314202711307323075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13794791009081126972389733 2586523314202711307323075)
                ·
                  refine ⟨3879784971304066960984613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586523314202711307323075 3879784971304066960984613)
                  ·
                    refine ⟨727459682119512555184615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879784971304066960984613 727459682119512555184615)
                    ·
                      rfl

theorem cell22_2125084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2125084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125084 prefixEnd_2125084 := by exact prefixLift 2125084
  have htrace : WordTrace (prefixWord ++ tailWord_2125084) baseStart_2125084 baseEnd_2125084 := by
    simpa [prefixWord, tailWord_2125084, baseEnd_2125084] using wordTrace_append hprefix tailTrace_2125084
  have hstable : (prefixWord ++ tailWord_2125084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125084).length < 2 ^ (prefixWord ++ tailWord_2125084).sum := by decide
  have hdescent : baseEnd_2125084 < baseStart_2125084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125114 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_2125114 : Nat := 118140960795 + 2125114 * 2 ^ 59
def prefixEnd_2125114 : Nat := 4983230072969 + 3 ^ 40 * 2125114 * 2
def baseEnd_2125114 : Nat := 727469951732602476934523

theorem tailTrace_2125114 : CollatzResearch.WordTrace tailWord_2125114 prefixEnd_2125114 727469951732602476934523 := by
  unfold tailWord_2125114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19377318805770598355283599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51672850148721595614089597 19377318805770598355283599)
  ·
    refine ⟨29065978208655897532925399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19377318805770598355283599 29065978208655897532925399)
    ·
      refine ⟨43598967312983846299388099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29065978208655897532925399 43598967312983846299388099)
      ·
        refine ⟨65398450969475769449082149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43598967312983846299388099 65398450969475769449082149)
        ·
          refine ⟨12262209556776706771702903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65398450969475769449082149 12262209556776706771702903)
          ·
            refine ⟨18393314335165060157554355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12262209556776706771702903 18393314335165060157554355)
            ·
              refine ⟨27589971502747590236331533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18393314335165060157554355 27589971502747590236331533)
              ·
                refine ⟨10346239313530346338624325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27589971502747590236331533 10346239313530346338624325)
                ·
                  refine ⟨1939919871286939938492061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10346239313530346338624325 1939919871286939938492061)
                  ·
                    refine ⟨727469951732602476934523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939919871286939938492061 727469951732602476934523)
                    ·
                      rfl

theorem cell22_2125114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_2125114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125114 prefixEnd_2125114 := by exact prefixLift 2125114
  have htrace : WordTrace (prefixWord ++ tailWord_2125114) baseStart_2125114 baseEnd_2125114 := by
    simpa [prefixWord, tailWord_2125114, baseEnd_2125114] using wordTrace_append hprefix tailTrace_2125114
  have hstable : (prefixWord ++ tailWord_2125114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125114).length < 2 ^ (prefixWord ++ tailWord_2125114).sum := by decide
  have hdescent : baseEnd_2125114 < baseStart_2125114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125127 : List Nat := [1, 1, 4, 1, 2, 3, 1, 9]
def baseStart_2125127 : Nat := 118140960795 + 2125127 * 2 ^ 59
def prefixEnd_2125127 : Nat := 4983230072969 + 3 ^ 40 * 2125127 * 2
def baseEnd_2125127 : Nat := 80830489099808308484387

theorem tailTrace_2125127 : CollatzResearch.WordTrace tailWord_2125127 prefixEnd_2125127 80830489099808308484387 := by
  unfold tailWord_2125127
  simp only [CollatzResearch.WordTrace]
  refine ⟨77509749372035296641357635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51673166248023531094238423 77509749372035296641357635)
  ·
    refine ⟨116264624058052944962036453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77509749372035296641357635 116264624058052944962036453)
    ·
      refine ⟨21799617010884927180381835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116264624058052944962036453 21799617010884927180381835)
      ·
        refine ⟨32699425516327390770572753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21799617010884927180381835 32699425516327390770572753)
        ·
          refine ⟨24524569137245543077929565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32699425516327390770572753 24524569137245543077929565)
          ·
            refine ⟨9196713426467078654223587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24524569137245543077929565 9196713426467078654223587)
            ·
              refine ⟨13795070139700617981335381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9196713426467078654223587 13795070139700617981335381)
              ·
                refine ⟨80830489099808308484387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13795070139700617981335381 80830489099808308484387)
                ·
                  rfl

theorem cell22_2125127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 9].length) (baseStart_2125127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125127 prefixEnd_2125127 := by exact prefixLift 2125127
  have htrace : WordTrace (prefixWord ++ tailWord_2125127) baseStart_2125127 baseEnd_2125127 := by
    simpa [prefixWord, tailWord_2125127, baseEnd_2125127] using wordTrace_append hprefix tailTrace_2125127
  have hstable : (prefixWord ++ tailWord_2125127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125127).length < 2 ^ (prefixWord ++ tailWord_2125127).sum := by decide
  have hdescent : baseEnd_2125127 < baseStart_2125127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125189 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 5]
def baseStart_2125189 : Nat := 118140960795 + 2125189 * 2 ^ 59
def prefixEnd_2125189 : Nat := 4983230072969 + 3 ^ 40 * 2125189 * 2
def baseEnd_2125189 : Nat := 242498541921775760436431

theorem tailTrace_2125189 : CollatzResearch.WordTrace tailWord_2125189 prefixEnd_2125189 242498541921775760436431 := by
  unfold tailWord_2125189
  simp only [CollatzResearch.WordTrace]
  refine ⟨77512010697810681230114621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51674673798540454153409747 77512010697810681230114621)
  ·
    refine ⟨29067004011679005461292983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77512010697810681230114621 29067004011679005461292983)
    ·
      refine ⟨43600506017518508191939475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29067004011679005461292983 43600506017518508191939475)
      ·
        refine ⟨65400759026277762287909213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43600506017518508191939475 65400759026277762287909213)
        ·
          refine ⟨24525284634854160857965955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65400759026277762287909213 24525284634854160857965955)
          ·
            refine ⟨36787926952281241286948933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24525284634854160857965955 36787926952281241286948933)
            ·
              refine ⟨6897736303552732741302925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36787926952281241286948933 6897736303552732741302925)
              ·
                refine ⟨2586651113832274777988597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6897736303552732741302925 2586651113832274777988597)
                ·
                  refine ⟨242498541921775760436431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586651113832274777988597 242498541921775760436431)
                  ·
                    rfl

theorem cell22_2125189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_2125189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125189 prefixEnd_2125189 := by exact prefixLift 2125189
  have htrace : WordTrace (prefixWord ++ tailWord_2125189) baseStart_2125189 baseEnd_2125189 := by
    simpa [prefixWord, tailWord_2125189, baseEnd_2125189] using wordTrace_append hprefix tailTrace_2125189
  have hstable : (prefixWord ++ tailWord_2125189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125189).length < 2 ^ (prefixWord ++ tailWord_2125189).sum := by decide
  have hdescent : baseEnd_2125189 < baseStart_2125189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125281 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2125281 : Nat := 118140960795 + 2125281 * 2 ^ 59
def prefixEnd_2125281 : Nat := 4983230072969 + 3 ^ 40 * 2125281 * 2
def baseEnd_2125281 : Nat := 727527119245469708009011

theorem tailTrace_2125281 : CollatzResearch.WordTrace tailWord_2125281 prefixEnd_2125281 727527119245469708009011 := by
  unfold tailWord_2125281
  simp only [CollatzResearch.WordTrace]
  refine ⟨77515366213477380942463697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51676910808984920628309131 77515366213477380942463697)
  ·
    refine ⟨58136524660108035706847773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77515366213477380942463697 58136524660108035706847773)
    ·
      refine ⟨21801196747540513390067915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58136524660108035706847773 21801196747540513390067915)
      ·
        refine ⟨32701795121310770085101873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21801196747540513390067915 32701795121310770085101873)
        ·
          refine ⟨24526346340983077563826405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32701795121310770085101873 24526346340983077563826405)
          ·
            refine ⟨4598689938934327043217451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24526346340983077563826405 4598689938934327043217451)
            ·
              refine ⟨6898034908401490564826177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598689938934327043217451 6898034908401490564826177)
              ·
                refine ⟨5173526181301117923619633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6898034908401490564826177 5173526181301117923619633)
                ·
                  refine ⟨3880144635975838442714725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5173526181301117923619633 3880144635975838442714725)
                  ·
                    refine ⟨727527119245469708009011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3880144635975838442714725 727527119245469708009011)
                    ·
                      rfl

theorem cell22_2125281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2125281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125281 prefixEnd_2125281 := by exact prefixLift 2125281
  have htrace : WordTrace (prefixWord ++ tailWord_2125281) baseStart_2125281 baseEnd_2125281 := by
    simpa [prefixWord, tailWord_2125281, baseEnd_2125281] using wordTrace_append hprefix tailTrace_2125281
  have hstable : (prefixWord ++ tailWord_2125281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125281).length < 2 ^ (prefixWord ++ tailWord_2125281).sum := by decide
  have hdescent : baseEnd_2125281 < baseStart_2125281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125285 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 4]
def baseStart_2125285 : Nat := 118140960795 + 2125285 * 2 ^ 59
def prefixEnd_2125285 : Nat := 4983230072969 + 3 ^ 40 * 2125285 * 2
def baseEnd_2125285 : Nat := 242509496175738343636333

theorem tailTrace_2125285 : CollatzResearch.WordTrace tailWord_2125285 prefixEnd_2125285 242509496175738343636333 := by
  unfold tailWord_2125285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77515512105462889625609309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51677008070308593083739539 77515512105462889625609309)
  ·
    refine ⟨29068317039548583609603491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77515512105462889625609309 29068317039548583609603491)
    ·
      refine ⟨43602475559322875414405237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29068317039548583609603491 43602475559322875414405237)
      ·
        refine ⟨4087732083686519570100491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43602475559322875414405237 4087732083686519570100491)
        ·
          refine ⟨6131598125529779355150737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087732083686519570100491 6131598125529779355150737)
          ·
            refine ⟨4598698594147334516363053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6131598125529779355150737 4598698594147334516363053)
            ·
              refine ⟨1724511972805250443636145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4598698594147334516363053 1724511972805250443636145)
              ·
                refine ⟨1293383979603937832727109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724511972805250443636145 1293383979603937832727109)
                ·
                  refine ⟨242509496175738343636333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293383979603937832727109 242509496175738343636333)
                  ·
                    rfl

theorem cell22_2125285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_2125285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125285 prefixEnd_2125285 := by exact prefixLift 2125285
  have htrace : WordTrace (prefixWord ++ tailWord_2125285) baseStart_2125285 baseEnd_2125285 := by
    simpa [prefixWord, tailWord_2125285, baseEnd_2125285] using wordTrace_append hprefix tailTrace_2125285
  have hstable : (prefixWord ++ tailWord_2125285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125285).length < 2 ^ (prefixWord ++ tailWord_2125285).sum := by decide
  have hdescent : baseEnd_2125285 < baseStart_2125285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125345 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 1, 3]
def baseStart_2125345 : Nat := 118140960795 + 2125345 * 2 ^ 59
def prefixEnd_2125345 : Nat := 4983230072969 + 3 ^ 40 * 2125345 * 2
def baseEnd_2125345 : Nat := 727549027753394874408815

theorem tailTrace_2125345 : CollatzResearch.WordTrace tailWord_2125345 prefixEnd_2125345 727549027753394874408815 := by
  unfold tailWord_2125345
  simp only [CollatzResearch.WordTrace]
  refine ⟨77517700485245519872793489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51678466990163679915195659 77517700485245519872793489)
  ·
    refine ⟨58138275363934139904595117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77517700485245519872793489 58138275363934139904595117)
    ·
      refine ⟨21801853261475302464223169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58138275363934139904595117 21801853261475302464223169)
      ·
        refine ⟨16351389946106476848167377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21801853261475302464223169 16351389946106476848167377)
        ·
          refine ⟨12263542459579857636125533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16351389946106476848167377 12263542459579857636125533)
          ·
            refine ⟨4598828422342446613547075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12263542459579857636125533 4598828422342446613547075)
            ·
              refine ⟨6898242633513669920320613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598828422342446613547075 6898242633513669920320613)
              ·
                refine ⟨1293420493783813110060115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6898242633513669920320613 1293420493783813110060115)
                ·
                  refine ⟨1940130740675719665090173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293420493783813110060115 1940130740675719665090173)
                  ·
                    refine ⟨727549027753394874408815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940130740675719665090173 727549027753394874408815)
                    ·
                      rfl

theorem cell22_2125345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_2125345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125345 prefixEnd_2125345 := by exact prefixLift 2125345
  have htrace : WordTrace (prefixWord ++ tailWord_2125345) baseStart_2125345 baseEnd_2125345 := by
    simpa [prefixWord, tailWord_2125345, baseEnd_2125345] using wordTrace_append hprefix tailTrace_2125345
  have hstable : (prefixWord ++ tailWord_2125345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125345).length < 2 ^ (prefixWord ++ tailWord_2125345).sum := by decide
  have hdescent : baseEnd_2125345 < baseStart_2125345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125358 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_2125358 : Nat := 118140960795 + 2125358 * 2 ^ 59
def prefixEnd_2125358 : Nat := 4983230072969 + 3 ^ 40 * 2125358 * 2
def baseEnd_2125358 : Nat := 242517825973022391277925

theorem tailTrace_2125358 : CollatzResearch.WordTrace tailWord_2125358 prefixEnd_2125358 242517825973022391277925 := by
  unfold tailWord_2125358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689771829274802886627091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51678783089465615395344485 9689771829274802886627091)
  ·
    refine ⟨14534657743912204329940637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9689771829274802886627091 14534657743912204329940637)
    ·
      refine ⟨5450496653967076623727739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14534657743912204329940637 5450496653967076623727739)
      ·
        refine ⟨8175744980950614935591609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450496653967076623727739 8175744980950614935591609)
        ·
          refine ⟨6131808735712961201693707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8175744980950614935591609 6131808735712961201693707)
          ·
            refine ⟨9197713103569441802540561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6131808735712961201693707 9197713103569441802540561)
            ·
              refine ⟨6898284827677081351905421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9197713103569441802540561 6898284827677081351905421)
              ·
                refine ⟨2586856810378905506964533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6898284827677081351905421 2586856810378905506964533)
                ·
                  refine ⟨242517825973022391277925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586856810378905506964533 242517825973022391277925)
                  ·
                    rfl

theorem cell22_2125358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_2125358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125358 prefixEnd_2125358 := by exact prefixLift 2125358
  have htrace : WordTrace (prefixWord ++ tailWord_2125358) baseStart_2125358 baseEnd_2125358 := by
    simpa [prefixWord, tailWord_2125358, baseEnd_2125358] using wordTrace_append hprefix tailTrace_2125358
  have hstable : (prefixWord ++ tailWord_2125358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125358).length < 2 ^ (prefixWord ++ tailWord_2125358).sum := by decide
  have hdescent : baseEnd_2125358 < baseStart_2125358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125388 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_2125388 : Nat := 118140960795 + 2125388 * 2 ^ 59
def prefixEnd_2125388 : Nat := 4983230072969 + 3 ^ 40 * 2125388 * 2
def baseEnd_2125388 : Nat := 727563747532157095583683

theorem tailTrace_2125388 : CollatzResearch.WordTrace tailWord_2125388 prefixEnd_2125388 727563747532157095583683 := by
  unfold tailWord_2125388
  simp only [CollatzResearch.WordTrace]
  refine ⟨38759634412044869108304409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51679512549393158811072545 38759634412044869108304409)
  ·
    refine ⟨29069725809033651831228307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38759634412044869108304409 29069725809033651831228307)
    ·
      refine ⟨43604588713550477746842461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29069725809033651831228307 43604588713550477746842461)
      ·
        refine ⟨16351720767581429155065923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43604588713550477746842461 16351720767581429155065923)
        ·
          refine ⟨24527581151372143732598885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16351720767581429155065923 24527581151372143732598885)
          ·
            refine ⟨4598921465882276949862291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24527581151372143732598885 4598921465882276949862291)
            ·
              refine ⟨6898382198823415424793437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598921465882276949862291 6898382198823415424793437)
              ·
                refine ⟨2586893324558780784297539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6898382198823415424793437 2586893324558780784297539)
                ·
                  refine ⟨3880339986838171176446309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586893324558780784297539 3880339986838171176446309)
                  ·
                    refine ⟨727563747532157095583683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3880339986838171176446309 727563747532157095583683)
                    ·
                      rfl

theorem cell22_2125388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_2125388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125388 prefixEnd_2125388 := by exact prefixLift 2125388
  have htrace : WordTrace (prefixWord ++ tailWord_2125388) baseStart_2125388 baseEnd_2125388 := by
    simpa [prefixWord, tailWord_2125388, baseEnd_2125388] using wordTrace_append hprefix tailTrace_2125388
  have hstable : (prefixWord ++ tailWord_2125388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125388).length < 2 ^ (prefixWord ++ tailWord_2125388).sum := by decide
  have hdescent : baseEnd_2125388 < baseStart_2125388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125418 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2125418 : Nat := 118140960795 + 2125418 * 2 ^ 59
def prefixEnd_2125418 : Nat := 4983230072969 + 3 ^ 40 * 2125418 * 2
def baseEnd_2125418 : Nat := 727574017145247017333591

theorem tailTrace_2125418 : CollatzResearch.WordTrace tailWord_2125418 prefixEnd_2125418 727574017145247017333591 := by
  unfold tailWord_2125418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19380090753495263335050227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51680242009320702226800605 19380090753495263335050227)
  ·
    refine ⟨29070136130242895002575341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19380090753495263335050227 29070136130242895002575341)
    ·
      refine ⟨10901301048841085625965753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29070136130242895002575341 10901301048841085625965753)
      ·
        refine ⟨8175975786630814219474315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10901301048841085625965753 8175975786630814219474315)
        ·
          refine ⟨12263963679946221329211473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8175975786630814219474315 12263963679946221329211473)
          ·
            refine ⟨9197972759959665996908605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12263963679946221329211473 9197972759959665996908605)
            ·
              refine ⟨3449239784984874748840727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9197972759959665996908605 3449239784984874748840727)
              ·
                refine ⟨5173859677477312123261091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449239784984874748840727 5173859677477312123261091)
                ·
                  refine ⟨7760789516215968184891637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5173859677477312123261091 7760789516215968184891637)
                  ·
                    refine ⟨727574017145247017333591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7760789516215968184891637 727574017145247017333591)
                    ·
                      rfl

theorem cell22_2125418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2125418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125418 prefixEnd_2125418 := by exact prefixLift 2125418
  have htrace : WordTrace (prefixWord ++ tailWord_2125418) baseStart_2125418 baseEnd_2125418 := by
    simpa [prefixWord, tailWord_2125418, baseEnd_2125418] using wordTrace_append hprefix tailTrace_2125418
  have hstable : (prefixWord ++ tailWord_2125418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125418).length < 2 ^ (prefixWord ++ tailWord_2125418).sum := by decide
  have hdescent : baseEnd_2125418 < baseStart_2125418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125508 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2125508 : Nat := 118140960795 + 2125508 * 2 ^ 59
def prefixEnd_2125508 : Nat := 4983230072969 + 3 ^ 40 * 2125508 * 2
def baseEnd_2125508 : Nat := 727604825984516782583315

theorem tailTrace_2125508 : CollatzResearch.WordTrace tailWord_2125508 prefixEnd_2125508 727604825984516782583315 := by
  unfold tailWord_2125508
  simp only [CollatzResearch.WordTrace]
  refine ⟨38761822791827499355488589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51682430389103332473984785 38761822791827499355488589)
  ·
    refine ⟨14535683546935312258308221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38761822791827499355488589 14535683546935312258308221)
    ·
      refine ⟨5450881330100742096865583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14535683546935312258308221 5450881330100742096865583)
      ·
        refine ⟨8176321995151113145298375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450881330100742096865583 8176321995151113145298375)
        ·
          refine ⟨12264482992726669717947563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8176321995151113145298375 12264482992726669717947563)
          ·
            refine ⟨18396724489090004576921345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12264482992726669717947563 18396724489090004576921345)
            ·
              refine ⟨13797543366817503432691009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18396724489090004576921345 13797543366817503432691009)
              ·
                refine ⟨10348157525113127574518257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13797543366817503432691009 10348157525113127574518257)
                ·
                  refine ⟨7761118143834845680888693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10348157525113127574518257 7761118143834845680888693)
                  ·
                    refine ⟨727604825984516782583315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7761118143834845680888693 727604825984516782583315)
                    ·
                      rfl

theorem cell22_2125508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2125508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125508 prefixEnd_2125508 := by exact prefixLift 2125508
  have htrace : WordTrace (prefixWord ++ tailWord_2125508) baseStart_2125508 baseEnd_2125508 := by
    simpa [prefixWord, tailWord_2125508, baseEnd_2125508] using wordTrace_append hprefix tailTrace_2125508
  have hstable : (prefixWord ++ tailWord_2125508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125508).length < 2 ^ (prefixWord ++ tailWord_2125508).sum := by decide
  have hdescent : baseEnd_2125508 < baseStart_2125508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125553 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2125553 : Nat := 118140960795 + 2125553 * 2 ^ 59
def prefixEnd_2125553 : Nat := 4983230072969 + 3 ^ 40 * 2125553 * 2
def baseEnd_2125553 : Nat := 727620230404151665208177

theorem tailTrace_2125553 : CollatzResearch.WordTrace tailWord_2125553 prefixEnd_2125553 727620230404151665208177 := by
  unfold tailWord_2125553
  simp only [CollatzResearch.WordTrace]
  refine ⟨77525286868491971396365313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51683524578994647597576875 77525286868491971396365313)
  ·
    refine ⟨58143965151368978547273985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77525286868491971396365313 58143965151368978547273985)
    ·
      refine ⟨43607973863526733910455489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58143965151368978547273985 43607973863526733910455489)
      ·
        refine ⟨32705980397645050432841617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43607973863526733910455489 32705980397645050432841617)
        ·
          refine ⟨24529485298233787824631213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32705980397645050432841617 24529485298233787824631213)
          ·
            refine ⟨9198556986837670434236705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24529485298233787824631213 9198556986837670434236705)
            ·
              refine ⟨6898917740128252825677529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9198556986837670434236705 6898917740128252825677529)
              ·
                refine ⟨5174188305096189619258147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6898917740128252825677529 5174188305096189619258147)
                ·
                  refine ⟨7761282457644284428887221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174188305096189619258147 7761282457644284428887221)
                  ·
                    refine ⟨727620230404151665208177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7761282457644284428887221 727620230404151665208177)
                    ·
                      rfl

theorem cell22_2125553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2125553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125553 prefixEnd_2125553 := by exact prefixLift 2125553
  have htrace : WordTrace (prefixWord ++ tailWord_2125553) baseStart_2125553 baseEnd_2125553 := by
    simpa [prefixWord, tailWord_2125553, baseEnd_2125553] using wordTrace_append hprefix tailTrace_2125553
  have hstable : (prefixWord ++ tailWord_2125553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125553).length < 2 ^ (prefixWord ++ tailWord_2125553).sum := by decide
  have hdescent : baseEnd_2125553 < baseStart_2125553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125628 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_2125628 : Nat := 118140960795 + 2125628 * 2 ^ 59
def prefixEnd_2125628 : Nat := 4983230072969 + 3 ^ 40 * 2125628 * 2
def baseEnd_2125628 : Nat := 242548634812292156527649

theorem tailTrace_2125628 : CollatzResearch.WordTrace tailWord_2125628 prefixEnd_2125628 242548634812292156527649 := by
  unfold tailWord_2125628
  simp only [CollatzResearch.WordTrace]
  refine ⟨38764011171610129602672769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51685348228813506136897025 38764011171610129602672769)
  ·
    refine ⟨29073008378707597202004577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38764011171610129602672769 29073008378707597202004577)
    ·
      refine ⟨21804756284030697901503433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29073008378707597202004577 21804756284030697901503433)
      ·
        refine ⟨16353567213023023426127575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21804756284030697901503433 16353567213023023426127575)
        ·
          refine ⟨24530350819534535139191363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16353567213023023426127575 24530350819534535139191363)
          ·
            refine ⟨36795526229301802708787045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24530350819534535139191363 36795526229301802708787045)
            ·
              refine ⟨6899161167994088007897571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36795526229301802708787045 6899161167994088007897571)
              ·
                refine ⟨10348741751991132011846357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6899161167994088007897571 10348741751991132011846357)
                ·
                  refine ⟨242548634812292156527649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10348741751991132011846357 242548634812292156527649)
                  ·
                    rfl

theorem cell22_2125628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_2125628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125628 prefixEnd_2125628 := by exact prefixLift 2125628
  have htrace : WordTrace (prefixWord ++ tailWord_2125628) baseStart_2125628 baseEnd_2125628 := by
    simpa [prefixWord, tailWord_2125628, baseEnd_2125628] using wordTrace_append hprefix tailTrace_2125628
  have hstable : (prefixWord ++ tailWord_2125628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125628).length < 2 ^ (prefixWord ++ tailWord_2125628).sum := by decide
  have hdescent : baseEnd_2125628 < baseStart_2125628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125638 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2125638 : Nat := 118140960795 + 2125638 * 2 ^ 59
def prefixEnd_2125638 : Nat := 4983230072969 + 3 ^ 40 * 2125638 * 2
def baseEnd_2125638 : Nat := 727649327641239776832917

theorem tailTrace_2125638 : CollatzResearch.WordTrace tailWord_2125638 prefixEnd_2125638 727649327641239776832917 := by
  unfold tailWord_2125638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422762096037000966037799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51685591382122687275473045 2422762096037000966037799)
  ·
    refine ⟨3634143144055501449056699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2422762096037000966037799 3634143144055501449056699)
    ·
      refine ⟨5451214716083252173585049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634143144055501449056699 5451214716083252173585049)
      ·
        refine ⟨4088411037062439130188787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5451214716083252173585049 4088411037062439130188787)
        ·
          refine ⟨6132616555593658695283181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088411037062439130188787 6132616555593658695283181)
          ·
            refine ⟨2299731208347622010731193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6132616555593658695283181 2299731208347622010731193)
            ·
              refine ⟨1724798406260716508048395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299731208347622010731193 1724798406260716508048395)
              ·
                refine ⟨2587197609391074762072593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724798406260716508048395 2587197609391074762072593)
                ·
                  refine ⟨1940398207043306071554445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2587197609391074762072593 1940398207043306071554445)
                  ·
                    refine ⟨727649327641239776832917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940398207043306071554445 727649327641239776832917)
                    ·
                      rfl

theorem cell22_2125638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2125638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125638 prefixEnd_2125638 := by exact prefixLift 2125638
  have htrace : WordTrace (prefixWord ++ tailWord_2125638) baseStart_2125638 baseEnd_2125638 := by
    simpa [prefixWord, tailWord_2125638, baseEnd_2125638] using wordTrace_append hprefix tailTrace_2125638
  have hstable : (prefixWord ++ tailWord_2125638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125638).length < 2 ^ (prefixWord ++ tailWord_2125638).sum := by decide
  have hdescent : baseEnd_2125638 < baseStart_2125638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125705 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_2125705 : Nat := 118140960795 + 2125705 * 2 ^ 59
def prefixEnd_2125705 : Nat := 4983230072969 + 3 ^ 40 * 2125705 * 2
def baseEnd_2125705 : Nat := 727672263110473935407711

theorem tailTrace_2125705 : CollatzResearch.WordTrace tailWord_2125705 prefixEnd_2125705 727672263110473935407711 := by
  unfold tailWord_2125705
  simp only [CollatzResearch.WordTrace]
  refine ⟨77530830763941301355898569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51687220509294200903932379 77530830763941301355898569)
  ·
    refine ⟨58148123072955976016923927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77530830763941301355898569 58148123072955976016923927)
    ·
      refine ⟨87222184609433964025385891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58148123072955976016923927 87222184609433964025385891)
      ·
        refine ⟨130833276914150946038078837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87222184609433964025385891 130833276914150946038078837)
        ·
          refine ⟨12265619710701651191069891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130833276914150946038078837 12265619710701651191069891)
          ·
            refine ⟨18398429566052476786604837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12265619710701651191069891 18398429566052476786604837)
            ·
              refine ⟨3449705543634839397488407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18398429566052476786604837 3449705543634839397488407)
              ·
                refine ⟨5174558315452259096232611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449705543634839397488407 5174558315452259096232611)
                ·
                  refine ⟨7761837473178388644348917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174558315452259096232611 7761837473178388644348917)
                  ·
                    refine ⟨727672263110473935407711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7761837473178388644348917 727672263110473935407711)
                    ·
                      rfl

theorem cell22_2125705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_2125705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125705 prefixEnd_2125705 := by exact prefixLift 2125705
  have htrace : WordTrace (prefixWord ++ tailWord_2125705) baseStart_2125705 baseEnd_2125705 := by
    simpa [prefixWord, tailWord_2125705, baseEnd_2125705] using wordTrace_append hprefix tailTrace_2125705
  have hstable : (prefixWord ++ tailWord_2125705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125705).length < 2 ^ (prefixWord ++ tailWord_2125705).sum := by decide
  have hdescent : baseEnd_2125705 < baseStart_2125705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125724 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 4]
def baseStart_2125724 : Nat := 118140960795 + 2125724 * 2 ^ 59
def prefixEnd_2125724 : Nat := 4983230072969 + 3 ^ 40 * 2125724 * 2
def baseEnd_2125724 : Nat := 242559589066254739727551

theorem tailTrace_2125724 : CollatzResearch.WordTrace tailWord_2125724 prefixEnd_2125724 242559589066254739727551 := by
  unfold tailWord_2125724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38765761875436233800420113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51687682500581645067226817 38765761875436233800420113)
  ·
    refine ⟨29074321406577175350315085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38765761875436233800420113 29074321406577175350315085)
    ·
      refine ⟨10902870527466440756368157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29074321406577175350315085 10902870527466440756368157)
      ·
        refine ⟨4088576447799915283638059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10902870527466440756368157 4088576447799915283638059)
        ·
          refine ⟨6132864671699872925457089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088576447799915283638059 6132864671699872925457089)
          ·
            refine ⟨4599648503774904694092817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6132864671699872925457089 4599648503774904694092817)
            ·
              refine ⟨3449736377831178520569613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599648503774904694092817 3449736377831178520569613)
              ·
                refine ⟨1293651141686691945213605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3449736377831178520569613 1293651141686691945213605)
                ·
                  refine ⟨242559589066254739727551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293651141686691945213605 242559589066254739727551)
                  ·
                    rfl

theorem cell22_2125724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_2125724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125724 prefixEnd_2125724 := by exact prefixLift 2125724
  have htrace : WordTrace (prefixWord ++ tailWord_2125724) baseStart_2125724 baseEnd_2125724 := by
    simpa [prefixWord, tailWord_2125724, baseEnd_2125724] using wordTrace_append hprefix tailTrace_2125724
  have hstable : (prefixWord ++ tailWord_2125724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125724).length < 2 ^ (prefixWord ++ tailWord_2125724).sum := by decide
  have hdescent : baseEnd_2125724 < baseStart_2125724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125726 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2125726 : Nat := 118140960795 + 2125726 * 2 ^ 59
def prefixEnd_2125726 : Nat := 4983230072969 + 3 ^ 40 * 2125726 * 2
def baseEnd_2125726 : Nat := 727679451839636880632647

theorem tailTrace_2125726 : CollatzResearch.WordTrace tailWord_2125726 prefixEnd_2125726 727679451839636880632647 := by
  unfold tailWord_2125726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691449587108152742801629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51687731131243481294942021 9691449587108152742801629)
  ·
    refine ⟨3634293595165557278550611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9691449587108152742801629 3634293595165557278550611)
    ·
      refine ⟨5451440392748335917825917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634293595165557278550611 5451440392748335917825917)
      ·
        refine ⟨2044290147280625969184719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5451440392748335917825917 2044290147280625969184719)
        ·
          refine ⟨3066435220920938953777079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044290147280625969184719 3066435220920938953777079)
          ·
            refine ⟨4599652831381408430665619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066435220920938953777079 4599652831381408430665619)
            ·
              refine ⟨6899479247072112645998429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4599652831381408430665619 6899479247072112645998429)
              ·
                refine ⟨2587304717652042242249411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6899479247072112645998429 2587304717652042242249411)
                ·
                  refine ⟨3880957076478063363374117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587304717652042242249411 3880957076478063363374117)
                  ·
                    refine ⟨727679451839636880632647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3880957076478063363374117 727679451839636880632647)
                    ·
                      rfl

theorem cell22_2125726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2125726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125726 prefixEnd_2125726 := by exact prefixLift 2125726
  have htrace : WordTrace (prefixWord ++ tailWord_2125726) baseStart_2125726 baseEnd_2125726 := by
    simpa [prefixWord, tailWord_2125726, baseEnd_2125726] using wordTrace_append hprefix tailTrace_2125726
  have hstable : (prefixWord ++ tailWord_2125726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125726).length < 2 ^ (prefixWord ++ tailWord_2125726).sum := by decide
  have hdescent : baseEnd_2125726 < baseStart_2125726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125733 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_2125733 : Nat := 118140960795 + 2125733 * 2 ^ 59
def prefixEnd_2125733 : Nat := 4983230072969 + 3 ^ 40 * 2125733 * 2
def baseEnd_2125733 : Nat := 727681848082691195707625

theorem tailTrace_2125733 : CollatzResearch.WordTrace tailWord_2125733 prefixEnd_2125733 727681848082691195707625 := by
  unfold tailWord_2125733
  simp only [CollatzResearch.WordTrace]
  refine ⟨77531852007839862137917853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51687901338559908091945235 77531852007839862137917853)
  ·
    refine ⟨29074444502939948301719195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77531852007839862137917853 29074444502939948301719195)
    ·
      refine ⟨43611666754409922452578793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29074444502939948301719195 43611666754409922452578793)
      ·
        refine ⟨32708750065807441839434095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43611666754409922452578793 32708750065807441839434095)
        ·
          refine ⟨49063125098711162759151143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32708750065807441839434095 49063125098711162759151143)
          ·
            refine ⟨73594687648066744138726715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49063125098711162759151143 73594687648066744138726715)
            ·
              refine ⟨110392031472100116208090073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73594687648066744138726715 110392031472100116208090073)
              ·
                refine ⟨82794023604075087156067555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110392031472100116208090073 82794023604075087156067555)
                ·
                  refine ⟨124191035406112630734101333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82794023604075087156067555 124191035406112630734101333)
                  ·
                    refine ⟨727681848082691195707625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 124191035406112630734101333 727681848082691195707625)
                    ·
                      rfl

theorem cell22_2125733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_2125733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125733 prefixEnd_2125733 := by exact prefixLift 2125733
  have htrace : WordTrace (prefixWord ++ tailWord_2125733) baseStart_2125733 baseEnd_2125733 := by
    simpa [prefixWord, tailWord_2125733, baseEnd_2125733] using wordTrace_append hprefix tailTrace_2125733
  have hstable : (prefixWord ++ tailWord_2125733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125733).length < 2 ^ (prefixWord ++ tailWord_2125733).sum := by decide
  have hdescent : baseEnd_2125733 < baseStart_2125733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125735 : List Nat := [1, 1, 6, 1, 2, 2, 9]
def baseStart_2125735 : Nat := 118140960795 + 2125735 * 2 ^ 59
def prefixEnd_2125735 : Nat := 4983230072969 + 3 ^ 40 * 2125735 * 2
def baseEnd_2125735 : Nat := 26951204915687550265097

theorem tailTrace_2125735 : CollatzResearch.WordTrace tailWord_2125735 prefixEnd_2125735 26951204915687550265097 := by
  unfold tailWord_2125735
  simp only [CollatzResearch.WordTrace]
  refine ⟨77531924953832616479490659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51687949969221744319660439 77531924953832616479490659)
  ·
    refine ⟨116297887430748924719235989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77531924953832616479490659 116297887430748924719235989)
    ·
      refine ⟨5451463473316355846214187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 116297887430748924719235989 5451463473316355846214187)
      ·
        refine ⟨8177195209974533769321281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451463473316355846214187 8177195209974533769321281)
        ·
          refine ⟨6132896407480900326990961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8177195209974533769321281 6132896407480900326990961)
          ·
            refine ⟨4599672305610675245243221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6132896407480900326990961 4599672305610675245243221)
            ·
              refine ⟨26951204915687550265097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4599672305610675245243221 26951204915687550265097)
              ·
                rfl

theorem cell22_2125735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 9].length) (baseStart_2125735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125735 prefixEnd_2125735 := by exact prefixLift 2125735
  have htrace : WordTrace (prefixWord ++ tailWord_2125735) baseStart_2125735 baseEnd_2125735 := by
    simpa [prefixWord, tailWord_2125735, baseEnd_2125735] using wordTrace_append hprefix tailTrace_2125735
  have hstable : (prefixWord ++ tailWord_2125735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125735).length < 2 ^ (prefixWord ++ tailWord_2125735).sum := by decide
  have hdescent : baseEnd_2125735 < baseStart_2125735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125756 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_2125756 : Nat := 118140960795 + 2125756 * 2 ^ 59
def prefixEnd_2125756 : Nat := 4983230072969 + 3 ^ 40 * 2125756 * 2
def baseEnd_2125756 : Nat := 727689721452726802382555

theorem tailTrace_2125756 : CollatzResearch.WordTrace tailWord_2125756 prefixEnd_2125756 727689721452726802382555 := by
  unfold tailWord_2125756
  simp only [CollatzResearch.WordTrace]
  refine ⟨38766345443378268533002561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51688460591171024710670081 38766345443378268533002561)
  ·
    refine ⟨29074759082533701399751921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38766345443378268533002561 29074759082533701399751921)
    ·
      refine ⟨21806069311900276049813941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29074759082533701399751921 21806069311900276049813941)
      ·
        refine ⟨2044318997990650879670057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21806069311900276049813941 2044318997990650879670057)
        ·
          refine ⟨1533239248492988159752543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044318997990650879670057 1533239248492988159752543)
          ·
            refine ⟨2299858872739482239628815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533239248492988159752543 2299858872739482239628815)
            ·
              refine ⟨3449788309109223359443223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299858872739482239628815 3449788309109223359443223)
              ·
                refine ⟨5174682463663835039164835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449788309109223359443223 5174682463663835039164835)
                ·
                  refine ⟨7762023695495752558747253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174682463663835039164835 7762023695495752558747253)
                  ·
                    refine ⟨727689721452726802382555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7762023695495752558747253 727689721452726802382555)
                    ·
                      rfl

theorem cell22_2125756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_2125756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125756 prefixEnd_2125756 := by exact prefixLift 2125756
  have htrace : WordTrace (prefixWord ++ tailWord_2125756) baseStart_2125756 baseEnd_2125756 := by
    simpa [prefixWord, tailWord_2125756, baseEnd_2125756] using wordTrace_append hprefix tailTrace_2125756
  have hstable : (prefixWord ++ tailWord_2125756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125756).length < 2 ^ (prefixWord ++ tailWord_2125756).sum := by decide
  have hdescent : baseEnd_2125756 < baseStart_2125756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125763 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 11]
def baseStart_2125763 : Nat := 118140960795 + 2125763 * 2 ^ 59
def prefixEnd_2125763 : Nat := 4983230072969 + 3 ^ 40 * 2125763 * 2
def baseEnd_2125763 : Nat := 242564039231927039152511

theorem tailTrace_2125763 : CollatzResearch.WordTrace tailWord_2125763 prefixEnd_2125763 242564039231927039152511 := by
  unfold tailWord_2125763
  simp only [CollatzResearch.WordTrace]
  refine ⟨77532946197731177261509943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51688630798487451507673295 77532946197731177261509943)
  ·
    refine ⟨116299419296596765892264915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77532946197731177261509943 116299419296596765892264915)
    ·
      refine ⟨174449128944895148838397373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116299419296596765892264915 174449128944895148838397373)
      ·
        refine ⟨65418423354335680814399015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174449128944895148838397373 65418423354335680814399015)
        ·
          refine ⟨98127635031503521221598523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65418423354335680814399015 98127635031503521221598523)
          ·
            refine ⟨147191452547255281832397785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98127635031503521221598523 147191452547255281832397785)
            ·
              refine ⟨110393589410441461374298339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147191452547255281832397785 110393589410441461374298339)
              ·
                refine ⟨165590384115662192061447509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110393589410441461374298339 165590384115662192061447509)
                ·
                  refine ⟨242564039231927039152511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 165590384115662192061447509 242564039231927039152511)
                  ·
                    rfl

theorem cell22_2125763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_2125763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125763 prefixEnd_2125763 := by exact prefixLift 2125763
  have htrace : WordTrace (prefixWord ++ tailWord_2125763) baseStart_2125763 baseEnd_2125763 := by
    simpa [prefixWord, tailWord_2125763, baseEnd_2125763] using wordTrace_append hprefix tailTrace_2125763
  have hstable : (prefixWord ++ tailWord_2125763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125763).length < 2 ^ (prefixWord ++ tailWord_2125763).sum := by decide
  have hdescent : baseEnd_2125763 < baseStart_2125763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125780 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_2125780 : Nat := 118140960795 + 2125780 * 2 ^ 59
def prefixEnd_2125780 : Nat := 4983230072969 + 3 ^ 40 * 2125780 * 2
def baseEnd_2125780 : Nat := 242565979047732913260827

theorem tailTrace_2125780 : CollatzResearch.WordTrace tailWord_2125780 prefixEnd_2125780 242565979047732913260827 := by
  unfold tailWord_2125780
  simp only [CollatzResearch.WordTrace]
  refine ⟨38766783119334794582439397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51689044159113059443252529 38766783119334794582439397)
  ·
    refine ⟨7268771834875273984207387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38766783119334794582439397 7268771834875273984207387)
    ·
      refine ⟨10903157752312910976311081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7268771834875273984207387 10903157752312910976311081)
      ·
        refine ⟨8177368314234683232233311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10903157752312910976311081 8177368314234683232233311)
        ·
          refine ⟨12266052471352024848349967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8177368314234683232233311 12266052471352024848349967)
          ·
            refine ⟨18399078707028037272524951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12266052471352024848349967 18399078707028037272524951)
            ·
              refine ⟨27598618060542055908787427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18399078707028037272524951 27598618060542055908787427)
              ·
                refine ⟨41397927090813083863181141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27598618060542055908787427 41397927090813083863181141)
                ·
                  refine ⟨242565979047732913260827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41397927090813083863181141 242565979047732913260827)
                  ·
                    rfl

theorem cell22_2125780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_2125780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125780 prefixEnd_2125780 := by exact prefixLift 2125780
  have htrace : WordTrace (prefixWord ++ tailWord_2125780) baseStart_2125780 baseEnd_2125780 := by
    simpa [prefixWord, tailWord_2125780, baseEnd_2125780] using wordTrace_append hprefix tailTrace_2125780
  have hstable : (prefixWord ++ tailWord_2125780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125780).length < 2 ^ (prefixWord ++ tailWord_2125780).sum := by decide
  have hdescent : baseEnd_2125780 < baseStart_2125780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125814 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_2125814 : Nat := 118140960795 + 2125814 * 2 ^ 59
def prefixEnd_2125814 : Nat := 4983230072969 + 3 ^ 40 * 2125814 * 2
def baseEnd_2125814 : Nat := 242569858679344661477459

theorem tailTrace_2125814 : CollatzResearch.WordTrace tailWord_2125814 prefixEnd_2125814 242569858679344661477459 := by
  unfold tailWord_2125814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845925395034150810726031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51689870880364275314410997 4845925395034150810726031)
  ·
    refine ⟨7268888092551226216089047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4845925395034150810726031 7268888092551226216089047)
    ·
      refine ⟨10903332138826839324133571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7268888092551226216089047 10903332138826839324133571)
      ·
        refine ⟨16354998208240258986200357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10903332138826839324133571 16354998208240258986200357)
        ·
          refine ⟨3066562164045048559912567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16354998208240258986200357 3066562164045048559912567)
          ·
            refine ⟨4599843246067572839868851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066562164045048559912567 4599843246067572839868851)
            ·
              refine ⟨6899764869101359259803277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4599843246067572839868851 6899764869101359259803277)
              ·
                refine ⟨2587411825913009722426229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6899764869101359259803277 2587411825913009722426229)
                ·
                  refine ⟨242569858679344661477459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2587411825913009722426229 242569858679344661477459)
                  ·
                    rfl

theorem cell22_2125814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_2125814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125814 prefixEnd_2125814 := by exact prefixLift 2125814
  have htrace : WordTrace (prefixWord ++ tailWord_2125814) baseStart_2125814 baseEnd_2125814 := by
    simpa [prefixWord, tailWord_2125814, baseEnd_2125814] using wordTrace_append hprefix tailTrace_2125814
  have hstable : (prefixWord ++ tailWord_2125814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125814).length < 2 ^ (prefixWord ++ tailWord_2125814).sum := by decide
  have hdescent : baseEnd_2125814 < baseStart_2125814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125825 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 8]
def baseStart_2125825 : Nat := 118140960795 + 2125825 * 2 ^ 59
def prefixEnd_2125825 : Nat := 4983230072969 + 3 ^ 40 * 2125825 * 2
def baseEnd_2125825 : Nat := 242571113854277874135781

theorem tailTrace_2125825 : CollatzResearch.WordTrace tailWord_2125825 prefixEnd_2125825 242571113854277874135781 := by
  unfold tailWord_2125825
  simp only [CollatzResearch.WordTrace]
  refine ⟨77535207523506561850266929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51690138349004374566844619 77535207523506561850266929)
  ·
    refine ⟨58151405642629921387700197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77535207523506561850266929 58151405642629921387700197)
    ·
      refine ⟨10903388557993110260193787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58151405642629921387700197 10903388557993110260193787)
      ·
        refine ⟨16355082836989665390290681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10903388557993110260193787 16355082836989665390290681)
        ·
          refine ⟨12266312127742249042718011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16355082836989665390290681 12266312127742249042718011)
          ·
            refine ⟨18399468191613373564077017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12266312127742249042718011 18399468191613373564077017)
            ·
              refine ⟨13799601143710030173057763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18399468191613373564077017 13799601143710030173057763)
              ·
                refine ⟨20699401715565045259586645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13799601143710030173057763 20699401715565045259586645)
                ·
                  refine ⟨242571113854277874135781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20699401715565045259586645 242571113854277874135781)
                  ·
                    rfl

theorem cell22_2125825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_2125825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125825 prefixEnd_2125825 := by exact prefixLift 2125825
  have htrace : WordTrace (prefixWord ++ tailWord_2125825) baseStart_2125825 baseEnd_2125825 := by
    simpa [prefixWord, tailWord_2125825, baseEnd_2125825] using wordTrace_append hprefix tailTrace_2125825
  have hstable : (prefixWord ++ tailWord_2125825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125825).length < 2 ^ (prefixWord ++ tailWord_2125825).sum := by decide
  have hdescent : baseEnd_2125825 < baseStart_2125825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125840 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_2125840 : Nat := 118140960795 + 2125840 * 2 ^ 59
def prefixEnd_2125840 : Nat := 4983230072969 + 3 ^ 40 * 2125840 * 2
def baseEnd_2125840 : Nat := 727718476369378583282297

theorem tailTrace_2125840 : CollatzResearch.WordTrace tailWord_2125840 prefixEnd_2125840 727718476369378583282297 := by
  unfold tailWord_2125840
  simp only [CollatzResearch.WordTrace]
  refine ⟨38767877309226109706031487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51690503078968146274708649 38767877309226109706031487)
  ·
    refine ⟨58151815963839164559047231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38767877309226109706031487 58151815963839164559047231)
    ·
      refine ⟨87227723945758746838570847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58151815963839164559047231 87227723945758746838570847)
      ·
        refine ⟨130841585918638120257856271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87227723945758746838570847 130841585918638120257856271)
        ·
          refine ⟨196262378877957180386784407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130841585918638120257856271 196262378877957180386784407)
          ·
            refine ⟨294393568316935770580176611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196262378877957180386784407 294393568316935770580176611)
            ·
              refine ⟨441590352475403655870264917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294393568316935770580176611 441590352475403655870264917)
              ·
                refine ⟨5174886943071136592229667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 441590352475403655870264917 5174886943071136592229667)
                ·
                  refine ⟨7762330414606704888344501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174886943071136592229667 7762330414606704888344501)
                  ·
                    refine ⟨727718476369378583282297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7762330414606704888344501 727718476369378583282297)
                    ·
                      rfl

theorem cell22_2125840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_2125840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125840 prefixEnd_2125840 := by exact prefixLift 2125840
  have htrace : WordTrace (prefixWord ++ tailWord_2125840) baseStart_2125840 baseEnd_2125840 := by
    simpa [prefixWord, tailWord_2125840, baseEnd_2125840] using wordTrace_append hprefix tailTrace_2125840
  have hstable : (prefixWord ++ tailWord_2125840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125840).length < 2 ^ (prefixWord ++ tailWord_2125840).sum := by decide
  have hdescent : baseEnd_2125840 < baseStart_2125840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125874 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_2125874 : Nat := 118140960795 + 2125874 * 2 ^ 59
def prefixEnd_2125874 : Nat := 4983230072969 + 3 ^ 40 * 2125874 * 2
def baseEnd_2125874 : Nat := 727730115264213827932193

theorem tailTrace_2125874 : CollatzResearch.WordTrace tailWord_2125874 prefixEnd_2125874 727730115264213827932193 := by
  unfold tailWord_2125874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19384248675082260804700169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51691329800219362145867117 19384248675082260804700169)
  ·
    refine ⟨14538186506311695603525127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19384248675082260804700169 14538186506311695603525127)
    ·
      refine ⟨21807279759467543405287691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14538186506311695603525127 21807279759467543405287691)
      ·
        refine ⟨32710919639201315107931537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21807279759467543405287691 32710919639201315107931537)
        ·
          refine ⟨24533189729400986330948653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32710919639201315107931537 24533189729400986330948653)
          ·
            refine ⟨9199946148525369874105745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24533189729400986330948653 9199946148525369874105745)
            ·
              refine ⟨6899959611394027405579309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9199946148525369874105745 6899959611394027405579309)
              ·
                refine ⟨2587484854272760277092241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6899959611394027405579309 2587484854272760277092241)
                ·
                  refine ⟨1940613640704570207819181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2587484854272760277092241 1940613640704570207819181)
                  ·
                    refine ⟨727730115264213827932193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940613640704570207819181 727730115264213827932193)
                    ·
                      rfl

theorem cell22_2125874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_2125874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125874 prefixEnd_2125874 := by exact prefixLift 2125874
  have htrace : WordTrace (prefixWord ++ tailWord_2125874) baseStart_2125874 baseEnd_2125874 := by
    simpa [prefixWord, tailWord_2125874, baseEnd_2125874] using wordTrace_append hprefix tailTrace_2125874
  have hstable : (prefixWord ++ tailWord_2125874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125874).length < 2 ^ (prefixWord ++ tailWord_2125874).sum := by decide
  have hdescent : baseEnd_2125874 < baseStart_2125874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125889 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2125889 : Nat := 118140960795 + 2125889 * 2 ^ 59
def prefixEnd_2125889 : Nat := 4983230072969 + 3 ^ 40 * 2125889 * 2
def baseEnd_2125889 : Nat := 727735250070758788807147

theorem tailTrace_2125889 : CollatzResearch.WordTrace tailWord_2125889 prefixEnd_2125889 727735250070758788807147 := by
  unfold tailWord_2125889
  simp only [CollatzResearch.WordTrace]
  refine ⟨77537541795274700780596721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51691694530183133853731147 77537541795274700780596721)
  ·
    refine ⟨58153156346456025585447541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77537541795274700780596721 58153156346456025585447541)
    ·
      refine ⟨5451858407480252398635707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58153156346456025585447541 5451858407480252398635707)
      ·
        refine ⟨8177787611220378597953561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451858407480252398635707 8177787611220378597953561)
        ·
          refine ⟨6133340708415283948465171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8177787611220378597953561 6133340708415283948465171)
          ·
            refine ⟨9200011062622925922697757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133340708415283948465171 9200011062622925922697757)
            ·
              refine ⟨3450004148483597221011659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9200011062622925922697757 3450004148483597221011659)
              ·
                refine ⟨5175006222725395831517489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450004148483597221011659 5175006222725395831517489)
                ·
                  refine ⟨3881254667044046873638117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5175006222725395831517489 3881254667044046873638117)
                  ·
                    refine ⟨727735250070758788807147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3881254667044046873638117 727735250070758788807147)
                    ·
                      rfl

theorem cell22_2125889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2125889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2125889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2125889 prefixEnd_2125889 := by exact prefixLift 2125889
  have htrace : WordTrace (prefixWord ++ tailWord_2125889) baseStart_2125889 baseEnd_2125889 := by
    simpa [prefixWord, tailWord_2125889, baseEnd_2125889] using wordTrace_append hprefix tailTrace_2125889
  have hstable : (prefixWord ++ tailWord_2125889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125889).length < 2 ^ (prefixWord ++ tailWord_2125889).sum := by decide
  have hdescent : baseEnd_2125889 < baseStart_2125889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126026 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_2126026 : Nat := 118140960795 + 2126026 * 2 ^ 59
def prefixEnd_2126026 : Nat := 4983230072969 + 3 ^ 40 * 2126026 * 2
def baseEnd_2126026 : Nat := 727782147970536098131727

theorem tailTrace_2126026 : CollatzResearch.WordTrace tailWord_2126026 prefixEnd_2126026 727782147970536098131727 := by
  unfold tailWord_2126026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19385634648944593294583483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51695025730518915452222621 19385634648944593294583483)
  ·
    refine ⟨29078451973416889941875225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19385634648944593294583483 29078451973416889941875225)
    ·
      refine ⟨21808838980062667456406419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29078451973416889941875225 21808838980062667456406419)
      ·
        refine ⟨32713258470094001184609629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21808838980062667456406419 32713258470094001184609629)
        ·
          refine ⟨12267471926285250444228611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32713258470094001184609629 12267471926285250444228611)
          ·
            refine ⟨18401207889427875666342917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12267471926285250444228611 18401207889427875666342917)
            ·
              refine ⟨3450226479267726687439297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18401207889427875666342917 3450226479267726687439297)
              ·
                refine ⟨2587669859450795015579473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3450226479267726687439297 2587669859450795015579473)
                ·
                  refine ⟨1940752394588096261684605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2587669859450795015579473 1940752394588096261684605)
                  ·
                    refine ⟨727782147970536098131727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940752394588096261684605 727782147970536098131727)
                    ·
                      rfl

theorem cell22_2126026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_2126026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126026 prefixEnd_2126026 := by exact prefixLift 2126026
  have htrace : WordTrace (prefixWord ++ tailWord_2126026) baseStart_2126026 baseEnd_2126026 := by
    simpa [prefixWord, tailWord_2126026, baseEnd_2126026] using wordTrace_append hprefix tailTrace_2126026
  have hstable : (prefixWord ++ tailWord_2126026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126026).length < 2 ^ (prefixWord ++ tailWord_2126026).sum := by decide
  have hdescent : baseEnd_2126026 < baseStart_2126026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126028 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 4]
def baseStart_2126028 : Nat := 118140960795 + 2126028 * 2 ^ 59
def prefixEnd_2126028 : Nat := 4983230072969 + 3 ^ 40 * 2126028 * 2
def baseEnd_2126028 : Nat := 242594277537136253193907

theorem tailTrace_2126028 : CollatzResearch.WordTrace tailWord_2126028 prefixEnd_2126028 242594277537136253193907 := by
  unfold tailWord_2126028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38771305770885563759953369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51695074361180751679937825 38771305770885563759953369)
  ·
    refine ⟨29078479328164172819965027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38771305770885563759953369 29078479328164172819965027)
    ·
      refine ⟨43617718992246259229947541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29078479328164172819965027 43617718992246259229947541)
      ·
        refine ⟨2044580577761543401403791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43617718992246259229947541 2044580577761543401403791)
        ·
          refine ⟨3066870866642315102105687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044580577761543401403791 3066870866642315102105687)
          ·
            refine ⟨4600306299963472653158531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066870866642315102105687 4600306299963472653158531)
            ·
              refine ⟨6900459449945208979737797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600306299963472653158531 6900459449945208979737797)
              ·
                refine ⟨1293836146864726683700837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6900459449945208979737797 1293836146864726683700837)
                ·
                  refine ⟨242594277537136253193907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293836146864726683700837 242594277537136253193907)
                  ·
                    rfl

theorem cell22_2126028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_2126028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126028 prefixEnd_2126028 := by exact prefixLift 2126028
  have htrace : WordTrace (prefixWord ++ tailWord_2126028) baseStart_2126028 baseEnd_2126028 := by
    simpa [prefixWord, tailWord_2126028, baseEnd_2126028] using wordTrace_append hprefix tailTrace_2126028
  have hstable : (prefixWord ++ tailWord_2126028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126028).length < 2 ^ (prefixWord ++ tailWord_2126028).sum := by decide
  have hdescent : baseEnd_2126028 < baseStart_2126028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126052 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2126052 : Nat := 118140960795 + 2126052 * 2 ^ 59
def prefixEnd_2126052 : Nat := 4983230072969 + 3 ^ 40 * 2126052 * 2
def baseEnd_2126052 : Nat := 727791048301880696981647

theorem tailTrace_2126052 : CollatzResearch.WordTrace tailWord_2126052 prefixEnd_2126052 727791048301880696981647 := by
  unfold tailWord_2126052
  simp only [CollatzResearch.WordTrace]
  refine ⟨38771743446842089809390205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51695657929122786412520273 38771743446842089809390205)
  ·
    refine ⟨14539403792565783678521327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38771743446842089809390205 14539403792565783678521327)
    ·
      refine ⟨21809105688848675517781991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14539403792565783678521327 21809105688848675517781991)
      ·
        refine ⟨32713658533273013276672987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21809105688848675517781991 32713658533273013276672987)
        ·
          refine ⟨49070487799909519915009481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32713658533273013276672987 49070487799909519915009481)
          ·
            refine ⟨36802865849932139936257111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49070487799909519915009481 36802865849932139936257111)
            ·
              refine ⟨55204298774898209904385667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36802865849932139936257111 55204298774898209904385667)
              ·
                refine ⟨82806448162347314856578501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55204298774898209904385667 82806448162347314856578501)
                ·
                  refine ⟨15526209030440121535608469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82806448162347314856578501 15526209030440121535608469)
                  ·
                    refine ⟨727791048301880696981647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15526209030440121535608469 727791048301880696981647)
                    ·
                      rfl

theorem cell22_2126052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2126052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126052 prefixEnd_2126052 := by exact prefixLift 2126052
  have htrace : WordTrace (prefixWord ++ tailWord_2126052) baseStart_2126052 baseEnd_2126052 := by
    simpa [prefixWord, tailWord_2126052, baseEnd_2126052] using wordTrace_append hprefix tailTrace_2126052
  have hstable : (prefixWord ++ tailWord_2126052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126052).length < 2 ^ (prefixWord ++ tailWord_2126052).sum := by decide
  have hdescent : baseEnd_2126052 < baseStart_2126052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126067 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 7]
def baseStart_2126067 : Nat := 118140960795 + 2126067 * 2 ^ 59
def prefixEnd_2126067 : Nat := 4983230072969 + 3 ^ 40 * 2126067 * 2
def baseEnd_2126067 : Nat := 242598727702808552618867

theorem tailTrace_2126067 : CollatzResearch.WordTrace tailWord_2126067 prefixEnd_2126067 242598727702808552618867 := by
  unfold tailWord_2126067
  simp only [CollatzResearch.WordTrace]
  refine ⟨77544033988629837180576455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51696022659086558120384303 77544033988629837180576455)
  ·
    refine ⟨116316050982944755770864683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77544033988629837180576455 116316050982944755770864683)
    ·
      refine ⟨174474076474417133656297025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116316050982944755770864683 174474076474417133656297025)
      ·
        refine ⟨130855557355812850242222769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174474076474417133656297025 130855557355812850242222769)
        ·
          refine ⟨98141668016859637681667077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130855557355812850242222769 98141668016859637681667077)
          ·
            refine ⟨18401562753161182065312577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98141668016859637681667077 18401562753161182065312577)
            ·
              refine ⟨13801172064870886548984433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18401562753161182065312577 13801172064870886548984433)
              ·
                refine ⟨10350879048653164911738325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13801172064870886548984433 10350879048653164911738325)
                ·
                  refine ⟨242598727702808552618867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10350879048653164911738325 242598727702808552618867)
                  ·
                    rfl

theorem cell22_2126067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_2126067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126067 prefixEnd_2126067 := by exact prefixLift 2126067
  have htrace : WordTrace (prefixWord ++ tailWord_2126067) baseStart_2126067 baseEnd_2126067 := by
    simpa [prefixWord, tailWord_2126067, baseEnd_2126067] using wordTrace_append hprefix tailTrace_2126067
  have hstable : (prefixWord ++ tailWord_2126067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126067).length < 2 ^ (prefixWord ++ tailWord_2126067).sum := by decide
  have hdescent : baseEnd_2126067 < baseStart_2126067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126088 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 1, 3]
def baseStart_2126088 : Nat := 118140960795 + 2126088 * 2 ^ 59
def prefixEnd_2126088 : Nat := 4983230072969 + 3 ^ 40 * 2126088 * 2
def baseEnd_2126088 : Nat := 727803371837588603081537

theorem tailTrace_2126088 : CollatzResearch.WordTrace tailWord_2126088 prefixEnd_2126088 727803371837588603081537 := by
  unfold tailWord_2126088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38772399960776878883545459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51696533281035838511393945 38772399960776878883545459)
  ·
    refine ⟨58158599941165318325318189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38772399960776878883545459 58158599941165318325318189)
    ·
      refine ⟨21809474977936994371994321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58158599941165318325318189 21809474977936994371994321)
      ·
        refine ⟨16357106233452745778995741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21809474977936994371994321 16357106233452745778995741)
        ·
          refine ⟨6133914837544779667123403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16357106233452745778995741 6133914837544779667123403)
          ·
            refine ⟨9200872256317169500685105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133914837544779667123403 9200872256317169500685105)
            ·
              refine ⟨6900654192237877125513829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9200872256317169500685105 6900654192237877125513829)
              ·
                refine ⟨1293872661044601961033843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6900654192237877125513829 1293872661044601961033843)
                ·
                  refine ⟨1940808991566902941550765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293872661044601961033843 1940808991566902941550765)
                  ·
                    refine ⟨727803371837588603081537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940808991566902941550765 727803371837588603081537)
                    ·
                      rfl

theorem cell22_2126088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_2126088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126088 prefixEnd_2126088 := by exact prefixLift 2126088
  have htrace : WordTrace (prefixWord ++ tailWord_2126088) baseStart_2126088 baseEnd_2126088 := by
    simpa [prefixWord, tailWord_2126088, baseEnd_2126088] using wordTrace_append hprefix tailTrace_2126088
  have hstable : (prefixWord ++ tailWord_2126088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126088).length < 2 ^ (prefixWord ++ tailWord_2126088).sum := by decide
  have hdescent : baseEnd_2126088 < baseStart_2126088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126122 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2126122 : Nat := 118140960795 + 2126122 * 2 ^ 59
def prefixEnd_2126122 : Nat := 4983230072969 + 3 ^ 40 * 2126122 * 2
def baseEnd_2126122 : Nat := 727815010732423847731433

theorem tailTrace_2126122 : CollatzResearch.WordTrace tailWord_2126122 prefixEnd_2126122 727815010732423847731433 := by
  unfold tailWord_2126122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19386510000857645393457155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51697360002287054382552413 19386510000857645393457155)
  ·
    refine ⟨29079765001286468090185733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19386510000857645393457155 29079765001286468090185733)
    ·
      refine ⟨5452455937741212766909825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29079765001286468090185733 5452455937741212766909825)
      ·
        refine ⟨4089341953305909575182369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5452455937741212766909825 4089341953305909575182369)
        ·
          refine ⟨3067006464979432181386777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4089341953305909575182369 3067006464979432181386777)
          ·
            refine ⟨2300254848734574136040083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3067006464979432181386777 2300254848734574136040083)
            ·
              refine ⟨3450382273101861204060125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300254848734574136040083 3450382273101861204060125)
              ·
                refine ⟨1293893352413197951522547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3450382273101861204060125 1293893352413197951522547)
                ·
                  refine ⟨1940840028619796927283821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293893352413197951522547 1940840028619796927283821)
                  ·
                    refine ⟨727815010732423847731433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940840028619796927283821 727815010732423847731433)
                    ·
                      rfl

theorem cell22_2126122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2126122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126122 prefixEnd_2126122 := by exact prefixLift 2126122
  have htrace : WordTrace (prefixWord ++ tailWord_2126122) baseStart_2126122 baseEnd_2126122 := by
    simpa [prefixWord, tailWord_2126122, baseEnd_2126122] using wordTrace_append hprefix tailTrace_2126122
  have hstable : (prefixWord ++ tailWord_2126122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126122).length < 2 ^ (prefixWord ++ tailWord_2126122).sum := by decide
  have hdescent : baseEnd_2126122 < baseStart_2126122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126165 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_2126165 : Nat := 118140960795 + 2126165 * 2 ^ 59
def prefixEnd_2126165 : Nat := 4983230072969 + 3 ^ 40 * 2126165 * 2
def baseEnd_2126165 : Nat := 727829730511186068906301

theorem tailTrace_2126165 : CollatzResearch.WordTrace tailWord_2126165 prefixEnd_2126165 727829730511186068906301 := by
  unfold tailWord_2126165
  simp only [CollatzResearch.WordTrace]
  refine ⟨77547608342274799917643949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51698405561516533278429299 77547608342274799917643949)
  ·
    refine ⟨29080353128353049969116481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77547608342274799917643949 29080353128353049969116481)
    ·
      refine ⟨21810264846264787476837361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29080353128353049969116481 21810264846264787476837361)
      ·
        refine ⟨16357698634698590607628021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21810264846264787476837361 16357698634698590607628021)
        ·
          refine ⟨1533534247002992869465127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16357698634698590607628021 1533534247002992869465127)
          ·
            refine ⟨2300301370504489304197691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533534247002992869465127 2300301370504489304197691)
            ·
              refine ⟨3450452055756733956296537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300301370504489304197691 3450452055756733956296537)
              ·
                refine ⟨2587839041817550467222403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3450452055756733956296537 2587839041817550467222403)
                ·
                  refine ⟨3881758562726325700833605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587839041817550467222403 3881758562726325700833605)
                  ·
                    refine ⟨727829730511186068906301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3881758562726325700833605 727829730511186068906301)
                    ·
                      rfl

theorem cell22_2126165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_2126165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126165 prefixEnd_2126165 := by exact prefixLift 2126165
  have htrace : WordTrace (prefixWord ++ tailWord_2126165) baseStart_2126165 baseEnd_2126165 := by
    simpa [prefixWord, tailWord_2126165, baseEnd_2126165] using wordTrace_append hprefix tailTrace_2126165
  have hstable : (prefixWord ++ tailWord_2126165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126165).length < 2 ^ (prefixWord ++ tailWord_2126165).sum := by decide
  have hdescent : baseEnd_2126165 < baseStart_2126165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126240 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 1, 3]
def baseStart_2126240 : Nat := 118140960795 + 2126240 * 2 ^ 59
def prefixEnd_2126240 : Nat := 4983230072969 + 3 ^ 40 * 2126240 * 2
def baseEnd_2126240 : Nat := 727855404543910873281071

theorem tailTrace_2126240 : CollatzResearch.WordTrace tailWord_2126240 prefixEnd_2126240 727855404543910873281071 := by
  unfold tailWord_2126240
  simp only [CollatzResearch.WordTrace]
  refine ⟨38775171908501543863312087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51700229211335391817749449 38775171908501543863312087)
  ·
    refine ⟨58162757862752315794968131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38775171908501543863312087 58162757862752315794968131)
    ·
      refine ⟨87244136794128473692452197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58162757862752315794968131 87244136794128473692452197)
      ·
        refine ⟨16358275648899088817334787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87244136794128473692452197 16358275648899088817334787)
        ·
          refine ⟨24537413473348633226002181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16358275648899088817334787 24537413473348633226002181)
          ·
            refine ⟨4600765026252868729875409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24537413473348633226002181 4600765026252868729875409)
            ·
              refine ⟨3450573769689651547406557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4600765026252868729875409 3450573769689651547406557)
              ·
                refine ⟨1293965163633619330277459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3450573769689651547406557 1293965163633619330277459)
                ·
                  refine ⟨1940947745450428995416189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293965163633619330277459 1940947745450428995416189)
                  ·
                    refine ⟨727855404543910873281071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940947745450428995416189 727855404543910873281071)
                    ·
                      rfl

theorem cell22_2126240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_2126240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126240 prefixEnd_2126240 := by exact prefixLift 2126240
  have htrace : WordTrace (prefixWord ++ tailWord_2126240) baseStart_2126240 baseEnd_2126240 := by
    simpa [prefixWord, tailWord_2126240, baseEnd_2126240] using wordTrace_append hprefix tailTrace_2126240
  have hstable : (prefixWord ++ tailWord_2126240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126240).length < 2 ^ (prefixWord ++ tailWord_2126240).sum := by decide
  have hdescent : baseEnd_2126240 < baseStart_2126240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126253 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2126253 : Nat := 118140960795 + 2126253 * 2 ^ 59
def prefixEnd_2126253 : Nat := 4983230072969 + 3 ^ 40 * 2126253 * 2
def baseEnd_2126253 : Nat := 242619951569861057568677

theorem tailTrace_2126253 : CollatzResearch.WordTrace tailWord_2126253 prefixEnd_2126253 242619951569861057568677 := by
  unfold tailWord_2126253
  simp only [CollatzResearch.WordTrace]
  refine ⟨77550817965955990946847413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51700545310637327297898275 77550817965955990946847413)
  ·
    refine ⟨7270389184308374151266945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77550817965955990946847413 7270389184308374151266945)
    ·
      refine ⟨5452791888231280613450209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7270389184308374151266945 5452791888231280613450209)
      ·
        refine ⟨4089593916173460460087657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5452791888231280613450209 4089593916173460460087657)
        ·
          refine ⟨3067195437130095345065743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4089593916173460460087657 3067195437130095345065743)
          ·
            refine ⟨4600793155695143017598615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3067195437130095345065743 4600793155695143017598615)
            ·
              refine ⟨6901189733542714526397923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600793155695143017598615 6901189733542714526397923)
              ·
                refine ⟨10351784600314071789596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901189733542714526397923 10351784600314071789596885)
                ·
                  refine ⟨242619951569861057568677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10351784600314071789596885 242619951569861057568677)
                  ·
                    rfl

theorem cell22_2126253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2126253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126253 prefixEnd_2126253 := by exact prefixLift 2126253
  have htrace : WordTrace (prefixWord ++ tailWord_2126253) baseStart_2126253 baseEnd_2126253 := by
    simpa [prefixWord, tailWord_2126253, baseEnd_2126253] using wordTrace_append hprefix tailTrace_2126253
  have hstable : (prefixWord ++ tailWord_2126253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126253).length < 2 ^ (prefixWord ++ tailWord_2126253).sum := by decide
  have hdescent : baseEnd_2126253 < baseStart_2126253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126386 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2126386 : Nat := 118140960795 + 2126386 * 2 ^ 59
def prefixEnd_2126386 : Nat := 4983230072969 + 3 ^ 40 * 2126386 * 2
def baseEnd_2126386 : Nat := 727905383327615159130623

theorem tailTrace_2126386 : CollatzResearch.WordTrace tailWord_2126386 prefixEnd_2126386 727905383327615159130623 := by
  unfold tailWord_2126386
  simp only [CollatzResearch.WordTrace]
  refine ⟨19388917218618538665359753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51703779249649436440959341 19388917218618538665359753)
  ·
    refine ⟨14541687913963903999019815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19388917218618538665359753 14541687913963903999019815)
    ·
      refine ⟨21812531870945855998529723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14541687913963903999019815 21812531870945855998529723)
      ·
        refine ⟨32718797806418783997794585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21812531870945855998529723 32718797806418783997794585)
        ·
          refine ⟨24539098354814087998345939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32718797806418783997794585 24539098354814087998345939)
          ·
            refine ⟨36808647532221131997518909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24539098354814087998345939 36808647532221131997518909)
            ·
              refine ⟨13803242824582924499069591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36808647532221131997518909 13803242824582924499069591)
              ·
                refine ⟨20704864236874386748604387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13803242824582924499069591 20704864236874386748604387)
                ·
                  refine ⟨31057296355311580122906581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20704864236874386748604387 31057296355311580122906581)
                  ·
                    refine ⟨727905383327615159130623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31057296355311580122906581 727905383327615159130623)
                    ·
                      rfl

theorem cell22_2126386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2126386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126386 prefixEnd_2126386 := by exact prefixLift 2126386
  have htrace : WordTrace (prefixWord ++ tailWord_2126386) baseStart_2126386 baseEnd_2126386 := by
    simpa [prefixWord, tailWord_2126386, baseEnd_2126386] using wordTrace_append hprefix tailTrace_2126386
  have hstable : (prefixWord ++ tailWord_2126386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126386).length < 2 ^ (prefixWord ++ tailWord_2126386).sum := by decide
  have hdescent : baseEnd_2126386 < baseStart_2126386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126431 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_2126431 : Nat := 118140960795 + 2126431 * 2 ^ 59
def prefixEnd_2126431 : Nat := 4983230072969 + 3 ^ 40 * 2126431 * 2
def baseEnd_2126431 : Nat := 727920787747250041755485

theorem tailTrace_2126431 : CollatzResearch.WordTrace tailWord_2126431 prefixEnd_2126431 727920787747250041755485 := by
  unfold tailWord_2126431
  simp only [CollatzResearch.WordTrace]
  refine ⟨77557310159311127346827147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51704873439540751564551431 77557310159311127346827147)
  ·
    refine ⟨116335965238966691020240721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77557310159311127346827147 116335965238966691020240721)
    ·
      refine ⟨87251973929225018265180541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116335965238966691020240721 87251973929225018265180541)
      ·
        refine ⟨32719490223459381849442703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87251973929225018265180541 32719490223459381849442703)
        ·
          refine ⟨49079235335189072774164055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32719490223459381849442703 49079235335189072774164055)
          ·
            refine ⟨73618853002783609161246083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49079235335189072774164055 73618853002783609161246083)
            ·
              refine ⟨110428279504175413741869125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73618853002783609161246083 110428279504175413741869125)
              ·
                refine ⟨20705302407032890076600461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110428279504175413741869125 20705302407032890076600461)
                ·
                  refine ⟨7764488402637333778725173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20705302407032890076600461 7764488402637333778725173)
                  ·
                    refine ⟨727920787747250041755485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7764488402637333778725173 727920787747250041755485)
                    ·
                      rfl

theorem cell22_2126431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_2126431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126431 prefixEnd_2126431 := by exact prefixLift 2126431
  have htrace : WordTrace (prefixWord ++ tailWord_2126431) baseStart_2126431 baseEnd_2126431 := by
    simpa [prefixWord, tailWord_2126431, baseEnd_2126431] using wordTrace_append hprefix tailTrace_2126431
  have hstable : (prefixWord ++ tailWord_2126431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126431).length < 2 ^ (prefixWord ++ tailWord_2126431).sum := by decide
  have hdescent : baseEnd_2126431 < baseStart_2126431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126433 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 6]
def baseStart_2126433 : Nat := 118140960795 + 2126433 * 2 ^ 59
def prefixEnd_2126433 : Nat := 4983230072969 + 3 ^ 40 * 2126433 * 2
def baseEnd_2126433 : Nat := 242640490796040901068493

theorem tailTrace_2126433 : CollatzResearch.WordTrace tailWord_2126433 prefixEnd_2126433 242640490796040901068493 := by
  unfold tailWord_2126433
  simp only [CollatzResearch.WordTrace]
  refine ⟨77557383105303881688399953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51704922070202587792266635 77557383105303881688399953)
  ·
    refine ⟨58168037328977911266299965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77557383105303881688399953 58168037328977911266299965)
    ·
      refine ⟨21813013998366716724862487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58168037328977911266299965 21813013998366716724862487)
      ·
        refine ⟨32719520997550075087293731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21813013998366716724862487 32719520997550075087293731)
        ·
          refine ⟨49079281496325112630940597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32719520997550075087293731 49079281496325112630940597)
          ·
            refine ⟨4601182640280479309150681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49079281496325112630940597 4601182640280479309150681)
            ·
              refine ⟨3450886980210359481863011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4601182640280479309150681 3450886980210359481863011)
              ·
                refine ⟨5176330470315539222794517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450886980210359481863011 5176330470315539222794517)
                ·
                  refine ⟨242640490796040901068493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5176330470315539222794517 242640490796040901068493)
                  ·
                    rfl

theorem cell22_2126433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_2126433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126433 prefixEnd_2126433 := by exact prefixLift 2126433
  have htrace : WordTrace (prefixWord ++ tailWord_2126433) baseStart_2126433 baseEnd_2126433 := by
    simpa [prefixWord, tailWord_2126433, baseEnd_2126433] using wordTrace_append hprefix tailTrace_2126433
  have hstable : (prefixWord ++ tailWord_2126433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126433).length < 2 ^ (prefixWord ++ tailWord_2126433).sum := by decide
  have hdescent : baseEnd_2126433 < baseStart_2126433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126484 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2126484 : Nat := 118140960795 + 2126484 * 2 ^ 59
def prefixEnd_2126484 : Nat := 4983230072969 + 3 ^ 40 * 2126484 * 2
def baseEnd_2126484 : Nat := 242646310243458523393441

theorem tailTrace_2126484 : CollatzResearch.WordTrace tailWord_2126484 prefixEnd_2126484 242646310243458523393441 := by
  unfold tailWord_2126484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38779621614059558699253253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51706162152079411599004337 38779621614059558699253253)
  ·
    refine ⟨7271179052636167256109985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38779621614059558699253253 7271179052636167256109985)
    ·
      refine ⟨5453384289477125442082489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7271179052636167256109985 5453384289477125442082489)
      ·
        refine ⟨4090038217107844081561867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5453384289477125442082489 4090038217107844081561867)
        ·
          refine ⟨6135057325661766122342801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090038217107844081561867 6135057325661766122342801)
          ·
            refine ⟨4601292994246324591757101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6135057325661766122342801 4601292994246324591757101)
            ·
              refine ⟨1725484872842371721908913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4601292994246324591757101 1725484872842371721908913)
              ·
                refine ⟨1294113654631778791431685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725484872842371721908913 1294113654631778791431685)
                ·
                  refine ⟨242646310243458523393441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294113654631778791431685 242646310243458523393441)
                  ·
                    rfl

theorem cell22_2126484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2126484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126484 prefixEnd_2126484 := by exact prefixLift 2126484
  have htrace : WordTrace (prefixWord ++ tailWord_2126484) baseStart_2126484 baseEnd_2126484 := by
    simpa [prefixWord, tailWord_2126484, baseEnd_2126484] using wordTrace_append hprefix tailTrace_2126484
  have hstable : (prefixWord ++ tailWord_2126484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126484).length < 2 ^ (prefixWord ++ tailWord_2126484).sum := by decide
  have hdescent : baseEnd_2126484 < baseStart_2126484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126491 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_2126491 : Nat := 118140960795 + 2126491 * 2 ^ 59
def prefixEnd_2126491 : Nat := 4983230072969 + 3 ^ 40 * 2126491 * 2
def baseEnd_2126491 : Nat := 727941326973429885255301

theorem tailTrace_2126491 : CollatzResearch.WordTrace tailWord_2126491 prefixEnd_2126491 727941326973429885255301 := by
  unfold tailWord_2126491
  simp only [CollatzResearch.WordTrace]
  refine ⟨77559498539093757594011327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51706332359395838396007551 77559498539093757594011327)
  ·
    refine ⟨116339247808640636391016991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77559498539093757594011327 116339247808640636391016991)
    ·
      refine ⟨174508871712960954586525487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116339247808640636391016991 174508871712960954586525487)
      ·
        refine ⟨261763307569441431879788231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174508871712960954586525487 261763307569441431879788231)
        ·
          refine ⟨392644961354162147819682347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261763307569441431879788231 392644961354162147819682347)
          ·
            refine ⟨588967442031243221729523521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392644961354162147819682347 588967442031243221729523521)
            ·
              refine ⟨441725581523432416297142641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588967442031243221729523521 441725581523432416297142641)
              ·
                refine ⟨331294186142574312222856981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441725581523432416297142641 331294186142574312222856981)
                ·
                  refine ⟨15529414975433170885446421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 331294186142574312222856981 15529414975433170885446421)
                  ·
                    refine ⟨727941326973429885255301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15529414975433170885446421 727941326973429885255301)
                    ·
                      rfl

theorem cell22_2126491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_2126491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126491 prefixEnd_2126491 := by exact prefixLift 2126491
  have htrace : WordTrace (prefixWord ++ tailWord_2126491) baseStart_2126491 baseEnd_2126491 := by
    simpa [prefixWord, tailWord_2126491, baseEnd_2126491] using wordTrace_append hprefix tailTrace_2126491
  have hstable : (prefixWord ++ tailWord_2126491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126491).length < 2 ^ (prefixWord ++ tailWord_2126491).sum := by decide
  have hdescent : baseEnd_2126491 < baseStart_2126491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126540 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_2126540 : Nat := 118140960795 + 2126540 * 2 ^ 59
def prefixEnd_2126540 : Nat := 4983230072969 + 3 ^ 40 * 2126540 * 2
def baseEnd_2126540 : Nat := 242652700224936696926717

theorem tailTrace_2126540 : CollatzResearch.WordTrace tailWord_2126540 prefixEnd_2126540 242652700224936696926717 := by
  unfold tailWord_2126540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38780642857958119481272537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51707523810610825975030049 38780642857958119481272537)
  ·
    refine ⟨29085482143468589610954403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38780642857958119481272537 29085482143468589610954403)
    ·
      refine ⟨43628223215202884416431605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29085482143468589610954403 43628223215202884416431605)
      ·
        refine ⟨4090145926425270414040463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43628223215202884416431605 4090145926425270414040463)
        ·
          refine ⟨6135218889637905621060695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090145926425270414040463 6135218889637905621060695)
          ·
            refine ⟨9202828334456858431591043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135218889637905621060695 9202828334456858431591043)
            ·
              refine ⟨13804242501685287647386565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9202828334456858431591043 13804242501685287647386565)
              ·
                refine ⟨2588295469065991433884981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13804242501685287647386565 2588295469065991433884981)
                ·
                  refine ⟨242652700224936696926717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2588295469065991433884981 242652700224936696926717)
                  ·
                    rfl

theorem cell22_2126540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_2126540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126540 prefixEnd_2126540 := by exact prefixLift 2126540
  have htrace : WordTrace (prefixWord ++ tailWord_2126540) baseStart_2126540 baseEnd_2126540 := by
    simpa [prefixWord, tailWord_2126540, baseEnd_2126540] using wordTrace_append hprefix tailTrace_2126540
  have hstable : (prefixWord ++ tailWord_2126540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126540).length < 2 ^ (prefixWord ++ tailWord_2126540).sum := by decide
  have hdescent : baseEnd_2126540 < baseStart_2126540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126553 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_2126553 : Nat := 118140960795 + 2126553 * 2 ^ 59
def prefixEnd_2126553 : Nat := 4983230072969 + 3 ^ 40 * 2126553 * 2
def baseEnd_2126553 : Nat := 727962550840482390205111

theorem tailTrace_2126553 : CollatzResearch.WordTrace tailWord_2126553 prefixEnd_2126553 727962550840482390205111 := by
  unfold tailWord_2126553
  simp only [CollatzResearch.WordTrace]
  refine ⟨77561759864869142182768313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51707839909912761455178875 77561759864869142182768313)
  ·
    refine ⟨58171319898651856637076235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77561759864869142182768313 58171319898651856637076235)
    ·
      refine ⟨87256979847977784955614353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58171319898651856637076235 87256979847977784955614353)
      ·
        refine ⟨65442734885983338716710765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87256979847977784955614353 65442734885983338716710765)
        ·
          refine ⟨24541025582243752018766537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65442734885983338716710765 24541025582243752018766537)
          ·
            refine ⟨18405769186682814014074903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24541025582243752018766537 18405769186682814014074903)
            ·
              refine ⟨27608653780024221021112355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18405769186682814014074903 27608653780024221021112355)
              ·
                refine ⟨41412980670036331531668533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27608653780024221021112355 41412980670036331531668533)
                ·
                  refine ⟨3882466937815906081093925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41412980670036331531668533 3882466937815906081093925)
                  ·
                    refine ⟨727962550840482390205111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882466937815906081093925 727962550840482390205111)
                    ·
                      rfl

theorem cell22_2126553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_2126553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126553 prefixEnd_2126553 := by exact prefixLift 2126553
  have htrace : WordTrace (prefixWord ++ tailWord_2126553) baseStart_2126553 baseEnd_2126553 := by
    simpa [prefixWord, tailWord_2126553, baseEnd_2126553] using wordTrace_append hprefix tailTrace_2126553
  have hstable : (prefixWord ++ tailWord_2126553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126553).length < 2 ^ (prefixWord ++ tailWord_2126553).sum := by decide
  have hdescent : baseEnd_2126553 < baseStart_2126553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126570 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2126570 : Nat := 118140960795 + 2126570 * 2 ^ 59
def prefixEnd_2126570 : Nat := 4983230072969 + 3 ^ 40 * 2126570 * 2
def baseEnd_2126570 : Nat := 727968370287900012530059

theorem tailTrace_2126570 : CollatzResearch.WordTrace tailWord_2126570 prefixEnd_2126570 727968370287900012530059 := by
  unfold tailWord_2126570
  simp only [CollatzResearch.WordTrace]
  refine ⟨19390594976451888521534291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51708253270538369390758109 19390594976451888521534291)
  ·
    refine ⟨29085892464677832782301437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19390594976451888521534291 29085892464677832782301437)
    ·
      refine ⟨10907209674254187293363039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29085892464677832782301437 10907209674254187293363039)
      ·
        refine ⟨16360814511381280940044559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10907209674254187293363039 16360814511381280940044559)
        ·
          refine ⟨24541221767071921410066839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16360814511381280940044559 24541221767071921410066839)
          ·
            refine ⟨36811832650607882115100259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24541221767071921410066839 36811832650607882115100259)
            ·
              refine ⟨55217748975911823172650389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36811832650607882115100259 55217748975911823172650389)
              ·
                refine ⟨2588331983245866711217987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55217748975911823172650389 2588331983245866711217987)
                ·
                  refine ⟨3882497974868800066826981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588331983245866711217987 3882497974868800066826981)
                  ·
                    refine ⟨727968370287900012530059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882497974868800066826981 727968370287900012530059)
                    ·
                      rfl

theorem cell22_2126570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2126570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126570 prefixEnd_2126570 := by exact prefixLift 2126570
  have htrace : WordTrace (prefixWord ++ tailWord_2126570) baseStart_2126570 baseEnd_2126570 := by
    simpa [prefixWord, tailWord_2126570, baseEnd_2126570] using wordTrace_append hprefix tailTrace_2126570
  have hstable : (prefixWord ++ tailWord_2126570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126570).length < 2 ^ (prefixWord ++ tailWord_2126570).sum := by decide
  have hdescent : baseEnd_2126570 < baseStart_2126570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126613 : List Nat := [1, 3, 2, 1, 2, 2, 2, 9]
def baseStart_2126613 : Nat := 118140960795 + 2126613 * 2 ^ 59
def prefixEnd_2126613 : Nat := 4983230072969 + 3 ^ 40 * 2126613 * 2
def baseEnd_2126613 : Nat := 80887010007406914856103

theorem tailTrace_2126613 : CollatzResearch.WordTrace tailWord_2126613 prefixEnd_2126613 80887010007406914856103 := by
  unfold tailWord_2126613
  simp only [CollatzResearch.WordTrace]
  refine ⟨77563948244651772429952493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51709298829767848286634995 77563948244651772429952493)
  ·
    refine ⟨29086480591744414661232185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77563948244651772429952493 29086480591744414661232185)
    ·
      refine ⟨21814860443808310995924139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29086480591744414661232185 21814860443808310995924139)
      ·
        refine ⟨32722290665712466493886209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21814860443808310995924139 32722290665712466493886209)
        ·
          refine ⟨24541717999284349870414657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32722290665712466493886209 24541717999284349870414657)
          ·
            refine ⟨18406288499463262402810993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24541717999284349870414657 18406288499463262402810993)
            ·
              refine ⟨13804716374597446802108245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18406288499463262402810993 13804716374597446802108245)
              ·
                refine ⟨80887010007406914856103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13804716374597446802108245 80887010007406914856103)
                ·
                  rfl

theorem cell22_2126613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 9].length) (baseStart_2126613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126613 prefixEnd_2126613 := by exact prefixLift 2126613
  have htrace : WordTrace (prefixWord ++ tailWord_2126613) baseStart_2126613 baseEnd_2126613 := by
    simpa [prefixWord, tailWord_2126613, baseEnd_2126613] using wordTrace_append hprefix tailTrace_2126613
  have hstable : (prefixWord ++ tailWord_2126613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126613).length < 2 ^ (prefixWord ++ tailWord_2126613).sum := by decide
  have hdescent : baseEnd_2126613 < baseStart_2126613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126754 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_2126754 : Nat := 118140960795 + 2126754 * 2 ^ 59
def prefixEnd_2126754 : Nat := 4983230072969 + 3 ^ 40 * 2126754 * 2
def baseEnd_2126754 : Nat := 242677119082728288643165

theorem tailTrace_2126754 : CollatzResearch.WordTrace tailWord_2126754 prefixEnd_2126754 242677119082728288643165 := by
  unfold tailWord_2126754
  simp only [CollatzResearch.WordTrace]
  refine ⟨19392272734285238377708829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51712727291427302340556877 19392272734285238377708829)
  ·
    refine ⟨7272102275356964391640811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19392272734285238377708829 7272102275356964391640811)
    ·
      refine ⟨10908153413035446587461217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7272102275356964391640811 10908153413035446587461217)
      ·
        refine ⟨8181115059776584940595913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10908153413035446587461217 8181115059776584940595913)
        ·
          refine ⟨6135836294832438705446935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8181115059776584940595913 6135836294832438705446935)
          ·
            refine ⟨9203754442248658058170403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135836294832438705446935 9203754442248658058170403)
            ·
              refine ⟨13805631663372987087255605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9203754442248658058170403 13805631663372987087255605)
              ·
                refine ⟨1294277968441217539430213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13805631663372987087255605 1294277968441217539430213)
                ·
                  refine ⟨242677119082728288643165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294277968441217539430213 242677119082728288643165)
                  ·
                    rfl

theorem cell22_2126754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2126754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126754 prefixEnd_2126754 := by exact prefixLift 2126754
  have htrace : WordTrace (prefixWord ++ tailWord_2126754) baseStart_2126754 baseEnd_2126754 := by
    simpa [prefixWord, tailWord_2126754, baseEnd_2126754] using wordTrace_append hprefix tailTrace_2126754
  have hstable : (prefixWord ++ tailWord_2126754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126754).length < 2 ^ (prefixWord ++ tailWord_2126754).sum := by decide
  have hdescent : baseEnd_2126754 < baseStart_2126754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126769 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_2126769 : Nat := 118140960795 + 2126769 * 2 ^ 59
def prefixEnd_2126769 : Nat := 4983230072969 + 3 ^ 40 * 2126769 * 2
def baseEnd_2126769 : Nat := 728036492054729826804449

theorem tailTrace_2126769 : CollatzResearch.WordTrace tailWord_2126769 prefixEnd_2126769 728036492054729826804449 := by
  unfold tailWord_2126769
  simp only [CollatzResearch.WordTrace]
  refine ⟨77569638032086611072631361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51713092021391074048420907 77569638032086611072631361)
  ·
    refine ⟨58177228524064958304473521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77569638032086611072631361 58177228524064958304473521)
    ·
      refine ⟨43632921393048718728355141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58177228524064958304473521 43632921393048718728355141)
      ·
        refine ⟨8181172761196634761566589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43632921393048718728355141 8181172761196634761566589)
        ·
          refine ⟨3067939785448738035587471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8181172761196634761566589 3067939785448738035587471)
          ·
            refine ⟨4601909678173107053381207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3067939785448738035587471 4601909678173107053381207)
            ·
              refine ⟨6902864517259660580071811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4601909678173107053381207 6902864517259660580071811)
              ·
                refine ⟨10354296775889490870107717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6902864517259660580071811 10354296775889490870107717)
                ·
                  refine ⟨1941430645479279538145197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10354296775889490870107717 1941430645479279538145197)
                  ·
                    refine ⟨728036492054729826804449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941430645479279538145197 728036492054729826804449)
                    ·
                      rfl

theorem cell22_2126769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_2126769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126769 prefixEnd_2126769 := by exact prefixLift 2126769
  have htrace : WordTrace (prefixWord ++ tailWord_2126769) baseStart_2126769 baseEnd_2126769 := by
    simpa [prefixWord, tailWord_2126769, baseEnd_2126769] using wordTrace_append hprefix tailTrace_2126769
  have hstable : (prefixWord ++ tailWord_2126769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126769).length < 2 ^ (prefixWord ++ tailWord_2126769).sum := by decide
  have hdescent : baseEnd_2126769 < baseStart_2126769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126837 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2126837 : Nat := 118140960795 + 2126837 * 2 ^ 59
def prefixEnd_2126837 : Nat := 4983230072969 + 3 ^ 40 * 2126837 * 2
def baseEnd_2126837 : Nat := 728059769844400316104241

theorem tailTrace_2126837 : CollatzResearch.WordTrace tailWord_2126837 prefixEnd_2126837 728059769844400316104241 := by
  unfold tailWord_2126837
  simp only [CollatzResearch.WordTrace]
  refine ⟨77572118195840258686106765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51714745463893505790737843 77572118195840258686106765)
  ·
    refine ⟨29089544323440097007290037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77572118195840258686106765 29089544323440097007290037)
    ·
      refine ⟨2727144780322509094433441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29089544323440097007290037 2727144780322509094433441)
      ·
        refine ⟨2045358585241881820825081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2727144780322509094433441 2045358585241881820825081)
        ·
          refine ⟨1534018938931411365618811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045358585241881820825081 1534018938931411365618811)
          ·
            refine ⟨2301028408397117048428217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534018938931411365618811 2301028408397117048428217)
            ·
              refine ⟨1725771306297837786321163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2301028408397117048428217 1725771306297837786321163)
              ·
                refine ⟨2588656959446756679481745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725771306297837786321163 2588656959446756679481745)
                ·
                  refine ⟨1941492719585067509611309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2588656959446756679481745 1941492719585067509611309)
                  ·
                    refine ⟨728059769844400316104241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941492719585067509611309 728059769844400316104241)
                    ·
                      rfl

theorem cell22_2126837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2126837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126837 prefixEnd_2126837 := by exact prefixLift 2126837
  have htrace : WordTrace (prefixWord ++ tailWord_2126837) baseStart_2126837 baseEnd_2126837 := by
    simpa [prefixWord, tailWord_2126837, baseEnd_2126837] using wordTrace_append hprefix tailTrace_2126837
  have hstable : (prefixWord ++ tailWord_2126837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126837).length < 2 ^ (prefixWord ++ tailWord_2126837).sum := by decide
  have hdescent : baseEnd_2126837 < baseStart_2126837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126840 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_2126840 : Nat := 118140960795 + 2126840 * 2 ^ 59
def prefixEnd_2126840 : Nat := 4983230072969 + 3 ^ 40 * 2126840 * 2
def baseEnd_2126840 : Nat := 728060796805709308279231

theorem tailTrace_2126840 : CollatzResearch.WordTrace tailWord_2126840 prefixEnd_2126840 728060796805709308279231 := by
  unfold tailWord_2126840
  simp only [CollatzResearch.WordTrace]
  refine ⟨38786113807414695099232987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51714818409886260132310649 38786113807414695099232987)
  ·
    refine ⟨58179170711122042648849481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38786113807414695099232987 58179170711122042648849481)
    ·
      refine ⟨43634378033341531986637111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58179170711122042648849481 43634378033341531986637111)
      ·
        refine ⟨65451567050012297979955667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43634378033341531986637111 65451567050012297979955667)
        ·
          refine ⟨98177350575018446969933501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65451567050012297979955667 98177350575018446969933501)
          ·
            refine ⟨36816506465631917613725063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98177350575018446969933501 36816506465631917613725063)
            ·
              refine ⟨55224759698447876420587595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36816506465631917613725063 55224759698447876420587595)
              ·
                refine ⟨82837139547671814630881393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55224759698447876420587595 82837139547671814630881393)
                ·
                  refine ⟨62127854660753860973161045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82837139547671814630881393 62127854660753860973161045)
                  ·
                    refine ⟨728060796805709308279231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62127854660753860973161045 728060796805709308279231)
                    ·
                      rfl

theorem cell22_2126840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_2126840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126840 prefixEnd_2126840 := by exact prefixLift 2126840
  have htrace : WordTrace (prefixWord ++ tailWord_2126840) baseStart_2126840 baseEnd_2126840 := by
    simpa [prefixWord, tailWord_2126840, baseEnd_2126840] using wordTrace_append hprefix tailTrace_2126840
  have hstable : (prefixWord ++ tailWord_2126840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126840).length < 2 ^ (prefixWord ++ tailWord_2126840).sum := by decide
  have hdescent : baseEnd_2126840 < baseStart_2126840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126844 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 5]
def baseStart_2126844 : Nat := 118140960795 + 2126844 * 2 ^ 59
def prefixEnd_2126844 : Nat := 4983230072969 + 3 ^ 40 * 2126844 * 2
def baseEnd_2126844 : Nat := 242687388695818210393073

theorem tailTrace_2126844 : CollatzResearch.WordTrace tailWord_2126844 prefixEnd_2126844 242687388695818210393073 := by
  unfold tailWord_2126844
  simp only [CollatzResearch.WordTrace]
  refine ⟨38786186753407449440805793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51714915671209932587741057 38786186753407449440805793)
  ·
    refine ⟨29089640065055587080604345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38786186753407449440805793 29089640065055587080604345)
    ·
      refine ⟨21817230048791690310453259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29089640065055587080604345 21817230048791690310453259)
      ·
        refine ⟨32725845073187535465679889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21817230048791690310453259 32725845073187535465679889)
        ·
          refine ⟨24544383804890651599259917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32725845073187535465679889 24544383804890651599259917)
          ·
            refine ⟨9204143926833994349722469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24544383804890651599259917 9204143926833994349722469)
            ·
              refine ⟨1725776986281373940572963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9204143926833994349722469 1725776986281373940572963)
              ·
                refine ⟨2588665479422060910859445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725776986281373940572963 2588665479422060910859445)
                ·
                  refine ⟨242687388695818210393073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2588665479422060910859445 242687388695818210393073)
                  ·
                    rfl

theorem cell22_2126844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_2126844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126844 prefixEnd_2126844 := by exact prefixLift 2126844
  have htrace : WordTrace (prefixWord ++ tailWord_2126844) baseStart_2126844 baseEnd_2126844 := by
    simpa [prefixWord, tailWord_2126844, baseEnd_2126844] using wordTrace_append hprefix tailTrace_2126844
  have hstable : (prefixWord ++ tailWord_2126844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126844).length < 2 ^ (prefixWord ++ tailWord_2126844).sum := by decide
  have hdescent : baseEnd_2126844 < baseStart_2126844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126904 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_2126904 : Nat := 118140960795 + 2126904 * 2 ^ 59
def prefixEnd_2126904 : Nat := 4983230072969 + 3 ^ 40 * 2126904 * 2
def baseEnd_2126904 : Nat := 728082705313634474679035

theorem tailTrace_2126904 : CollatzResearch.WordTrace tailWord_2126904 prefixEnd_2126904 728082705313634474679035 := by
  unfold tailWord_2126904
  simp only [CollatzResearch.WordTrace]
  refine ⟨38787280943298764564397883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51716374591065019419197177 38787280943298764564397883)
  ·
    refine ⟨58180921414948146846596825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38787280943298764564397883 58180921414948146846596825)
    ·
      refine ⟨43635691061211110134947619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58180921414948146846596825 43635691061211110134947619)
      ·
        refine ⟨65453536591816665202421429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43635691061211110134947619 65453536591816665202421429)
        ·
          refine ⟨6136269055482812362727009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65453536591816665202421429 6136269055482812362727009)
          ·
            refine ⟨4602201791612109272045257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6136269055482812362727009 4602201791612109272045257)
            ·
              refine ⟨3451651343709081954033943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602201791612109272045257 3451651343709081954033943)
              ·
                refine ⟨5177477015563622931050915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451651343709081954033943 5177477015563622931050915)
                ·
                  refine ⟨7766215523345434396576373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5177477015563622931050915 7766215523345434396576373)
                  ·
                    refine ⟨728082705313634474679035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7766215523345434396576373 728082705313634474679035)
                    ·
                      rfl

theorem cell22_2126904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_2126904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126904 prefixEnd_2126904 := by exact prefixLift 2126904
  have htrace : WordTrace (prefixWord ++ tailWord_2126904) baseStart_2126904 baseEnd_2126904 := by
    simpa [prefixWord, tailWord_2126904, baseEnd_2126904] using wordTrace_append hprefix tailTrace_2126904
  have hstable : (prefixWord ++ tailWord_2126904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126904).length < 2 ^ (prefixWord ++ tailWord_2126904).sum := by decide
  have hdescent : baseEnd_2126904 < baseStart_2126904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126919 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2126919 : Nat := 118140960795 + 2126919 * 2 ^ 59
def prefixEnd_2126919 : Nat := 4983230072969 + 3 ^ 40 * 2126919 * 2
def baseEnd_2126919 : Nat := 728087840120179435553989

theorem tailTrace_2126919 : CollatzResearch.WordTrace tailWord_2126919 prefixEnd_2126919 728087840120179435553989 := by
  unfold tailWord_2126919
  simp only [CollatzResearch.WordTrace]
  refine ⟨77575108981543186690591811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51716739321028791127061207 77575108981543186690591811)
  ·
    refine ⟨116362663472314780035887717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77575108981543186690591811 116362663472314780035887717)
    ·
      refine ⟨21817999401059021256728947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116362663472314780035887717 21817999401059021256728947)
      ·
        refine ⟨32726999101588531885093421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21817999401059021256728947 32726999101588531885093421)
        ·
          refine ⟨12272624663095699456910033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32726999101588531885093421 12272624663095699456910033)
          ·
            refine ⟨9204468497321774592682525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12272624663095699456910033 9204468497321774592682525)
            ·
              refine ⟨3451675686495665472255947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9204468497321774592682525 3451675686495665472255947)
              ·
                refine ⟨5177513529743498208383921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451675686495665472255947 5177513529743498208383921)
                ·
                  refine ⟨3883135147307623656287941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5177513529743498208383921 3883135147307623656287941)
                  ·
                    refine ⟨728087840120179435553989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883135147307623656287941 728087840120179435553989)
                    ·
                      rfl

theorem cell22_2126919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2126919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126919 prefixEnd_2126919 := by exact prefixLift 2126919
  have htrace : WordTrace (prefixWord ++ tailWord_2126919) baseStart_2126919 baseEnd_2126919 := by
    simpa [prefixWord, tailWord_2126919, baseEnd_2126919] using wordTrace_append hprefix tailTrace_2126919
  have hstable : (prefixWord ++ tailWord_2126919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126919).length < 2 ^ (prefixWord ++ tailWord_2126919).sum := by decide
  have hdescent : baseEnd_2126919 < baseStart_2126919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126966 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_2126966 : Nat := 118140960795 + 2126966 * 2 ^ 59
def prefixEnd_2126966 : Nat := 4983230072969 + 3 ^ 40 * 2126966 * 2
def baseEnd_2126966 : Nat := 728103929180686979628845

theorem tailTrace_2126966 : CollatzResearch.WordTrace tailWord_2126966 prefixEnd_2126966 728103929180686979628845 := by
  unfold tailWord_2126966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848551450773307107347047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51717882141581942478368501 4848551450773307107347047)
  ·
    refine ⟨7272827176159960661020571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4848551450773307107347047 7272827176159960661020571)
    ·
      refine ⟨10909240764239940991530857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7272827176159960661020571 10909240764239940991530857)
      ·
        refine ⟨8181930573179955743648143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10909240764239940991530857 8181930573179955743648143)
        ·
          refine ⟨12272895859769933615472215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8181930573179955743648143 12272895859769933615472215)
          ·
            refine ⟨18409343789654900423208323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12272895859769933615472215 18409343789654900423208323)
            ·
              refine ⟨27614015684482350634812485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18409343789654900423208323 27614015684482350634812485)
              ·
                refine ⟨5177627940840440744027341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27614015684482350634812485 5177627940840440744027341)
                ·
                  refine ⟨1941610477815165279010253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5177627940840440744027341 1941610477815165279010253)
                  ·
                    refine ⟨728103929180686979628845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941610477815165279010253 728103929180686979628845)
                    ·
                      rfl

theorem cell22_2126966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_2126966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126966 prefixEnd_2126966 := by exact prefixLift 2126966
  have htrace : WordTrace (prefixWord ++ tailWord_2126966) baseStart_2126966 baseEnd_2126966 := by
    simpa [prefixWord, tailWord_2126966, baseEnd_2126966] using wordTrace_append hprefix tailTrace_2126966
  have hstable : (prefixWord ++ tailWord_2126966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126966).length < 2 ^ (prefixWord ++ tailWord_2126966).sum := by decide
  have hdescent : baseEnd_2126966 < baseStart_2126966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126974 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2126974 : Nat := 118140960795 + 2126974 * 2 ^ 59
def prefixEnd_2126974 : Nat := 4983230072969 + 3 ^ 40 * 2126974 * 2
def baseEnd_2126974 : Nat := 242702222581392541809607

theorem tailTrace_2126974 : CollatzResearch.WordTrace tailWord_2126974 prefixEnd_2126974 242702222581392541809607 := by
  unfold tailWord_2126974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697139374542991385480497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51718076664229287389229317 9697139374542991385480497)
  ·
    refine ⟨7272854530907243539110373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9697139374542991385480497 7272854530907243539110373)
    ·
      refine ⟨1363660224545108163583195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7272854530907243539110373 1363660224545108163583195)
      ·
        refine ⟨2045490336817662245374793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363660224545108163583195 2045490336817662245374793)
        ·
          refine ⟨1534117752613246684031095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045490336817662245374793 1534117752613246684031095)
          ·
            refine ⟨2301176628919870026046643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534117752613246684031095 2301176628919870026046643)
            ·
              refine ⟨3451764943379805039069965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301176628919870026046643 3451764943379805039069965)
              ·
                refine ⟨1294411853767426889651237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3451764943379805039069965 1294411853767426889651237)
                ·
                  refine ⟨242702222581392541809607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294411853767426889651237 242702222581392541809607)
                  ·
                    rfl

theorem cell22_2126974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2126974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2126974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2126974 prefixEnd_2126974 := by exact prefixLift 2126974
  have htrace : WordTrace (prefixWord ++ tailWord_2126974) baseStart_2126974 baseEnd_2126974 := by
    simpa [prefixWord, tailWord_2126974, baseEnd_2126974] using wordTrace_append hprefix tailTrace_2126974
  have hstable : (prefixWord ++ tailWord_2126974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126974).length < 2 ^ (prefixWord ++ tailWord_2126974).sum := by decide
  have hdescent : baseEnd_2126974 < baseStart_2126974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127000 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 1, 3]
def baseStart_2127000 : Nat := 118140960795 + 2127000 * 2 ^ 59
def prefixEnd_2127000 : Nat := 4983230072969 + 3 ^ 40 * 2127000 * 2
def baseEnd_2127000 : Nat := 728115568075522224278741

theorem tailTrace_2127000 : CollatzResearch.WordTrace tailWord_2127000 prefixEnd_2127000 728115568075522224278741 := by
  unfold tailWord_2127000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38789031647124868762145227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51718708862833158349526969 38789031647124868762145227)
  ·
    refine ⟨58183547470687303143217841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38789031647124868762145227 58183547470687303143217841)
    ·
      refine ⟨43637660603015477357413381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58183547470687303143217841 43637660603015477357413381)
      ·
        refine ⟨8182061363065402004515009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43637660603015477357413381 8182061363065402004515009)
        ·
          refine ⟨6136546022299051503386257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8182061363065402004515009 6136546022299051503386257)
          ·
            refine ⟨4602409516724288627539693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6136546022299051503386257 4602409516724288627539693)
            ·
              refine ⟨1725903568771608235327385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4602409516724288627539693 1725903568771608235327385)
              ·
                refine ⟨1294427676578706176495539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725903568771608235327385 1294427676578706176495539)
                ·
                  refine ⟨1941641514868059264743309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294427676578706176495539 1941641514868059264743309)
                  ·
                    refine ⟨728115568075522224278741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941641514868059264743309 728115568075522224278741)
                    ·
                      rfl

theorem cell22_2127000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_2127000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127000 prefixEnd_2127000 := by exact prefixLift 2127000
  have htrace : WordTrace (prefixWord ++ tailWord_2127000) baseStart_2127000 baseEnd_2127000 := by
    simpa [prefixWord, tailWord_2127000, baseEnd_2127000] using wordTrace_append hprefix tailTrace_2127000
  have hstable : (prefixWord ++ tailWord_2127000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127000).length < 2 ^ (prefixWord ++ tailWord_2127000).sum := by decide
  have hdescent : baseEnd_2127000 < baseStart_2127000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127009 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2127009 : Nat := 118140960795 + 2127009 * 2 ^ 59
def prefixEnd_2127009 : Nat := 4983230072969 + 3 ^ 40 * 2127009 * 2
def baseEnd_2127009 : Nat := 728118648959449200803713

theorem tailTrace_2127009 : CollatzResearch.WordTrace tailWord_2127009 prefixEnd_2127009 728118648959449200803713 := by
  unfold tailWord_2127009
  simp only [CollatzResearch.WordTrace]
  refine ⟨77578391551217132061368081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51718927700811421374245387 77578391551217132061368081)
  ·
    refine ⟨58183793663412849046026061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77578391551217132061368081 58183793663412849046026061)
    ·
      refine ⟨21818922623779818392259773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58183793663412849046026061 21818922623779818392259773)
      ·
        refine ⟨8182095983917431897097415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21818922623779818392259773 8182095983917431897097415)
        ·
          refine ⟨12273143975876147845646123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8182095983917431897097415 12273143975876147845646123)
          ·
            refine ⟨18409715963814221768469185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12273143975876147845646123 18409715963814221768469185)
            ·
              refine ⟨13807286972860666326351889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18409715963814221768469185 13807286972860666326351889)
              ·
                refine ⟨10355465229645499744763917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13807286972860666326351889 10355465229645499744763917)
                ·
                  refine ⟨3883299461117062404286469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10355465229645499744763917 3883299461117062404286469)
                  ·
                    refine ⟨728118648959449200803713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883299461117062404286469 728118648959449200803713)
                    ·
                      rfl

theorem cell22_2127009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2127009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127009 prefixEnd_2127009 := by exact prefixLift 2127009
  have htrace : WordTrace (prefixWord ++ tailWord_2127009) baseStart_2127009 baseEnd_2127009 := by
    simpa [prefixWord, tailWord_2127009, baseEnd_2127009] using wordTrace_append hprefix tailTrace_2127009
  have hstable : (prefixWord ++ tailWord_2127009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127009).length < 2 ^ (prefixWord ++ tailWord_2127009).sum := by decide
  have hdescent : baseEnd_2127009 < baseStart_2127009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127026 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_2127026 : Nat := 118140960795 + 2127026 * 2 ^ 59
def prefixEnd_2127026 : Nat := 4983230072969 + 3 ^ 40 * 2127026 * 2
def baseEnd_2127026 : Nat := 728124468406866823128661

theorem tailTrace_2127026 : CollatzResearch.WordTrace tailWord_2127026 prefixEnd_2127026 728124468406866823128661 := by
  unfold tailWord_2127026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19394752898038885991184233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51719341061437029309824621 19394752898038885991184233)
  ·
    refine ⟨14546064673529164493388175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19394752898038885991184233 14546064673529164493388175)
    ·
      refine ⟨21819097010293746740082263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14546064673529164493388175 21819097010293746740082263)
      ·
        refine ⟨32728645515440620110123395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21819097010293746740082263 32728645515440620110123395)
        ·
          refine ⟨49092968273160930165185093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32728645515440620110123395 49092968273160930165185093)
          ·
            refine ⟨9204931551217674405972205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49092968273160930165185093 9204931551217674405972205)
            ·
              refine ⟨3451849331706627902239577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9204931551217674405972205 3451849331706627902239577)
              ·
                refine ⟨2588886998779970926679683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3451849331706627902239577 2588886998779970926679683)
                ·
                  refine ⟨3883330498169956390019525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588886998779970926679683 3883330498169956390019525)
                  ·
                    refine ⟨728124468406866823128661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883330498169956390019525 728124468406866823128661)
                    ·
                      rfl

theorem cell22_2127026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_2127026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127026 prefixEnd_2127026 := by exact prefixLift 2127026
  have htrace : WordTrace (prefixWord ++ tailWord_2127026) baseStart_2127026 baseEnd_2127026 := by
    simpa [prefixWord, tailWord_2127026, baseEnd_2127026] using wordTrace_append hprefix tailTrace_2127026
  have hstable : (prefixWord ++ tailWord_2127026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127026).length < 2 ^ (prefixWord ++ tailWord_2127026).sum := by decide
  have hdescent : baseEnd_2127026 < baseStart_2127026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127039 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 6, 3]
def baseStart_2127039 : Nat := 118140960795 + 2127039 * 2 ^ 59
def prefixEnd_2127039 : Nat := 4983230072969 + 3 ^ 40 * 2127039 * 2
def baseEnd_2127039 : Nat := 728128918572539122553621

theorem tailTrace_2127039 : CollatzResearch.WordTrace tailWord_2127039 prefixEnd_2127039 728128918572539122553621 := by
  unfold tailWord_2127039
  simp only [CollatzResearch.WordTrace]
  refine ⟨77579485741108447184960171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51719657160738964789973447 77579485741108447184960171)
  ·
    refine ⟨116369228611662670777440257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77579485741108447184960171 116369228611662670777440257)
    ·
      refine ⟨87276921458747003083080193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116369228611662670777440257 87276921458747003083080193)
      ·
        refine ⟨65457691094060252312310145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87276921458747003083080193 65457691094060252312310145)
        ·
          refine ⟨49093268320545189234232609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65457691094060252312310145 49093268320545189234232609)
          ·
            refine ⟨36819951240408891925674457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49093268320545189234232609 36819951240408891925674457)
            ·
              refine ⟨27614963430306668944255843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36819951240408891925674457 27614963430306668944255843)
              ·
                refine ⟨41422445145460003416383765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27614963430306668944255843 41422445145460003416383765)
                ·
                  refine ⟨1941677116193437660142989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41422445145460003416383765 1941677116193437660142989)
                  ·
                    refine ⟨728128918572539122553621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941677116193437660142989 728128918572539122553621)
                    ·
                      rfl

theorem cell22_2127039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_2127039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127039 prefixEnd_2127039 := by exact prefixLift 2127039
  have htrace : WordTrace (prefixWord ++ tailWord_2127039) baseStart_2127039 baseEnd_2127039 := by
    simpa [prefixWord, tailWord_2127039, baseEnd_2127039] using wordTrace_append hprefix tailTrace_2127039
  have hstable : (prefixWord ++ tailWord_2127039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127039).length < 2 ^ (prefixWord ++ tailWord_2127039).sum := by decide
  have hdescent : baseEnd_2127039 < baseStart_2127039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127052 : List Nat := [2, 2, 1, 17]
def baseStart_2127052 : Nat := 118140960795 + 2127052 * 2 ^ 59
def prefixEnd_2127052 : Nat := 4983230072969 + 3 ^ 40 * 2127052 * 2
def baseEnd_2127052 : Nat := 998811205402210455389

theorem tailTrace_2127052 : CollatzResearch.WordTrace tailWord_2127052 prefixEnd_2127052 998811205402210455389 := by
  unfold tailWord_2127052
  simp only [CollatzResearch.WordTrace]
  refine ⟨38789979945030675202591705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51719973260040900270122273 38789979945030675202591705)
  ·
    refine ⟨29092484958773006401943779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38789979945030675202591705 29092484958773006401943779)
    ·
      refine ⟨43638727438159509602915669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29092484958773006401943779 43638727438159509602915669)
      ·
        refine ⟨998811205402210455389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 43638727438159509602915669 998811205402210455389)
        ·
          rfl

theorem cell22_2127052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 17].length) (baseStart_2127052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127052 prefixEnd_2127052 := by exact prefixLift 2127052
  have htrace : WordTrace (prefixWord ++ tailWord_2127052) baseStart_2127052 baseEnd_2127052 := by
    simpa [prefixWord, tailWord_2127052, baseEnd_2127052] using wordTrace_append hprefix tailTrace_2127052
  have hstable : (prefixWord ++ tailWord_2127052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127052).length < 2 ^ (prefixWord ++ tailWord_2127052).sum := by decide
  have hdescent : baseEnd_2127052 < baseStart_2127052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127118 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2127118 : Nat := 118140960795 + 2127118 * 2 ^ 59
def prefixEnd_2127118 : Nat := 4983230072969 + 3 ^ 40 * 2127118 * 2
def baseEnd_2127118 : Nat := 728155961887009249828379

theorem tailTrace_2127118 : CollatzResearch.WordTrace tailWord_2127118 prefixEnd_2127118 728155961887009249828379 := by
  unfold tailWord_2127118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697795888477780459635751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51721578071881495784724005 9697795888477780459635751)
  ·
    refine ⟨14546693832716670689453627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9697795888477780459635751 14546693832716670689453627)
    ·
      refine ⟨21820040749075006034180441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14546693832716670689453627 21820040749075006034180441)
      ·
        refine ⟨16365030561806254525635331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21820040749075006034180441 16365030561806254525635331)
        ·
          refine ⟨24547545842709381788452997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16365030561806254525635331 24547545842709381788452997)
          ·
            refine ⟨4602664845508009085334937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24547545842709381788452997 4602664845508009085334937)
            ·
              refine ⟨3451998634131006814001203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602664845508009085334937 3451998634131006814001203)
              ·
                refine ⟨5177997951196510221001805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451998634131006814001203 5177997951196510221001805)
                ·
                  refine ⟨1941749231698691332875677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5177997951196510221001805 1941749231698691332875677)
                  ·
                    refine ⟨728155961887009249828379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941749231698691332875677 728155961887009249828379)
                    ·
                      rfl

theorem cell22_2127118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2127118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127118 prefixEnd_2127118 := by exact prefixLift 2127118
  have htrace : WordTrace (prefixWord ++ tailWord_2127118) baseStart_2127118 baseEnd_2127118 := by
    simpa [prefixWord, tailWord_2127118, baseEnd_2127118] using wordTrace_append hprefix tailTrace_2127118
  have hstable : (prefixWord ++ tailWord_2127118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127118).length < 2 ^ (prefixWord ++ tailWord_2127118).sum := by decide
  have hdescent : baseEnd_2127118 < baseStart_2127118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127208 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2127208 : Nat := 118140960795 + 2127208 * 2 ^ 59
def prefixEnd_2127208 : Nat := 4983230072969 + 3 ^ 40 * 2127208 * 2
def baseEnd_2127208 : Nat := 728186770726279015078103

theorem tailTrace_2127208 : CollatzResearch.WordTrace tailWord_2127208 prefixEnd_2127208 728186770726279015078103 := by
  unfold tailWord_2127208
  simp only [CollatzResearch.WordTrace]
  refine ⟨38792824838748094523931139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51723766451664126031908185 38792824838748094523931139)
  ·
    refine ⟨58189237258122141785896709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38792824838748094523931139 58189237258122141785896709)
    ·
      refine ⟨10910481985897901584855633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58189237258122141785896709 10910481985897901584855633)
      ·
        refine ⟨8182861489423426188641725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10910481985897901584855633 8182861489423426188641725)
        ·
          refine ⟨3068573058533784820740647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8182861489423426188641725 3068573058533784820740647)
          ·
            refine ⟨4602859587800677231110971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3068573058533784820740647 4602859587800677231110971)
            ·
              refine ⟨6904289381701015846666457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4602859587800677231110971 6904289381701015846666457)
              ·
                refine ⟨5178217036275761884999843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904289381701015846666457 5178217036275761884999843)
                ·
                  refine ⟨7767325554413642827499765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178217036275761884999843 7767325554413642827499765)
                  ·
                    refine ⟨728186770726279015078103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7767325554413642827499765 728186770726279015078103)
                    ·
                      rfl

theorem cell22_2127208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2127208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127208 prefixEnd_2127208 := by exact prefixLift 2127208
  have htrace : WordTrace (prefixWord ++ tailWord_2127208) baseStart_2127208 baseEnd_2127208 := by
    simpa [prefixWord, tailWord_2127208, baseEnd_2127208] using wordTrace_append hprefix tailTrace_2127208
  have hstable : (prefixWord ++ tailWord_2127208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127208).length < 2 ^ (prefixWord ++ tailWord_2127208).sum := by decide
  have hdescent : baseEnd_2127208 < baseStart_2127208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127221 : List Nat := [1, 3, 4, 1, 3, 10]
def baseStart_2127221 : Nat := 118140960795 + 2127221 * 2 ^ 59
def prefixEnd_2127221 : Nat := 4983230072969 + 3 ^ 40 * 2127221 * 2
def baseEnd_2127221 : Nat := 8990015072740139685223

theorem tailTrace_2127221 : CollatzResearch.WordTrace tailWord_2127221 prefixEnd_2127221 8990015072740139685223 := by
  unfold tailWord_2127221
  simp only [CollatzResearch.WordTrace]
  refine ⟨77586123826449092268085517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51724082550966061512057011 77586123826449092268085517)
  ·
    refine ⟨29094796434918409600532069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77586123826449092268085517 29094796434918409600532069)
    ·
      refine ⟨5455274331547201800099763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29094796434918409600532069 5455274331547201800099763)
      ·
        refine ⟨8182911497320802700149645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5455274331547201800099763 8182911497320802700149645)
        ·
          refine ⟨3068591811495301012556117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8182911497320802700149645 3068591811495301012556117)
          ·
            refine ⟨8990015072740139685223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3068591811495301012556117 8990015072740139685223)
            ·
              rfl

theorem cell22_2127221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 10].length) (baseStart_2127221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127221 prefixEnd_2127221 := by exact prefixLift 2127221
  have htrace : WordTrace (prefixWord ++ tailWord_2127221) baseStart_2127221 baseEnd_2127221 := by
    simpa [prefixWord, tailWord_2127221, baseEnd_2127221] using wordTrace_append hprefix tailTrace_2127221
  have hstable : (prefixWord ++ tailWord_2127221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127221).length < 2 ^ (prefixWord ++ tailWord_2127221).sum := by decide
  have hdescent : baseEnd_2127221 < baseStart_2127221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127281 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2127281 : Nat := 118140960795 + 2127281 * 2 ^ 59
def prefixEnd_2127281 : Nat := 4983230072969 + 3 ^ 40 * 2127281 * 2
def baseEnd_2127281 : Nat := 728211760118131158002879

theorem tailTrace_2127281 : CollatzResearch.WordTrace tailWord_2127281 prefixEnd_2127281 728211760118131158002879 := by
  unfold tailWord_2127281
  simp only [CollatzResearch.WordTrace]
  refine ⟨77588312206231722515269697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51725541470821148343513131 77588312206231722515269697)
  ·
    refine ⟨58191234154673791886452273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77588312206231722515269697 58191234154673791886452273)
    ·
      refine ⟨43643425616005343914839205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58191234154673791886452273 43643425616005343914839205)
      ·
        refine ⟨8183142303001001984032351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43643425616005343914839205 8183142303001001984032351)
        ·
          refine ⟨12274713454501502976048527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8183142303001001984032351 12274713454501502976048527)
          ·
            refine ⟨18412070181752254464072791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12274713454501502976048527 18412070181752254464072791)
            ·
              refine ⟨27618105272628381696109187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18412070181752254464072791 27618105272628381696109187)
              ·
                refine ⟨41427157908942572544163781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27618105272628381696109187 41427157908942572544163781)
                ·
                  refine ⟨7767592107926732352030709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41427157908942572544163781 7767592107926732352030709)
                  ·
                    refine ⟨728211760118131158002879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7767592107926732352030709 728211760118131158002879)
                    ·
                      rfl

theorem cell22_2127281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2127281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127281 prefixEnd_2127281 := by exact prefixLift 2127281
  have htrace : WordTrace (prefixWord ++ tailWord_2127281) baseStart_2127281 baseEnd_2127281 := by
    simpa [prefixWord, tailWord_2127281, baseEnd_2127281] using wordTrace_append hprefix tailTrace_2127281
  have hstable : (prefixWord ++ tailWord_2127281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127281).length < 2 ^ (prefixWord ++ tailWord_2127281).sum := by decide
  have hdescent : baseEnd_2127281 < baseStart_2127281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127296 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_2127296 : Nat := 118140960795 + 2127296 * 2 ^ 59
def prefixEnd_2127296 : Nat := 4983230072969 + 3 ^ 40 * 2127296 * 2
def baseEnd_2127296 : Nat := 728216894924676118877833

theorem tailTrace_2127296 : CollatzResearch.WordTrace tailWord_2127296 prefixEnd_2127296 728216894924676118877833 := by
  unfold tailWord_2127296
  simp only [CollatzResearch.WordTrace]
  refine ⟨38794429650588690038532871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51725906200784920051377161 38794429650588690038532871)
  ·
    refine ⟨58191644475883035057799307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38794429650588690038532871 58191644475883035057799307)
    ·
      refine ⟨87287466713824552586698961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58191644475883035057799307 87287466713824552586698961)
      ·
        refine ⟨65465600035368414440024221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87287466713824552586698961 65465600035368414440024221)
        ·
          refine ⟨24549600013263155415009083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65465600035368414440024221 24549600013263155415009083)
          ·
            refine ⟨36824400019894733122513625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24549600013263155415009083 36824400019894733122513625)
            ·
              refine ⟨27618300014921049841885219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36824400019894733122513625 27618300014921049841885219)
              ·
                refine ⟨41427450022381574762827829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27618300014921049841885219 41427450022381574762827829)
                ·
                  refine ⟨3883823439598272634015109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41427450022381574762827829 3883823439598272634015109)
                  ·
                    refine ⟨728216894924676118877833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883823439598272634015109 728216894924676118877833)
                    ·
                      rfl

theorem cell22_2127296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_2127296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127296 prefixEnd_2127296 := by exact prefixLift 2127296
  have htrace : WordTrace (prefixWord ++ tailWord_2127296) baseStart_2127296 baseEnd_2127296 := by
    simpa [prefixWord, tailWord_2127296, baseEnd_2127296] using wordTrace_append hprefix tailTrace_2127296
  have hstable : (prefixWord ++ tailWord_2127296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127296).length < 2 ^ (prefixWord ++ tailWord_2127296).sum := by decide
  have hdescent : baseEnd_2127296 < baseStart_2127296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127311 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 6]
def baseStart_2127311 : Nat := 118140960795 + 2127311 * 2 ^ 59
def prefixEnd_2127311 : Nat := 4983230072969 + 3 ^ 40 * 2127311 * 2
def baseEnd_2127311 : Nat := 242740676577073693250929

theorem tailTrace_2127311 : CollatzResearch.WordTrace tailWord_2127311 prefixEnd_2127311 242740676577073693250929 := by
  unfold tailWord_2127311
  simp only [CollatzResearch.WordTrace]
  refine ⟨77589406396123037638861787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51726270930748691759241191 77589406396123037638861787)
  ·
    refine ⟨116384109594184556458292681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77589406396123037638861787 116384109594184556458292681)
    ·
      refine ⟨87288082195638417343719511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116384109594184556458292681 87288082195638417343719511)
      ·
        refine ⟨130932123293457626015579267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87288082195638417343719511 130932123293457626015579267)
        ·
          refine ⟨196398184940186439023368901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130932123293457626015579267 196398184940186439023368901)
          ·
            refine ⟨36824659676284957316881669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196398184940186439023368901 36824659676284957316881669)
            ·
              refine ⟨6904623689303429496915313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36824659676284957316881669 6904623689303429496915313)
              ·
                refine ⟨5178467766977572122686485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904623689303429496915313 5178467766977572122686485)
                ·
                  refine ⟨242740676577073693250929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5178467766977572122686485 242740676577073693250929)
                  ·
                    rfl

theorem cell22_2127311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 6].length) (baseStart_2127311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127311 prefixEnd_2127311 := by exact prefixLift 2127311
  have htrace : WordTrace (prefixWord ++ tailWord_2127311) baseStart_2127311 baseEnd_2127311 := by
    simpa [prefixWord, tailWord_2127311, baseEnd_2127311] using wordTrace_append hprefix tailTrace_2127311
  have hstable : (prefixWord ++ tailWord_2127311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127311).length < 2 ^ (prefixWord ++ tailWord_2127311).sum := by decide
  have hdescent : baseEnd_2127311 < baseStart_2127311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127328 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 4]
def baseStart_2127328 : Nat := 118140960795 + 2127328 * 2 ^ 59
def prefixEnd_2127328 : Nat := 4983230072969 + 3 ^ 40 * 2127328 * 2
def baseEnd_2127328 : Nat := 242742616392879567359245

theorem tailTrace_2127328 : CollatzResearch.WordTrace tailWord_2127328 prefixEnd_2127328 242742616392879567359245 := by
  unfold tailWord_2127328
  simp only [CollatzResearch.WordTrace]
  refine ⟨38795013218530724771115319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51726684291374299694820425 38795013218530724771115319)
  ·
    refine ⟨58192519827796087156672979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38795013218530724771115319 58192519827796087156672979)
    ·
      refine ⟨87288779741694130735009469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58192519827796087156672979 87288779741694130735009469)
      ·
        refine ⟨32733292403135299025628551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87288779741694130735009469 32733292403135299025628551)
        ·
          refine ⟨49099938604702948538442827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32733292403135299025628551 49099938604702948538442827)
          ·
            refine ⟨73649907907054422807664241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49099938604702948538442827 73649907907054422807664241)
            ·
              refine ⟨55237430930290817105748181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73649907907054422807664241 55237430930290817105748181)
              ·
                refine ⟨1294627287428691025915973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55237430930290817105748181 1294627287428691025915973)
                ·
                  refine ⟨242742616392879567359245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294627287428691025915973 242742616392879567359245)
                  ·
                    rfl

theorem cell22_2127328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_2127328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127328 prefixEnd_2127328 := by exact prefixLift 2127328
  have htrace : WordTrace (prefixWord ++ tailWord_2127328) baseStart_2127328 baseEnd_2127328 := by
    simpa [prefixWord, tailWord_2127328, baseEnd_2127328] using wordTrace_append hprefix tailTrace_2127328
  have hstable : (prefixWord ++ tailWord_2127328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127328).length < 2 ^ (prefixWord ++ tailWord_2127328).sum := by decide
  have hdescent : baseEnd_2127328 < baseStart_2127328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127343 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 4, 3]
def baseStart_2127343 : Nat := 118140960795 + 2127343 * 2 ^ 59
def prefixEnd_2127343 : Nat := 4983230072969 + 3 ^ 40 * 2127343 * 2
def baseEnd_2127343 : Nat := 728232983985183662952689

theorem tailTrace_2127343 : CollatzResearch.WordTrace tailWord_2127343 prefixEnd_2127343 728232983985183662952689 := by
  unfold tailWord_2127343
  simp only [CollatzResearch.WordTrace]
  refine ⟨77590573532007107104026683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51727049021338071402684455 77590573532007107104026683)
  ·
    refine ⟨116385860298010660656040025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77590573532007107104026683 116385860298010660656040025)
    ·
      refine ⟨87289395223507995492030019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116385860298010660656040025 87289395223507995492030019)
      ·
        refine ⟨130934092835261993238045029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87289395223507995492030019 130934092835261993238045029)
        ·
          refine ⟨24550142406611623732133443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130934092835261993238045029 24550142406611623732133443)
          ·
            refine ⟨36825213609917435598200165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24550142406611623732133443 36825213609917435598200165)
            ·
              refine ⟨6904727551859519174662531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36825213609917435598200165 6904727551859519174662531)
              ·
                refine ⟨10357091327789278761993797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6904727551859519174662531 10357091327789278761993797)
                ·
                  refine ⟨1941954623960489767873837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10357091327789278761993797 1941954623960489767873837)
                  ·
                    refine ⟨728232983985183662952689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941954623960489767873837 728232983985183662952689)
                    ·
                      rfl

theorem cell22_2127343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_2127343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127343 prefixEnd_2127343 := by exact prefixLift 2127343
  have htrace : WordTrace (prefixWord ++ tailWord_2127343) baseStart_2127343 baseEnd_2127343 := by
    simpa [prefixWord, tailWord_2127343, baseEnd_2127343] using wordTrace_append hprefix tailTrace_2127343
  have hstable : (prefixWord ++ tailWord_2127343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127343).length < 2 ^ (prefixWord ++ tailWord_2127343).sum := by decide
  have hdescent : baseEnd_2127343 < baseStart_2127343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127356 : List Nat := [2, 2, 2, 1, 2, 1, 3, 9]
def baseStart_2127356 : Nat := 118140960795 + 2127356 * 2 ^ 59
def prefixEnd_2127356 : Nat := 4983230072969 + 3 ^ 40 * 2127356 * 2
def baseEnd_2127356 : Nat := 80915270461206218041961

theorem tailTrace_2127356 : CollatzResearch.WordTrace tailWord_2127356 prefixEnd_2127356 80915270461206218041961 := by
  unfold tailWord_2127356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38795523840480005162124961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51727365120640006882833281 38795523840480005162124961)
  ·
    refine ⟨29096642880360003871593721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38795523840480005162124961 29096642880360003871593721)
    ·
      refine ⟨21822482160270002903695291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29096642880360003871593721 21822482160270002903695291)
      ·
        refine ⟨32733723240405004355542937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21822482160270002903695291 32733723240405004355542937)
        ·
          refine ⟨24550292430303753266657203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32733723240405004355542937 24550292430303753266657203)
          ·
            refine ⟨36825438645455629899985805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24550292430303753266657203 36825438645455629899985805)
            ·
              refine ⟨13809539492045861212494677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36825438645455629899985805 13809539492045861212494677)
              ·
                refine ⟨80915270461206218041961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13809539492045861212494677 80915270461206218041961)
                ·
                  rfl

theorem cell22_2127356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_2127356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127356 prefixEnd_2127356 := by exact prefixLift 2127356
  have htrace : WordTrace (prefixWord ++ tailWord_2127356) baseStart_2127356 baseEnd_2127356 := by
    simpa [prefixWord, tailWord_2127356, baseEnd_2127356] using wordTrace_append hprefix tailTrace_2127356
  have hstable : (prefixWord ++ tailWord_2127356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127356).length < 2 ^ (prefixWord ++ tailWord_2127356).sum := by decide
  have hdescent : baseEnd_2127356 < baseStart_2127356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127364 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2127364 : Nat := 118140960795 + 2127364 * 2 ^ 59
def prefixEnd_2127364 : Nat := 4983230072969 + 3 ^ 40 * 2127364 * 2
def baseEnd_2127364 : Nat := 728240172714346608177625

theorem tailTrace_2127364 : CollatzResearch.WordTrace tailWord_2127364 prefixEnd_2127364 728240172714346608177625 := by
  unfold tailWord_2127364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38795669732465513845270573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51727559643287351793694097 38795669732465513845270573)
  ·
    refine ⟨14548376149674567691976465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38795669732465513845270573 14548376149674567691976465)
    ·
      refine ⟨10911282112255925768982349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14548376149674567691976465 10911282112255925768982349)
      ·
        refine ⟨4091730792095972163368381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10911282112255925768982349 4091730792095972163368381)
        ·
          refine ⟨1534399047035989561263143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4091730792095972163368381 1534399047035989561263143)
          ·
            refine ⟨2301598570553984341894715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534399047035989561263143 2301598570553984341894715)
            ·
              refine ⟨3452397855830976512842073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301598570553984341894715 3452397855830976512842073)
              ·
                refine ⟨2589298391873232384631555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452397855830976512842073 2589298391873232384631555)
                ·
                  refine ⟨3883947587809848576947333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589298391873232384631555 3883947587809848576947333)
                  ·
                    refine ⟨728240172714346608177625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883947587809848576947333 728240172714346608177625)
                    ·
                      rfl

theorem cell22_2127364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2127364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127364 prefixEnd_2127364 := by exact prefixLift 2127364
  have htrace : WordTrace (prefixWord ++ tailWord_2127364) baseStart_2127364 baseEnd_2127364 := by
    simpa [prefixWord, tailWord_2127364, baseEnd_2127364] using wordTrace_append hprefix tailTrace_2127364
  have hstable : (prefixWord ++ tailWord_2127364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127364).length < 2 ^ (prefixWord ++ tailWord_2127364).sum := by decide
  have hdescent : baseEnd_2127364 < baseStart_2127364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127418 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_2127418 : Nat := 118140960795 + 2127418 * 2 ^ 59
def prefixEnd_2127418 : Nat := 4983230072969 + 3 ^ 40 * 2127418 * 2
def baseEnd_2127418 : Nat := 242752886005969489109153

theorem tailTrace_2127418 : CollatzResearch.WordTrace tailWord_2127418 prefixEnd_2127418 242752886005969489109153 := by
  unfold tailWord_2127418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19398327251683848728251727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51728872671156929942004605 19398327251683848728251727)
  ·
    refine ⟨29097490877525773092377591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19398327251683848728251727 29097490877525773092377591)
    ·
      refine ⟨43646236316288659638566387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29097490877525773092377591 43646236316288659638566387)
      ·
        refine ⟨65469354474432989457849581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43646236316288659638566387 65469354474432989457849581)
        ·
          refine ⟨24551007927912371046693593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65469354474432989457849581 24551007927912371046693593)
          ·
            refine ⟨18413255945934278285020195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24551007927912371046693593 18413255945934278285020195)
            ·
              refine ⟨27619883918901417427530293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18413255945934278285020195 27619883918901417427530293)
              ·
                refine ⟨2589364117397007883830965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27619883918901417427530293 2589364117397007883830965)
                ·
                  refine ⟨242752886005969489109153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2589364117397007883830965 242752886005969489109153)
                  ·
                    rfl

theorem cell22_2127418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_2127418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127418 prefixEnd_2127418 := by exact prefixLift 2127418
  have htrace : WordTrace (prefixWord ++ tailWord_2127418) baseStart_2127418 baseEnd_2127418 := by
    simpa [prefixWord, tailWord_2127418, baseEnd_2127418] using wordTrace_append hprefix tailTrace_2127418
  have hstable : (prefixWord ++ tailWord_2127418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127418).length < 2 ^ (prefixWord ++ tailWord_2127418).sum := by decide
  have hdescent : baseEnd_2127418 < baseStart_2127418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127452 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 5]
def baseStart_2127452 : Nat := 118140960795 + 2127452 * 2 ^ 59
def prefixEnd_2127452 : Nat := 4983230072969 + 3 ^ 40 * 2127452 * 2
def baseEnd_2127452 : Nat := 242756765637581237325785

theorem tailTrace_2127452 : CollatzResearch.WordTrace tailWord_2127452 prefixEnd_2127452 242756765637581237325785 := by
  unfold tailWord_2127452
  simp only [CollatzResearch.WordTrace]
  refine ⟨38797274544306109359872305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51729699392408145813163073 38797274544306109359872305)
  ·
    refine ⟨29097955908229582019904229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38797274544306109359872305 29097955908229582019904229)
    ·
      refine ⟨5455866732793046628732043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29097955908229582019904229 5455866732793046628732043)
      ·
        refine ⟨8183800099189569943098065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5455866732793046628732043 8183800099189569943098065)
        ·
          refine ⟨6137850074392177457323549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8183800099189569943098065 6137850074392177457323549)
          ·
            refine ⟨2301693777897066546496331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6137850074392177457323549 2301693777897066546496331)
            ·
              refine ⟨3452540666845599819744497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301693777897066546496331 3452540666845599819744497)
              ·
                refine ⟨2589405500134199864808373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452540666845599819744497 2589405500134199864808373)
                ·
                  refine ⟨242756765637581237325785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2589405500134199864808373 242756765637581237325785)
                  ·
                    rfl

theorem cell22_2127452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_2127452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127452 prefixEnd_2127452 := by exact prefixLift 2127452
  have htrace : WordTrace (prefixWord ++ tailWord_2127452) baseStart_2127452 baseEnd_2127452 := by
    simpa [prefixWord, tailWord_2127452, baseEnd_2127452] using wordTrace_append hprefix tailTrace_2127452
  have hstable : (prefixWord ++ tailWord_2127452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127452).length < 2 ^ (prefixWord ++ tailWord_2127452).sum := by decide
  have hdescent : baseEnd_2127452 < baseStart_2127452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127463 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 6]
def baseStart_2127463 : Nat := 118140960795 + 2127463 * 2 ^ 59
def prefixEnd_2127463 : Nat := 4983230072969 + 3 ^ 40 * 2127463 * 2
def baseEnd_2127463 : Nat := 242758020812514449984107

theorem tailTrace_2127463 : CollatzResearch.WordTrace tailWord_2127463 prefixEnd_2127463 242758020812514449984107 := by
  unfold tailWord_2127463
  simp only [CollatzResearch.WordTrace]
  refine ⟨77594950291572367598395043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51729966861048245065596695 77594950291572367598395043)
  ·
    refine ⟨116392425437358551397592565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77594950291572367598395043 116392425437358551397592565)
    ·
      refine ⟨10911789884752364193524303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116392425437358551397592565 10911789884752364193524303)
      ·
        refine ⟨16367684827128546290286455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10911789884752364193524303 16367684827128546290286455)
        ·
          refine ⟨24551527240692819435429683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16367684827128546290286455 24551527240692819435429683)
          ·
            refine ⟨36827290861039229153144525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24551527240692819435429683 36827290861039229153144525)
            ·
              refine ⟨13810234072889710932429197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36827290861039229153144525 13810234072889710932429197)
              ·
                refine ⟨5178837777333641599660949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13810234072889710932429197 5178837777333641599660949)
                ·
                  refine ⟨242758020812514449984107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5178837777333641599660949 242758020812514449984107)
                  ·
                    rfl

theorem cell22_2127463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 6].length) (baseStart_2127463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127463 prefixEnd_2127463 := by exact prefixLift 2127463
  have htrace : WordTrace (prefixWord ++ tailWord_2127463) baseStart_2127463 baseEnd_2127463 := by
    simpa [prefixWord, tailWord_2127463, baseEnd_2127463] using wordTrace_append hprefix tailTrace_2127463
  have hstable : (prefixWord ++ tailWord_2127463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127463).length < 2 ^ (prefixWord ++ tailWord_2127463).sum := by decide
  have hdescent : baseEnd_2127463 < baseStart_2127463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127493 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_2127493 : Nat := 118140960795 + 2127493 * 2 ^ 59
def prefixEnd_2127493 : Nat := 4983230072969 + 3 ^ 40 * 2127493 * 2
def baseEnd_2127493 : Nat := 728284332050633271702229

theorem tailTrace_2127493 : CollatzResearch.WordTrace tailWord_2127493 prefixEnd_2127493 728284332050633271702229 := by
  unfold tailWord_2127493
  simp only [CollatzResearch.WordTrace]
  refine ⟨77596044481463682721987133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51730696320975788481324755 77596044481463682721987133)
  ·
    refine ⟨29098516680548881020745175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77596044481463682721987133 29098516680548881020745175)
    ·
      refine ⟨43647775020823321531117763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29098516680548881020745175 43647775020823321531117763)
      ·
        refine ⟨65471662531234982296676645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43647775020823321531117763 65471662531234982296676645)
        ·
          refine ⟨12275936724606559180626871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65471662531234982296676645 12275936724606559180626871)
          ·
            refine ⟨18413905086909838770940307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12275936724606559180626871 18413905086909838770940307)
            ·
              refine ⟨27620857630364758156410461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18413905086909838770940307 27620857630364758156410461)
              ·
                refine ⟨10357821611386784308653923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27620857630364758156410461 10357821611386784308653923)
                ·
                  refine ⟨15536732417080176462980885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10357821611386784308653923 15536732417080176462980885)
                  ·
                    refine ⟨728284332050633271702229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15536732417080176462980885 728284332050633271702229)
                    ·
                      rfl

theorem cell22_2127493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_2127493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127493 prefixEnd_2127493 := by exact prefixLift 2127493
  have htrace : WordTrace (prefixWord ++ tailWord_2127493) baseStart_2127493 baseEnd_2127493 := by
    simpa [prefixWord, tailWord_2127493, baseEnd_2127493] using wordTrace_append hprefix tailTrace_2127493
  have hstable : (prefixWord ++ tailWord_2127493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127493).length < 2 ^ (prefixWord ++ tailWord_2127493).sum := by decide
  have hdescent : baseEnd_2127493 < baseStart_2127493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127495 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 4, 3]
def baseStart_2127495 : Nat := 118140960795 + 2127495 * 2 ^ 59
def prefixEnd_2127495 : Nat := 4983230072969 + 3 ^ 40 * 2127495 * 2
def baseEnd_2127495 : Nat := 728285016691505933152223

theorem tailTrace_2127495 : CollatzResearch.WordTrace tailWord_2127495 prefixEnd_2127495 728285016691505933152223 := by
  unfold tailWord_2127495
  simp only [CollatzResearch.WordTrace]
  refine ⟨77596117427456437063559939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51730744951637624709039959 77596117427456437063559939)
  ·
    refine ⟨116394176141184655595339909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77596117427456437063559939 116394176141184655595339909)
    ·
      refine ⟨21823908026472122924126233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116394176141184655595339909 21823908026472122924126233)
      ·
        refine ⟨16367931019854092193094675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21823908026472122924126233 16367931019854092193094675)
        ·
          refine ⟨24551896529781138289642013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16367931019854092193094675 24551896529781138289642013)
          ·
            refine ⟨9206961198667926858615755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24551896529781138289642013 9206961198667926858615755)
            ·
              refine ⟨13810441798001890287923633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9206961198667926858615755 13810441798001890287923633)
              ·
                refine ⟨10357831348501417715942725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13810441798001890287923633 10357831348501417715942725)
                ·
                  refine ⟨1942093377844015821739261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10357831348501417715942725 1942093377844015821739261)
                  ·
                    refine ⟨728285016691505933152223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942093377844015821739261 728285016691505933152223)
                    ·
                      rfl

theorem cell22_2127495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_2127495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127495 prefixEnd_2127495 := by exact prefixLift 2127495
  have htrace : WordTrace (prefixWord ++ tailWord_2127495) baseStart_2127495 baseEnd_2127495 := by
    simpa [prefixWord, tailWord_2127495, baseEnd_2127495] using wordTrace_append hprefix tailTrace_2127495
  have hstable : (prefixWord ++ tailWord_2127495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127495).length < 2 ^ (prefixWord ++ tailWord_2127495).sum := by decide
  have hdescent : baseEnd_2127495 < baseStart_2127495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127542 : List Nat := [5, 1, 3, 1, 1, 1, 2, 8]
def baseStart_2127542 : Nat := 118140960795 + 2127542 * 2 ^ 59
def prefixEnd_2127542 : Nat := 4983230072969 + 3 ^ 40 * 2127542 * 2
def baseEnd_2127542 : Nat := 80922345083557053025231

theorem tailTrace_2127542 : CollatzResearch.WordTrace tailWord_2127542 prefixEnd_2127542 80922345083557053025231 := by
  unfold tailWord_2127542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849864478642885255657555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51731887772190776060347253 4849864478642885255657555)
  ·
    refine ⟨7274796717964327883486333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4849864478642885255657555 7274796717964327883486333)
    ·
      refine ⟨2728048769236622956307375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7274796717964327883486333 2728048769236622956307375)
      ·
        refine ⟨4092073153854934434461063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728048769236622956307375 4092073153854934434461063)
        ·
          refine ⟨6138109730782401651691595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092073153854934434461063 6138109730782401651691595)
          ·
            refine ⟨9207164596173602477537393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6138109730782401651691595 9207164596173602477537393)
            ·
              refine ⟨6905373447130201858153045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9207164596173602477537393 6905373447130201858153045)
              ·
                refine ⟨80922345083557053025231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6905373447130201858153045 80922345083557053025231)
                ·
                  rfl

theorem cell22_2127542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_2127542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127542 prefixEnd_2127542 := by exact prefixLift 2127542
  have htrace : WordTrace (prefixWord ++ tailWord_2127542) baseStart_2127542 baseEnd_2127542 := by
    simpa [prefixWord, tailWord_2127542, baseEnd_2127542] using wordTrace_append hprefix tailTrace_2127542
  have hstable : (prefixWord ++ tailWord_2127542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127542).length < 2 ^ (prefixWord ++ tailWord_2127542).sum := by decide
  have hdescent : baseEnd_2127542 < baseStart_2127542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127630 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2127630 : Nat := 118140960795 + 2127630 * 2 ^ 59
def prefixEnd_2127630 : Nat := 4983230072969 + 3 ^ 40 * 2127630 * 2
def baseEnd_2127630 : Nat := 728331229950410581026809

theorem tailTrace_2127630 : CollatzResearch.WordTrace tailWord_2127630 prefixEnd_2127630 728331229950410581026809 := by
  unfold tailWord_2127630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700130160245919389965543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51734027521311570079816229 9700130160245919389965543)
  ·
    refine ⟨14550195240368879084948315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700130160245919389965543 14550195240368879084948315)
    ·
      refine ⟨21825292860553318627422473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14550195240368879084948315 21825292860553318627422473)
      ·
        refine ⟨16368969645414988970566855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21825292860553318627422473 16368969645414988970566855)
        ·
          refine ⟨24553454468122483455850283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16368969645414988970566855 24553454468122483455850283)
          ·
            refine ⟨36830181702183725183775425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24553454468122483455850283 36830181702183725183775425)
            ·
              refine ⟨27622636276637793887831569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36830181702183725183775425 27622636276637793887831569)
              ·
                refine ⟨20716977207478345415873677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27622636276637793887831569 20716977207478345415873677)
                ·
                  refine ⟨7768866452804379530952629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20716977207478345415873677 7768866452804379530952629)
                  ·
                    refine ⟨728331229950410581026809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7768866452804379530952629 728331229950410581026809)
                    ·
                      rfl

theorem cell22_2127630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2127630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127630 prefixEnd_2127630 := by exact prefixLift 2127630
  have htrace : WordTrace (prefixWord ++ tailWord_2127630) baseStart_2127630 baseEnd_2127630 := by
    simpa [prefixWord, tailWord_2127630, baseEnd_2127630] using wordTrace_append hprefix tailTrace_2127630
  have hstable : (prefixWord ++ tailWord_2127630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127630).length < 2 ^ (prefixWord ++ tailWord_2127630).sum := by decide
  have hdescent : baseEnd_2127630 < baseStart_2127630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127660 : List Nat := [2, 2, 1, 1, 1, 6, 1, 8]
def baseStart_2127660 : Nat := 118140960795 + 2127660 * 2 ^ 59
def prefixEnd_2127660 : Nat := 4983230072969 + 3 ^ 40 * 2127660 * 2
def baseEnd_2127660 : Nat := 80926833284833389197413

theorem tailTrace_2127660 : CollatzResearch.WordTrace tailWord_2127660 prefixEnd_2127660 80926833284833389197413 := by
  unfold tailWord_2127660
  simp only [CollatzResearch.WordTrace]
  refine ⟨38801067735929335121658217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51734756981239113495544289 38801067735929335121658217)
  ·
    refine ⟨29100800801947001341243663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38801067735929335121658217 29100800801947001341243663)
    ·
      refine ⟨43651201202920502011865495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29100800801947001341243663 43651201202920502011865495)
      ·
        refine ⟨65476801804380753017798243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43651201202920502011865495 65476801804380753017798243)
        ·
          refine ⟨98215202706571129526697365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65476801804380753017798243 98215202706571129526697365)
          ·
            refine ⟨4603837626870521696563939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98215202706571129526697365 4603837626870521696563939)
            ·
              refine ⟨6905756440305782544845909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603837626870521696563939 6905756440305782544845909)
              ·
                refine ⟨80926833284833389197413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6905756440305782544845909 80926833284833389197413)
                ·
                  rfl

theorem cell22_2127660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_2127660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127660 prefixEnd_2127660 := by exact prefixLift 2127660
  have htrace : WordTrace (prefixWord ++ tailWord_2127660) baseStart_2127660 baseEnd_2127660 := by
    simpa [prefixWord, tailWord_2127660, baseEnd_2127660] using wordTrace_append hprefix tailTrace_2127660
  have hstable : (prefixWord ++ tailWord_2127660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127660).length < 2 ^ (prefixWord ++ tailWord_2127660).sum := by decide
  have hdescent : baseEnd_2127660 < baseStart_2127660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127677 : List Nat := [1, 4, 1, 4, 1, 3, 8]
def baseStart_2127677 : Nat := 118140960795 + 2127677 * 2 ^ 59
def prefixEnd_2127677 : Nat := 4983230072969 + 3 ^ 40 * 2127677 * 2
def baseEnd_2127677 : Nat := 26975826630034004633395

theorem tailTrace_2127677 : CollatzResearch.WordTrace tailWord_2127677 prefixEnd_2127677 26975826630034004633395 := by
  unfold tailWord_2127677
  simp only [CollatzResearch.WordTrace]
  refine ⟨77602755512797082146685285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51735170341864721431123523 77602755512797082146685285)
  ·
    refine ⟨14550516658649452902503491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77602755512797082146685285 14550516658649452902503491)
    ·
      refine ⟨21825774987974179353755237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14550516658649452902503491 21825774987974179353755237)
      ·
        refine ⟨4092332810245158628829107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21825774987974179353755237 4092332810245158628829107)
        ·
          refine ⟨6138499215367737943243661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092332810245158628829107 6138499215367737943243661)
          ·
            refine ⟨2301937205762901728716373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6138499215367737943243661 2301937205762901728716373)
            ·
              refine ⟨26975826630034004633395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2301937205762901728716373 26975826630034004633395)
              ·
                rfl

theorem cell22_2127677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 8].length) (baseStart_2127677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127677 prefixEnd_2127677 := by exact prefixLift 2127677
  have htrace : WordTrace (prefixWord ++ tailWord_2127677) baseStart_2127677 baseEnd_2127677 := by
    simpa [prefixWord, tailWord_2127677, baseEnd_2127677] using wordTrace_append hprefix tailTrace_2127677
  have hstable : (prefixWord ++ tailWord_2127677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127677).length < 2 ^ (prefixWord ++ tailWord_2127677).sum := by decide
  have hdescent : baseEnd_2127677 < baseStart_2127677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127690 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2127690 : Nat := 118140960795 + 2127690 * 2 ^ 59
def prefixEnd_2127690 : Nat := 4983230072969 + 3 ^ 40 * 2127690 * 2
def baseEnd_2127690 : Nat := 728351769176590424526625

theorem tailTrace_2127690 : CollatzResearch.WordTrace tailWord_2127690 prefixEnd_2127690 728351769176590424526625 := by
  unfold tailWord_2127690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19400807415437496341727131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51735486441166656911272349 19400807415437496341727131)
  ·
    refine ⟨29101211123156244512590697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19400807415437496341727131 29101211123156244512590697)
    ·
      refine ⟨21825908342367183384443023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29101211123156244512590697 21825908342367183384443023)
      ·
        refine ⟨32738862513550775076664535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21825908342367183384443023 32738862513550775076664535)
        ·
          refine ⟨49108293770326162614996803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32738862513550775076664535 49108293770326162614996803)
          ·
            refine ⟨73662440655489243922495205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49108293770326162614996803 73662440655489243922495205)
            ·
              refine ⟨13811707622904233235467851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73662440655489243922495205 13811707622904233235467851)
              ·
                refine ⟨20717561434356349853201777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13811707622904233235467851 20717561434356349853201777)
                ·
                  refine ⟨15538171075767262389901333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20717561434356349853201777 15538171075767262389901333)
                  ·
                    refine ⟨728351769176590424526625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15538171075767262389901333 728351769176590424526625)
                    ·
                      rfl

theorem cell22_2127690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2127690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127690 prefixEnd_2127690 := by exact prefixLift 2127690
  have htrace : WordTrace (prefixWord ++ tailWord_2127690) baseStart_2127690 baseEnd_2127690 := by
    simpa [prefixWord, tailWord_2127690, baseEnd_2127690] using wordTrace_append hprefix tailTrace_2127690
  have hstable : (prefixWord ++ tailWord_2127690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127690).length < 2 ^ (prefixWord ++ tailWord_2127690).sum := by decide
  have hdescent : baseEnd_2127690 < baseStart_2127690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127754 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_2127754 : Nat := 118140960795 + 2127754 * 2 ^ 59
def prefixEnd_2127754 : Nat := 4983230072969 + 3 ^ 40 * 2127754 * 2
def baseEnd_2127754 : Nat := 728373677684515590926429

theorem tailTrace_2127754 : CollatzResearch.WordTrace tailWord_2127754 prefixEnd_2127754 728373677684515590926429 := by
  unfold tailWord_2127754
  simp only [CollatzResearch.WordTrace]
  refine ⟨19401390983379531074309579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51737042622345416198158877 19401390983379531074309579)
  ·
    refine ⟨29102086475069296611464369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19401390983379531074309579 29102086475069296611464369)
    ·
      refine ⟨21826564856301972458598277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29102086475069296611464369 21826564856301972458598277)
      ·
        refine ⟨4092480910556619835987177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21826564856301972458598277 4092480910556619835987177)
        ·
          refine ⟨3069360682917464876990383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4092480910556619835987177 3069360682917464876990383)
          ·
            refine ⟨4604041024376197315485575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069360682917464876990383 4604041024376197315485575)
            ·
              refine ⟨6906061536564295973228363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604041024376197315485575 6906061536564295973228363)
              ·
                refine ⟨10359092304846443959842545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6906061536564295973228363 10359092304846443959842545)
                ·
                  refine ⟨7769319228634832969881909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10359092304846443959842545 7769319228634832969881909)
                  ·
                    refine ⟨728373677684515590926429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7769319228634832969881909 728373677684515590926429)
                    ·
                      rfl

theorem cell22_2127754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_2127754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127754 prefixEnd_2127754 := by exact prefixLift 2127754
  have htrace : WordTrace (prefixWord ++ tailWord_2127754) baseStart_2127754 baseEnd_2127754 := by
    simpa [prefixWord, tailWord_2127754, baseEnd_2127754] using wordTrace_append hprefix tailTrace_2127754
  have hstable : (prefixWord ++ tailWord_2127754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127754).length < 2 ^ (prefixWord ++ tailWord_2127754).sum := by decide
  have hdescent : baseEnd_2127754 < baseStart_2127754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127767 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 6]
def baseStart_2127767 : Nat := 118140960795 + 2127767 * 2 ^ 59
def prefixEnd_2127767 : Nat := 4983230072969 + 3 ^ 40 * 2127767 * 2
def baseEnd_2127767 : Nat := 242792709283395963450463

theorem tailTrace_2127767 : CollatzResearch.WordTrace tailWord_2127767 prefixEnd_2127767 242792709283395963450463 := by
  unfold tailWord_2127767
  simp only [CollatzResearch.WordTrace]
  refine ⟨77606038082471027517461555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51737358721647351678307703 77606038082471027517461555)
  ·
    refine ⟨116409057123706541276192333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77606038082471027517461555 116409057123706541276192333)
    ·
      refine ⟨43653396421389952978572125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116409057123706541276192333 43653396421389952978572125)
      ·
        refine ⟨16370023658021232366964547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43653396421389952978572125 16370023658021232366964547)
        ·
          refine ⟨24555035487031848550446821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16370023658021232366964547 24555035487031848550446821)
          ·
            refine ⟨4604069153818471603208779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24555035487031848550446821 4604069153818471603208779)
            ·
              refine ⟨6906103730727707404813169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604069153818471603208779 6906103730727707404813169)
              ·
                refine ⟨5179577798045780553609877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6906103730727707404813169 5179577798045780553609877)
                ·
                  refine ⟨242792709283395963450463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5179577798045780553609877 242792709283395963450463)
                  ·
                    rfl

theorem cell22_2127767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 6].length) (baseStart_2127767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127767 prefixEnd_2127767 := by exact prefixLift 2127767
  have htrace : WordTrace (prefixWord ++ tailWord_2127767) baseStart_2127767 baseEnd_2127767 := by
    simpa [prefixWord, tailWord_2127767, baseEnd_2127767] using wordTrace_append hprefix tailTrace_2127767
  have hstable : (prefixWord ++ tailWord_2127767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127767).length < 2 ^ (prefixWord ++ tailWord_2127767).sum := by decide
  have hdescent : baseEnd_2127767 < baseStart_2127767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127790 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_2127790 : Nat := 118140960795 + 2127790 * 2 ^ 59
def prefixEnd_2127790 : Nat := 4983230072969 + 3 ^ 40 * 2127790 * 2
def baseEnd_2127790 : Nat := 242795333740074499008773

theorem tailTrace_2127790 : CollatzResearch.WordTrace tailWord_2127790 prefixEnd_2127790 242795333740074499008773 := by
  unfold tailWord_2127790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700859620173462805693603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51737917974258468297032549 9700859620173462805693603)
  ·
    refine ⟨14551289430260194208540405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700859620173462805693603 14551289430260194208540405)
    ·
      refine ⟨1364183384086893207050663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14551289430260194208540405 1364183384086893207050663)
      ·
        refine ⟨2046275076130339810575995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364183384086893207050663 2046275076130339810575995)
        ·
          refine ⟨3069412614195509715863993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046275076130339810575995 3069412614195509715863993)
          ·
            refine ⟨2302059460646632286897995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3069412614195509715863993 2302059460646632286897995)
            ·
              refine ⟨3453089190969948430346993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302059460646632286897995 3453089190969948430346993)
              ·
                refine ⟨2589816893227461322760245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453089190969948430346993 2589816893227461322760245)
                ·
                  refine ⟨242795333740074499008773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2589816893227461322760245 242795333740074499008773)
                  ·
                    rfl

theorem cell22_2127790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_2127790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127790 prefixEnd_2127790 := by exact prefixLift 2127790
  have htrace : WordTrace (prefixWord ++ tailWord_2127790) baseStart_2127790 baseEnd_2127790 := by
    simpa [prefixWord, tailWord_2127790, baseEnd_2127790] using wordTrace_append hprefix tailTrace_2127790
  have hstable : (prefixWord ++ tailWord_2127790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127790).length < 2 ^ (prefixWord ++ tailWord_2127790).sum := by decide
  have hdescent : baseEnd_2127790 < baseStart_2127790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127795 : List Nat := [1, 1, 1, 2, 3, 1, 13]
def baseStart_2127795 : Nat := 118140960795 + 2127795 * 2 ^ 59
def prefixEnd_2127795 : Nat := 4983230072969 + 3 ^ 40 * 2127795 * 2
def baseEnd_2127795 : Nat := 26977322697126116690789

theorem tailTrace_2127795 : CollatzResearch.WordTrace tailWord_2127795 prefixEnd_2127795 26977322697126116690789 := by
  unfold tailWord_2127795
  simp only [CollatzResearch.WordTrace]
  refine ⟨77607059326369588299480839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51738039550913058866320559 77607059326369588299480839)
  ·
    refine ⟨116410588989554382449221259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77607059326369588299480839 116410588989554382449221259)
    ·
      refine ⟨174615883484331573673831889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116410588989554382449221259 174615883484331573673831889)
      ·
        refine ⟨130961912613248680255373917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174615883484331573673831889 130961912613248680255373917)
        ·
          refine ⟨49110717229968255095765219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130961912613248680255373917 49110717229968255095765219)
          ·
            refine ⟨73666075844952382643647829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49110717229968255095765219 73666075844952382643647829)
            ·
              refine ⟨26977322697126116690789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 73666075844952382643647829 26977322697126116690789)
              ·
                rfl

theorem cell22_2127795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 13].length) (baseStart_2127795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127795 prefixEnd_2127795 := by exact prefixLift 2127795
  have htrace : WordTrace (prefixWord ++ tailWord_2127795) baseStart_2127795 baseEnd_2127795 := by
    simpa [prefixWord, tailWord_2127795, baseEnd_2127795] using wordTrace_append hprefix tailTrace_2127795
  have hstable : (prefixWord ++ tailWord_2127795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127795).length < 2 ^ (prefixWord ++ tailWord_2127795).sum := by decide
  have hdescent : baseEnd_2127795 < baseStart_2127795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127829 : List Nat := [1, 3, 2, 3, 2, 1, 4, 6]
def baseStart_2127829 : Nat := 118140960795 + 2127829 * 2 ^ 59
def prefixEnd_2127829 : Nat := 4983230072969 + 3 ^ 40 * 2127829 * 2
def baseEnd_2127829 : Nat := 80933261301915599477911

theorem tailTrace_2127829 : CollatzResearch.WordTrace tailWord_2127829 prefixEnd_2127829 80933261301915599477911 := by
  unfold tailWord_2127829
  simp only [CollatzResearch.WordTrace]
  refine ⟨77608299408246412106218541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51738866272164274737479027 77608299408246412106218541)
  ·
    refine ⟨29103112278092404539831953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77608299408246412106218541 29103112278092404539831953)
    ·
      refine ⟨21827334208569303404873965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29103112278092404539831953 21827334208569303404873965)
      ·
        refine ⟨8185250328213488776827737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21827334208569303404873965 8185250328213488776827737)
        ·
          refine ⟨6138937746160116582620803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8185250328213488776827737 6138937746160116582620803)
          ·
            refine ⟨9208406619240174873931205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6138937746160116582620803 9208406619240174873931205)
            ·
              refine ⟨1726576241107532788862101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9208406619240174873931205 1726576241107532788862101)
              ·
                refine ⟨80933261301915599477911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1726576241107532788862101 80933261301915599477911)
                ·
                  rfl

theorem cell22_2127829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 6].length) (baseStart_2127829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127829 prefixEnd_2127829 := by exact prefixLift 2127829
  have htrace : WordTrace (prefixWord ++ tailWord_2127829) baseStart_2127829 baseEnd_2127829 := by
    simpa [prefixWord, tailWord_2127829, baseEnd_2127829] using wordTrace_append hprefix tailTrace_2127829
  have hstable : (prefixWord ++ tailWord_2127829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127829).length < 2 ^ (prefixWord ++ tailWord_2127829).sum := by decide
  have hdescent : baseEnd_2127829 < baseStart_2127829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127964 : List Nat := [2, 2, 4, 1, 1, 3, 9]
def baseStart_2127964 : Nat := 118140960795 + 2127964 * 2 ^ 59
def prefixEnd_2127964 : Nat := 4983230072969 + 3 ^ 40 * 2127964 * 2
def baseEnd_2127964 : Nat := 26979465369486853450955

theorem tailTrace_2127964 : CollatzResearch.WordTrace tailWord_2127964 prefixEnd_2127964 26979465369486853450955 := by
  unfold tailWord_2127964
  simp only [CollatzResearch.WordTrace]
  refine ⟨38806611631378665081191473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51742148841838220108255297 38806611631378665081191473)
  ·
    refine ⟨29104958723533998810893605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38806611631378665081191473 29104958723533998810893605)
    ·
      refine ⟨5457179760662624777042551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29104958723533998810893605 5457179760662624777042551)
      ·
        refine ⟨8185769640993937165563827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5457179760662624777042551 8185769640993937165563827)
        ·
          refine ⟨12278654461490905748345741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8185769640993937165563827 12278654461490905748345741)
          ·
            refine ⟨4604495423059089655629653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12278654461490905748345741 4604495423059089655629653)
            ·
              refine ⟨26979465369486853450955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4604495423059089655629653 26979465369486853450955)
              ·
                rfl

theorem cell22_2127964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 9].length) (baseStart_2127964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127964 prefixEnd_2127964 := by exact prefixLift 2127964
  have htrace : WordTrace (prefixWord ++ tailWord_2127964) baseStart_2127964 baseEnd_2127964 := by
    simpa [prefixWord, tailWord_2127964, baseEnd_2127964] using wordTrace_append hprefix tailTrace_2127964
  have hstable : (prefixWord ++ tailWord_2127964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127964).length < 2 ^ (prefixWord ++ tailWord_2127964).sum := by decide
  have hdescent : baseEnd_2127964 < baseStart_2127964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127968 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_2127968 : Nat := 118140960795 + 2127968 * 2 ^ 59
def prefixEnd_2127968 : Nat := 4983230072969 + 3 ^ 40 * 2127968 * 2
def baseEnd_2127968 : Nat := 728446934257890366075773

theorem tailTrace_2127968 : CollatzResearch.WordTrace tailWord_2127968 prefixEnd_2127968 728446934257890366075773 := by
  unfold tailWord_2127968
  simp only [CollatzResearch.WordTrace]
  refine ⟨38806684577371419422764279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51742246103161892563685705 38806684577371419422764279)
  ·
    refine ⟨58210026866057129134146419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38806684577371419422764279 58210026866057129134146419)
    ·
      refine ⟨87315040299085693701219629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58210026866057129134146419 87315040299085693701219629)
      ·
        refine ⟨32743140112157135137957361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87315040299085693701219629 32743140112157135137957361)
        ·
          refine ⟨24557355084117851353468021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32743140112157135137957361 24557355084117851353468021)
          ·
            refine ⟨2302252039136048564387627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24557355084117851353468021 2302252039136048564387627)
            ·
              refine ⟨3453378058704072846581441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302252039136048564387627 3453378058704072846581441)
              ·
                refine ⟨2590033544028054634936081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453378058704072846581441 2590033544028054634936081)
                ·
                  refine ⟨1942525158021040976202061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590033544028054634936081 1942525158021040976202061)
                  ·
                    refine ⟨728446934257890366075773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942525158021040976202061 728446934257890366075773)
                    ·
                      rfl

theorem cell22_2127968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_2127968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127968 prefixEnd_2127968 := by exact prefixLift 2127968
  have htrace : WordTrace (prefixWord ++ tailWord_2127968) baseStart_2127968 baseEnd_2127968 := by
    simpa [prefixWord, tailWord_2127968, baseEnd_2127968] using wordTrace_append hprefix tailTrace_2127968
  have hstable : (prefixWord ++ tailWord_2127968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127968).length < 2 ^ (prefixWord ++ tailWord_2127968).sum := by decide
  have hdescent : baseEnd_2127968 < baseStart_2127968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127996 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_2127996 : Nat := 118140960795 + 2127996 * 2 ^ 59
def prefixEnd_2127996 : Nat := 4983230072969 + 3 ^ 40 * 2127996 * 2
def baseEnd_2127996 : Nat := 728456519230107626375687

theorem tailTrace_2127996 : CollatzResearch.WordTrace tailWord_2127996 prefixEnd_2127996 728456519230107626375687 := by
  unfold tailWord_2127996
  simp only [CollatzResearch.WordTrace]
  refine ⟨38807195199320699813773921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51742926932427599751698561 38807195199320699813773921)
  ·
    refine ⟨29105396399490524860330441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38807195199320699813773921 29105396399490524860330441)
    ·
      refine ⟨21829047299617893645247831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29105396399490524860330441 21829047299617893645247831)
      ·
        refine ⟨32743570949426840467871747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21829047299617893645247831 32743570949426840467871747)
        ·
          refine ⟨49115356424140260701807621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32743570949426840467871747 49115356424140260701807621)
          ·
            refine ⟨9209129329526298881588929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49115356424140260701807621 9209129329526298881588929)
            ·
              refine ⟨6906846997144724161191697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9209129329526298881588929 6906846997144724161191697)
              ·
                refine ⟨5180135247858543120893773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6906846997144724161191697 5180135247858543120893773)
                ·
                  refine ⟨1942550717946953670335165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5180135247858543120893773 1942550717946953670335165)
                  ·
                    refine ⟨728456519230107626375687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942550717946953670335165 728456519230107626375687)
                    ·
                      rfl

theorem cell22_2127996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_2127996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2127996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2127996 prefixEnd_2127996 := by exact prefixLift 2127996
  have htrace : WordTrace (prefixWord ++ tailWord_2127996) baseStart_2127996 baseEnd_2127996 := by
    simpa [prefixWord, tailWord_2127996, baseEnd_2127996] using wordTrace_append hprefix tailTrace_2127996
  have hstable : (prefixWord ++ tailWord_2127996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127996).length < 2 ^ (prefixWord ++ tailWord_2127996).sum := by decide
  have hdescent : baseEnd_2127996 < baseStart_2127996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128069 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_2128069 : Nat := 118140960795 + 2128069 * 2 ^ 59
def prefixEnd_2128069 : Nat := 4983230072969 + 3 ^ 40 * 2128069 * 2
def baseEnd_2128069 : Nat := 728481508621959769300463

theorem tailTrace_2128069 : CollatzResearch.WordTrace tailWord_2128069 prefixEnd_2128069 728481508621959769300463 := by
  unfold tailWord_2128069
  simp only [CollatzResearch.WordTrace]
  refine ⟨77617052927376933094955261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51744701951584622063303507 77617052927376933094955261)
  ·
    refine ⟨29106394847766349910608223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77617052927376933094955261 29106394847766349910608223)
    ·
      refine ⟨43659592271649524865912335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29106394847766349910608223 43659592271649524865912335)
      ·
        refine ⟨65489388407474287298868503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43659592271649524865912335 65489388407474287298868503)
        ·
          refine ⟨98234082611211430948302755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65489388407474287298868503 98234082611211430948302755)
          ·
            refine ⟨147351123916817146422454133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98234082611211430948302755 147351123916817146422454133)
            ·
              refine ⟨13814167867201607477105075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147351123916817146422454133 13814167867201607477105075)
              ·
                refine ⟨20721251800802411215657613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13814167867201607477105075 20721251800802411215657613)
                ·
                  refine ⟨7770469425300904205871605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20721251800802411215657613 7770469425300904205871605)
                  ·
                    refine ⟨728481508621959769300463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7770469425300904205871605 728481508621959769300463)
                    ·
                      rfl

theorem cell22_2128069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_2128069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128069 prefixEnd_2128069 := by exact prefixLift 2128069
  have htrace : WordTrace (prefixWord ++ tailWord_2128069) baseStart_2128069 baseEnd_2128069 := by
    simpa [prefixWord, tailWord_2128069, baseEnd_2128069] using wordTrace_append hprefix tailTrace_2128069
  have hstable : (prefixWord ++ tailWord_2128069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128069).length < 2 ^ (prefixWord ++ tailWord_2128069).sum := by decide
  have hdescent : baseEnd_2128069 < baseStart_2128069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128088 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 4]
def baseStart_2128088 : Nat := 118140960795 + 2128088 * 2 ^ 59
def prefixEnd_2128088 : Nat := 4983230072969 + 3 ^ 40 * 2128088 * 2
def baseEnd_2128088 : Nat := 242829337570083351025135

theorem tailTrace_2128088 : CollatzResearch.WordTrace tailWord_2128088 prefixEnd_2128088 242829337570083351025135 := by
  unfold tailWord_2128088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38808872957154049669948459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51745163942872066226597945 38808872957154049669948459)
  ·
    refine ⟨58213309435731074504922689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38808872957154049669948459 58213309435731074504922689)
    ·
      refine ⟨43659982076798305878692017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58213309435731074504922689 43659982076798305878692017)
      ·
        refine ⟨32744986557598729409019013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43659982076798305878692017 32744986557598729409019013)
        ·
          refine ⟨6139684979549761764191065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32744986557598729409019013 6139684979549761764191065)
          ·
            refine ⟨4604763734662321323143299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6139684979549761764191065 4604763734662321323143299)
            ·
              refine ⟨6907145601993481984714949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604763734662321323143299 6907145601993481984714949)
              ·
                refine ⟨1295089800373777872134053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6907145601993481984714949 1295089800373777872134053)
                ·
                  refine ⟨242829337570083351025135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295089800373777872134053 242829337570083351025135)
                  ·
                    rfl

theorem cell22_2128088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_2128088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128088 prefixEnd_2128088 := by exact prefixLift 2128088
  have htrace : WordTrace (prefixWord ++ tailWord_2128088) baseStart_2128088 baseEnd_2128088 := by
    simpa [prefixWord, tailWord_2128088, baseEnd_2128088] using wordTrace_append hprefix tailTrace_2128088
  have hstable : (prefixWord ++ tailWord_2128088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128088).length < 2 ^ (prefixWord ++ tailWord_2128088).sum := by decide
  have hdescent : baseEnd_2128088 < baseStart_2128088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128103 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2128103 : Nat := 118140960795 + 2128103 * 2 ^ 59
def prefixEnd_2128103 : Nat := 4983230072969 + 3 ^ 40 * 2128103 * 2
def baseEnd_2128103 : Nat := 728493147516795013950359

theorem tailTrace_2128103 : CollatzResearch.WordTrace tailWord_2128103 prefixEnd_2128103 728493147516795013950359 := by
  unfold tailWord_2128103
  simp only [CollatzResearch.WordTrace]
  refine ⟨77618293009253756901692963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51745528672835837934461975 77618293009253756901692963)
  ·
    refine ⟨116427439513880635352539445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77618293009253756901692963 116427439513880635352539445)
    ·
      refine ⟨10915072454426309564300573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116427439513880635352539445 10915072454426309564300573)
      ·
        refine ⟨4093152170409866086612715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10915072454426309564300573 4093152170409866086612715)
        ·
          refine ⟨6139728255614799129919073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093152170409866086612715 6139728255614799129919073)
          ·
            refine ⟨4604796191711099347439305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6139728255614799129919073 4604796191711099347439305)
            ·
              refine ⟨3453597143783324510579479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4604796191711099347439305 3453597143783324510579479)
              ·
                refine ⟨5180395715674986765869219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453597143783324510579479 5180395715674986765869219)
                ·
                  refine ⟨7770593573512480148803829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5180395715674986765869219 7770593573512480148803829)
                  ·
                    refine ⟨728493147516795013950359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7770593573512480148803829 728493147516795013950359)
                    ·
                      rfl

theorem cell22_2128103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2128103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128103 prefixEnd_2128103 := by exact prefixLift 2128103
  have htrace : WordTrace (prefixWord ++ tailWord_2128103) baseStart_2128103 baseEnd_2128103 := by
    simpa [prefixWord, tailWord_2128103, baseEnd_2128103] using wordTrace_append hprefix tailTrace_2128103
  have hstable : (prefixWord ++ tailWord_2128103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128103).length < 2 ^ (prefixWord ++ tailWord_2128103).sum := by decide
  have hdescent : baseEnd_2128103 < baseStart_2128103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128118 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_2128118 : Nat := 118140960795 + 2128118 * 2 ^ 59
def prefixEnd_2128118 : Nat := 4983230072969 + 3 ^ 40 * 2128118 * 2
def baseEnd_2128118 : Nat := 728498282323339974825313

theorem tailTrace_2128118 : CollatzResearch.WordTrace tailWord_2128118 prefixEnd_2128118 728498282323339974825313 := by
  unfold tailWord_2128118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851177506512463403968063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51745893402799609642326005 4851177506512463403968063)
  ·
    refine ⟨7276766259768695105952095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4851177506512463403968063 7276766259768695105952095)
    ·
      refine ⟨10915149389653042658928143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7276766259768695105952095 10915149389653042658928143)
      ·
        refine ⟨16372724084479563988392215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10915149389653042658928143 16372724084479563988392215)
        ·
          refine ⟨24559086126719345982588323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16372724084479563988392215 24559086126719345982588323)
          ·
            refine ⟨36838629190079018973882485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24559086126719345982588323 36838629190079018973882485)
            ·
              refine ⟨3453621486569908028801483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36838629190079018973882485 3453621486569908028801483)
              ·
                refine ⟨5180432229854862043202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453621486569908028801483 5180432229854862043202225)
                ·
                  refine ⟨3885324172391146532401669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5180432229854862043202225 3885324172391146532401669)
                  ·
                    refine ⟨728498282323339974825313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885324172391146532401669 728498282323339974825313)
                    ·
                      rfl

theorem cell22_2128118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_2128118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128118 prefixEnd_2128118 := by exact prefixLift 2128118
  have htrace : WordTrace (prefixWord ++ tailWord_2128118) baseStart_2128118 baseEnd_2128118 := by
    simpa [prefixWord, tailWord_2128118, baseEnd_2128118] using wordTrace_append hprefix tailTrace_2128118
  have hstable : (prefixWord ++ tailWord_2128118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128118).length < 2 ^ (prefixWord ++ tailWord_2128118).sum := by decide
  have hdescent : baseEnd_2128118 < baseStart_2128118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128131 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 5, 3]
def baseStart_2128131 : Nat := 118140960795 + 2128131 * 2 ^ 59
def prefixEnd_2128131 : Nat := 4983230072969 + 3 ^ 40 * 2128131 * 2
def baseEnd_2128131 : Nat := 728502732489012274250273

theorem tailTrace_2128131 : CollatzResearch.WordTrace tailWord_2128131 prefixEnd_2128131 728502732489012274250273 := by
  unfold tailWord_2128131
  simp only [CollatzResearch.WordTrace]
  refine ⟨77619314253152317683712247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51746209502101545122474831 77619314253152317683712247)
  ·
    refine ⟨116428971379728476525568371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77619314253152317683712247 116428971379728476525568371)
    ·
      refine ⟨174643457069592714788352557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116428971379728476525568371 174643457069592714788352557)
      ·
        refine ⟨65491296401097268045632209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174643457069592714788352557 65491296401097268045632209)
        ·
          refine ⟨49118472300822951034224157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65491296401097268045632209 49118472300822951034224157)
          ·
            refine ⟨18419427112808606637834059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49118472300822951034224157 18419427112808606637834059)
            ·
              refine ⟨27629140669212909956751089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18419427112808606637834059 27629140669212909956751089)
              ·
                refine ⟨20721855501909682467563317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27629140669212909956751089 20721855501909682467563317)
                ·
                  refine ⟨1942673953304032731334061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20721855501909682467563317 1942673953304032731334061)
                  ·
                    refine ⟨728502732489012274250273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942673953304032731334061 728502732489012274250273)
                    ·
                      rfl

theorem cell22_2128131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 3].length) (baseStart_2128131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128131 prefixEnd_2128131 := by exact prefixLift 2128131
  have htrace : WordTrace (prefixWord ++ tailWord_2128131) baseStart_2128131 baseEnd_2128131 := by
    simpa [prefixWord, tailWord_2128131, baseEnd_2128131] using wordTrace_append hprefix tailTrace_2128131
  have hstable : (prefixWord ++ tailWord_2128131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128131).length < 2 ^ (prefixWord ++ tailWord_2128131).sum := by decide
  have hdescent : baseEnd_2128131 < baseStart_2128131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128161 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 5]
def baseStart_2128161 : Nat := 118140960795 + 2128161 * 2 ^ 59
def prefixEnd_2128161 : Nat := 4983230072969 + 3 ^ 40 * 2128161 * 2
def baseEnd_2128161 : Nat := 242837667367367398666727

theorem tailTrace_2128161 : CollatzResearch.WordTrace tailWord_2128161 prefixEnd_2128161 242837667367367398666727 := by
  unfold tailWord_2128161
  simp only [CollatzResearch.WordTrace]
  refine ⟨77620408443043632807304337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51746938962029088538202891 77620408443043632807304337)
  ·
    refine ⟨58215306332282724605478253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77620408443043632807304337 58215306332282724605478253)
    ·
      refine ⟨21830739874606021727054345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58215306332282724605478253 21830739874606021727054345)
      ·
        refine ⟨16373054905954516295290759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21830739874606021727054345 16373054905954516295290759)
        ·
          refine ⟨24559582358931774442936139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16373054905954516295290759 24559582358931774442936139)
          ·
            refine ⟨36839373538397661664404209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24559582358931774442936139 36839373538397661664404209)
            ·
              refine ⟨27629530153798246248303157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36839373538397661664404209 27629530153798246248303157)
              ·
                refine ⟨2590268451918585585778421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27629530153798246248303157 2590268451918585585778421)
                ·
                  refine ⟨242837667367367398666727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2590268451918585585778421 242837667367367398666727)
                  ·
                    rfl

theorem cell22_2128161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_2128161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128161 prefixEnd_2128161 := by exact prefixLift 2128161
  have htrace : WordTrace (prefixWord ++ tailWord_2128161) baseStart_2128161 baseEnd_2128161 := by
    simpa [prefixWord, tailWord_2128161, baseEnd_2128161] using wordTrace_append hprefix tailTrace_2128161
  have hstable : (prefixWord ++ tailWord_2128161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128161).length < 2 ^ (prefixWord ++ tailWord_2128161).sum := by decide
  have hdescent : baseEnd_2128161 < baseStart_2128161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128206 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_2128206 : Nat := 118140960795 + 2128206 * 2 ^ 59
def prefixEnd_2128206 : Nat := 4983230072969 + 3 ^ 40 * 2128206 * 2
def baseEnd_2128206 : Nat := 242842802173912359541681

theorem tailTrace_2128206 : CollatzResearch.WordTrace tailWord_2128206 prefixEnd_2128206 242842802173912359541681 := by
  unfold tailWord_2128206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9702756215985075686586559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51748033151920403661794981 9702756215985075686586559)
  ·
    refine ⟨14554134323977613529879839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9702756215985075686586559 14554134323977613529879839)
    ·
      refine ⟨21831201485966420294819759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14554134323977613529879839 21831201485966420294819759)
      ·
        refine ⟨32746802228949630442229639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21831201485966420294819759 32746802228949630442229639)
        ·
          refine ⟨49120203343424445663344459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32746802228949630442229639 49120203343424445663344459)
          ·
            refine ⟨73680305015136668495016689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49120203343424445663344459 73680305015136668495016689)
            ·
              refine ⟨55260228761352501371262517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73680305015136668495016689 55260228761352501371262517)
              ·
                refine ⟨5180646446376797003555861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55260228761352501371262517 5180646446376797003555861)
                ·
                  refine ⟨242842802173912359541681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5180646446376797003555861 242842802173912359541681)
                  ·
                    rfl

theorem cell22_2128206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_2128206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128206 prefixEnd_2128206 := by exact prefixLift 2128206
  have htrace : WordTrace (prefixWord ++ tailWord_2128206) baseStart_2128206 baseEnd_2128206 := by
    simpa [prefixWord, tailWord_2128206, baseEnd_2128206] using wordTrace_append hprefix tailTrace_2128206
  have hstable : (prefixWord ++ tailWord_2128206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128206).length < 2 ^ (prefixWord ++ tailWord_2128206).sum := by decide
  have hdescent : baseEnd_2128206 < baseStart_2128206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128253 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_2128253 : Nat := 118140960795 + 2128253 * 2 ^ 59
def prefixEnd_2128253 : Nat := 4983230072969 + 3 ^ 40 * 2128253 * 2
def baseEnd_2128253 : Nat := 728544495582244622699899

theorem tailTrace_2128253 : CollatzResearch.WordTrace tailWord_2128253 prefixEnd_2128253 728544495582244622699899 := by
  unfold tailWord_2128253
  simp only [CollatzResearch.WordTrace]
  refine ⟨77623763958710332519653413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51749175972473555013102275 77623763958710332519653413)
  ·
    refine ⟨14554455742258187347435015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77623763958710332519653413 14554455742258187347435015)
    ·
      refine ⟨21831683613387281021152523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14554455742258187347435015 21831683613387281021152523)
      ·
        refine ⟨32747525420080921531728785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21831683613387281021152523 32747525420080921531728785)
        ·
          refine ⟨24560644065060691148796589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32747525420080921531728785 24560644065060691148796589)
          ·
            refine ⟨9210241524397759180798721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24560644065060691148796589 9210241524397759180798721)
            ·
              refine ⟨6907681143298319385599041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9210241524397759180798721 6907681143298319385599041)
              ·
                refine ⟨5180760857473739539199281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6907681143298319385599041 5180760857473739539199281)
                ·
                  refine ⟨3885570643105304654399461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5180760857473739539199281 3885570643105304654399461)
                  ·
                    refine ⟨728544495582244622699899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885570643105304654399461 728544495582244622699899)
                    ·
                      rfl

theorem cell22_2128253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_2128253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128253 prefixEnd_2128253 := by exact prefixLift 2128253
  have htrace : WordTrace (prefixWord ++ tailWord_2128253) baseStart_2128253 baseEnd_2128253 := by
    simpa [prefixWord, tailWord_2128253, baseEnd_2128253] using wordTrace_append hprefix tailTrace_2128253
  have hstable : (prefixWord ++ tailWord_2128253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128253).length < 2 ^ (prefixWord ++ tailWord_2128253).sum := by decide
  have hdescent : baseEnd_2128253 < baseStart_2128253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128257 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 4]
def baseStart_2128257 : Nat := 118140960795 + 2128257 * 2 ^ 59
def prefixEnd_2128257 : Nat := 4983230072969 + 3 ^ 40 * 2128257 * 2
def baseEnd_2128257 : Nat := 242848621621329981866629

theorem tailTrace_2128257 : CollatzResearch.WordTrace tailWord_2128257 prefixEnd_2128257 242848621621329981866629 := by
  unfold tailWord_2128257
  simp only [CollatzResearch.WordTrace]
  refine ⟨77623909850695841202799025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51749273233797227468532683 77623909850695841202799025)
  ·
    refine ⟨58217932388021880902099269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77623909850695841202799025 58217932388021880902099269)
    ·
      refine ⟨10915862322754102669143613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58217932388021880902099269 10915862322754102669143613)
      ·
        refine ⟨4093448371032788500928855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10915862322754102669143613 4093448371032788500928855)
        ·
          refine ⟨6140172556549182751393283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093448371032788500928855 6140172556549182751393283)
          ·
            refine ⟨9210258834823774127089925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6140172556549182751393283 9210258834823774127089925)
            ·
              refine ⟨1726923531529457648829361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9210258834823774127089925 1726923531529457648829361)
              ·
                refine ⟨1295192648647093236622021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1726923531529457648829361 1295192648647093236622021)
                ·
                  refine ⟨242848621621329981866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295192648647093236622021 242848621621329981866629)
                  ·
                    rfl

theorem cell22_2128257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_2128257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128257 prefixEnd_2128257 := by exact prefixLift 2128257
  have htrace : WordTrace (prefixWord ++ tailWord_2128257) baseStart_2128257 baseEnd_2128257 := by
    simpa [prefixWord, tailWord_2128257, baseEnd_2128257] using wordTrace_append hprefix tailTrace_2128257
  have hstable : (prefixWord ++ tailWord_2128257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128257).length < 2 ^ (prefixWord ++ tailWord_2128257).sum := by decide
  have hdescent : baseEnd_2128257 < baseStart_2128257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128268 : List Nat := [2, 2, 1, 2, 1, 6, 1, 7]
def baseStart_2128268 : Nat := 118140960795 + 2128268 * 2 ^ 59
def prefixEnd_2128268 : Nat := 4983230072969 + 3 ^ 40 * 2128268 * 2
def baseEnd_2128268 : Nat := 80949958932087731508317

theorem tailTrace_2128268 : CollatzResearch.WordTrace tailWord_2128268 prefixEnd_2128268 80949958932087731508317 := by
  unfold tailWord_2128268
  simp only [CollatzResearch.WordTrace]
  refine ⟨38812155526827995040724729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51749540702437326720966305 38812155526827995040724729)
  ·
    refine ⟨29109116645120996280543547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38812155526827995040724729 29109116645120996280543547)
    ·
      refine ⟨43663674967681494420815321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29109116645120996280543547 43663674967681494420815321)
      ·
        refine ⟨32747756225761120815611491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43663674967681494420815321 32747756225761120815611491)
        ·
          refine ⟨49121634338641681223417237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32747756225761120815611491 49121634338641681223417237)
          ·
            refine ⟨2302576609623828807347683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49121634338641681223417237 2302576609623828807347683)
            ·
              refine ⟨3453864914435743211021525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302576609623828807347683 3453864914435743211021525)
              ·
                refine ⟨80949958932087731508317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3453864914435743211021525 80949958932087731508317)
                ·
                  rfl

theorem cell22_2128268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 7].length) (baseStart_2128268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128268 prefixEnd_2128268 := by exact prefixLift 2128268
  have htrace : WordTrace (prefixWord ++ tailWord_2128268) baseStart_2128268 baseEnd_2128268 := by
    simpa [prefixWord, tailWord_2128268, baseEnd_2128268] using wordTrace_append hprefix tailTrace_2128268
  have hstable : (prefixWord ++ tailWord_2128268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128268).length < 2 ^ (prefixWord ++ tailWord_2128268).sum := by decide
  have hdescent : baseEnd_2128268 < baseStart_2128268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128281 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_2128281 : Nat := 118140960795 + 2128281 * 2 ^ 59
def prefixEnd_2128281 : Nat := 4983230072969 + 3 ^ 40 * 2128281 * 2
def baseEnd_2128281 : Nat := 728554080554461882999813

theorem tailTrace_2128281 : CollatzResearch.WordTrace tailWord_2128281 prefixEnd_2128281 728554080554461882999813 := by
  unfold tailWord_2128281
  simp only [CollatzResearch.WordTrace]
  refine ⟨77624785202608893301672697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51749856801739262201115131 77624785202608893301672697)
  ·
    refine ⟨58218588901956669976254523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77624785202608893301672697 58218588901956669976254523)
    ·
      refine ⟨87327883352935004964381785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58218588901956669976254523 87327883352935004964381785)
      ·
        refine ⟨65495912514701253723286339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87327883352935004964381785 65495912514701253723286339)
        ·
          refine ⟨98243868772051880584929509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65495912514701253723286339 98243868772051880584929509)
          ·
            refine ⟨18420725394759727609674283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98243868772051880584929509 18420725394759727609674283)
            ·
              refine ⟨27631088092139591414511425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18420725394759727609674283 27631088092139591414511425)
              ·
                refine ⟨20723316069104693560883569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27631088092139591414511425 20723316069104693560883569)
                ·
                  refine ⟨15542487051828520170662677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20723316069104693560883569 15542487051828520170662677)
                  ·
                    refine ⟨728554080554461882999813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15542487051828520170662677 728554080554461882999813)
                    ·
                      rfl

theorem cell22_2128281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_2128281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128281 prefixEnd_2128281 := by exact prefixLift 2128281
  have htrace : WordTrace (prefixWord ++ tailWord_2128281) baseStart_2128281 baseEnd_2128281 := by
    simpa [prefixWord, tailWord_2128281, baseEnd_2128281] using wordTrace_append hprefix tailTrace_2128281
  have hstable : (prefixWord ++ tailWord_2128281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128281).length < 2 ^ (prefixWord ++ tailWord_2128281).sum := by decide
  have hdescent : baseEnd_2128281 < baseStart_2128281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128285 : List Nat := [1, 4, 2, 1, 4, 1, 3, 6]
def baseStart_2128285 : Nat := 118140960795 + 2128285 * 2 ^ 59
def prefixEnd_2128285 : Nat := 4983230072969 + 3 ^ 40 * 2128285 * 2
def baseEnd_2128285 : Nat := 80950605537356356211089

theorem tailTrace_2128285 : CollatzResearch.WordTrace tailWord_2128285 prefixEnd_2128285 80950605537356356211089 := by
  unfold tailWord_2128285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77624931094594401984818309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51749954063062934656545539 77624931094594401984818309)
  ·
    refine ⟨14554674580236450372153433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77624931094594401984818309 14554674580236450372153433)
    ·
      refine ⟨10916005935177337779115075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14554674580236450372153433 10916005935177337779115075)
      ·
        refine ⟨16374008902766006668672613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916005935177337779115075 16374008902766006668672613)
        ·
          refine ⟨3070126669268626250376115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16374008902766006668672613 3070126669268626250376115)
          ·
            refine ⟨4605190003902939375564173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070126669268626250376115 4605190003902939375564173)
            ·
              refine ⟨1726946251463602265836565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4605190003902939375564173 1726946251463602265836565)
              ·
                refine ⟨80950605537356356211089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1726946251463602265836565 80950605537356356211089)
                ·
                  rfl

theorem cell22_2128285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 6].length) (baseStart_2128285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128285 prefixEnd_2128285 := by exact prefixLift 2128285
  have htrace : WordTrace (prefixWord ++ tailWord_2128285) baseStart_2128285 baseEnd_2128285 := by
    simpa [prefixWord, tailWord_2128285, baseEnd_2128285] using wordTrace_append hprefix tailTrace_2128285
  have hstable : (prefixWord ++ tailWord_2128285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128285).length < 2 ^ (prefixWord ++ tailWord_2128285).sum := by decide
  have hdescent : baseEnd_2128285 < baseStart_2128285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128313 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 7]
def baseStart_2128313 : Nat := 118140960795 + 2128313 * 2 ^ 59
def prefixEnd_2128313 : Nat := 4983230072969 + 3 ^ 40 * 2128313 * 2
def baseEnd_2128313 : Nat := 242855011602808155399905

theorem tailTrace_2128313 : CollatzResearch.WordTrace tailWord_2128313 prefixEnd_2128313 242855011602808155399905 := by
  unfold tailWord_2128313
  simp only [CollatzResearch.WordTrace]
  refine ⟨77625952338492962766837593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51750634892328641844558395 77625952338492962766837593)
  ·
    refine ⟨58219464253869722075128195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77625952338492962766837593 58219464253869722075128195)
    ·
      refine ⟨87329196380804583112692293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58219464253869722075128195 87329196380804583112692293)
      ·
        refine ⟨16374224321400859333629805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87329196380804583112692293 16374224321400859333629805)
        ·
          refine ⟨6140334120525322250111177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16374224321400859333629805 6140334120525322250111177)
          ·
            refine ⟨4605250590393991687583383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6140334120525322250111177 4605250590393991687583383)
            ·
              refine ⟨6907875885590987531375075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605250590393991687583383 6907875885590987531375075)
              ·
                refine ⟨10361813828386481297062613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6907875885590987531375075 10361813828386481297062613)
                ·
                  refine ⟨242855011602808155399905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10361813828386481297062613 242855011602808155399905)
                  ·
                    rfl

theorem cell22_2128313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_2128313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128313 prefixEnd_2128313 := by exact prefixLift 2128313
  have htrace : WordTrace (prefixWord ++ tailWord_2128313) baseStart_2128313 baseEnd_2128313 := by
    simpa [prefixWord, tailWord_2128313, baseEnd_2128313] using wordTrace_append hprefix tailTrace_2128313
  have hstable : (prefixWord ++ tailWord_2128313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128313).length < 2 ^ (prefixWord ++ tailWord_2128313).sum := by decide
  have hdescent : baseEnd_2128313 < baseStart_2128313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128317 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_2128317 : Nat := 118140960795 + 2128317 * 2 ^ 59
def prefixEnd_2128317 : Nat := 4983230072969 + 3 ^ 40 * 2128317 * 2
def baseEnd_2128317 : Nat := 728566404090169789099703

theorem tailTrace_2128317 : CollatzResearch.WordTrace tailWord_2128317 prefixEnd_2128317 728566404090169789099703 := by
  unfold tailWord_2128317
  simp only [CollatzResearch.WordTrace]
  refine ⟨77626098230478471449983205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51750732153652314299988803 77626098230478471449983205)
  ·
    refine ⟨14554893418214713396871851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77626098230478471449983205 14554893418214713396871851)
    ·
      refine ⟨21832340127322070095307777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14554893418214713396871851 21832340127322070095307777)
      ·
        refine ⟨16374255095491552571480833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21832340127322070095307777 16374255095491552571480833)
        ·
          refine ⟨12280691321618664428610625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16374255095491552571480833 12280691321618664428610625)
          ·
            refine ⟨9210518491213998321457969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12280691321618664428610625 9210518491213998321457969)
            ·
              refine ⟨6907888868410498741093477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9210518491213998321457969 6907888868410498741093477)
              ·
                refine ⟨1295229162826968513955027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6907888868410498741093477 1295229162826968513955027)
                ·
                  refine ⟨1942843744240452770932541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295229162826968513955027 1942843744240452770932541)
                  ·
                    refine ⟨728566404090169789099703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942843744240452770932541 728566404090169789099703)
                    ·
                      rfl

theorem cell22_2128317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_2128317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128317 prefixEnd_2128317 := by exact prefixLift 2128317
  have htrace : WordTrace (prefixWord ++ tailWord_2128317) baseStart_2128317 baseEnd_2128317 := by
    simpa [prefixWord, tailWord_2128317, baseEnd_2128317] using wordTrace_append hprefix tailTrace_2128317
  have hstable : (prefixWord ++ tailWord_2128317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128317).length < 2 ^ (prefixWord ++ tailWord_2128317).sum := by decide
  have hdescent : baseEnd_2128317 < baseStart_2128317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128328 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2128328 : Nat := 118140960795 + 2128328 * 2 ^ 59
def prefixEnd_2128328 : Nat := 4983230072969 + 3 ^ 40 * 2128328 * 2
def baseEnd_2128328 : Nat := 728570169614969427074669

theorem tailTrace_2128328 : CollatzResearch.WordTrace tailWord_2128328 prefixEnd_2128328 728570169614969427074669 := by
  unfold tailWord_2128328
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813249716719310164316819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51750999622292413552422425 38813249716719310164316819)
  ·
    refine ⟨58219874575078965246475229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38813249716719310164316819 58219874575078965246475229)
    ·
      refine ⟨21832452965654611967428211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58219874575078965246475229 21832452965654611967428211)
      ·
        refine ⟨32748679448481917951142317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21832452965654611967428211 32748679448481917951142317)
        ·
          refine ⟨12280754793180719231678369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32748679448481917951142317 12280754793180719231678369)
          ·
            refine ⟨9210566094885539423758777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12280754793180719231678369 9210566094885539423758777)
            ·
              refine ⟨6907924571164154567819083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9210566094885539423758777 6907924571164154567819083)
              ·
                refine ⟨10361886856746231851728625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6907924571164154567819083 10361886856746231851728625)
                ·
                  refine ⟨7771415142559673888796469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10361886856746231851728625 7771415142559673888796469)
                  ·
                    refine ⟨728570169614969427074669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7771415142559673888796469 728570169614969427074669)
                    ·
                      rfl

theorem cell22_2128328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2128328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128328 prefixEnd_2128328 := by exact prefixLift 2128328
  have htrace : WordTrace (prefixWord ++ tailWord_2128328) baseStart_2128328 baseEnd_2128328 := by
    simpa [prefixWord, tailWord_2128328, baseEnd_2128328] using wordTrace_append hprefix tailTrace_2128328
  have hstable : (prefixWord ++ tailWord_2128328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128328).length < 2 ^ (prefixWord ++ tailWord_2128328).sum := by decide
  have hdescent : baseEnd_2128328 < baseStart_2128328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128330 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_2128330 : Nat := 118140960795 + 2128330 * 2 ^ 59
def prefixEnd_2128330 : Nat := 4983230072969 + 3 ^ 40 * 2128330 * 2
def baseEnd_2128330 : Nat := 242856951418614029508221

theorem tailTrace_2128330 : CollatzResearch.WordTrace tailWord_2128330 prefixEnd_2128330 242856951418614029508221 := by
  unfold tailWord_2128330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19406643094857843667551611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51751048252954249780137629 19406643094857843667551611)
  ·
    refine ⟨29109964642286765501327417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19406643094857843667551611 29109964642286765501327417)
    ·
      refine ⟨21832473481715074125995563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29109964642286765501327417 21832473481715074125995563)
      ·
        refine ⟨32748710222572611188993345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21832473481715074125995563 32748710222572611188993345)
        ·
          refine ⟨24561532666929458391745009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32748710222572611188993345 24561532666929458391745009)
          ·
            refine ⟨18421149500197093793808757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24561532666929458391745009 18421149500197093793808757)
            ·
              refine ⟨1726982765643477543169571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18421149500197093793808757 1726982765643477543169571)
              ·
                refine ⟨2590474148465216314754357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726982765643477543169571 2590474148465216314754357)
                ·
                  refine ⟨242856951418614029508221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2590474148465216314754357 242856951418614029508221)
                  ·
                    rfl

theorem cell22_2128330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_2128330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128330 prefixEnd_2128330 := by exact prefixLift 2128330
  have htrace : WordTrace (prefixWord ++ tailWord_2128330) baseStart_2128330 baseEnd_2128330 := by
    simpa [prefixWord, tailWord_2128330, baseEnd_2128330] using wordTrace_append hprefix tailTrace_2128330
  have hstable : (prefixWord ++ tailWord_2128330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128330).length < 2 ^ (prefixWord ++ tailWord_2128330).sum := by decide
  have hdescent : baseEnd_2128330 < baseStart_2128330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128360 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2128360 : Nat := 118140960795 + 2128360 * 2 ^ 59
def prefixEnd_2128360 : Nat := 4983230072969 + 3 ^ 40 * 2128360 * 2
def baseEnd_2128360 : Nat := 728581123868932010274571

theorem tailTrace_2128360 : CollatzResearch.WordTrace tailWord_2128360 prefixEnd_2128360 728581123868932010274571 := by
  unfold tailWord_2128360
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813833284661344896899267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51751777712881793195865689 38813833284661344896899267)
  ·
    refine ⟨58220749926992017345348901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38813833284661344896899267 58220749926992017345348901)
    ·
      refine ⟨10916390611311003252252919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58220749926992017345348901 10916390611311003252252919)
      ·
        refine ⟨16374585916966504878379379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916390611311003252252919 16374585916966504878379379)
        ·
          refine ⟨24561878875449757317569069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16374585916966504878379379 24561878875449757317569069)
          ·
            refine ⟨9210704578293658994088401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24561878875449757317569069 9210704578293658994088401)
            ·
              refine ⟨6908028433720244245566301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9210704578293658994088401 6908028433720244245566301)
              ·
                refine ⟨2590510662645091592087363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6908028433720244245566301 2590510662645091592087363)
                ·
                  refine ⟨3885765993967637388131045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590510662645091592087363 3885765993967637388131045)
                  ·
                    refine ⟨728581123868932010274571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885765993967637388131045 728581123868932010274571)
                    ·
                      rfl

theorem cell22_2128360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2128360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128360 prefixEnd_2128360 := by exact prefixLift 2128360
  have htrace : WordTrace (prefixWord ++ tailWord_2128360) baseStart_2128360 baseEnd_2128360 := by
    simpa [prefixWord, tailWord_2128360, baseEnd_2128360] using wordTrace_append hprefix tailTrace_2128360
  have hstable : (prefixWord ++ tailWord_2128360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128360).length < 2 ^ (prefixWord ++ tailWord_2128360).sum := by decide
  have hdescent : baseEnd_2128360 < baseStart_2128360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128405 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2128405 : Nat := 118140960795 + 2128405 * 2 ^ 59
def prefixEnd_2128405 : Nat := 4983230072969 + 3 ^ 40 * 2128405 * 2
def baseEnd_2128405 : Nat := 728596528288566892899433

theorem tailTrace_2128405 : CollatzResearch.WordTrace tailWord_2128405 prefixEnd_2128405 728596528288566892899433 := by
  unfold tailWord_2128405
  simp only [CollatzResearch.WordTrace]
  refine ⟨77629307854159662479186669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51752871902773108319457779 77629307854159662479186669)
  ·
    refine ⟨29110990445309873429695001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77629307854159662479186669 29110990445309873429695001)
    ·
      refine ⟨21833242833982405072271251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29110990445309873429695001 21833242833982405072271251)
      ·
        refine ⟨32749864250973607608406877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21833242833982405072271251 32749864250973607608406877)
        ·
          refine ⟨12281199094115102853152579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32749864250973607608406877 12281199094115102853152579)
          ·
            refine ⟨18421798641172654279728869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12281199094115102853152579 18421798641172654279728869)
            ·
              refine ⟨3454087245219872677449163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18421798641172654279728869 3454087245219872677449163)
              ·
                refine ⟨5181130867829809016173745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454087245219872677449163 5181130867829809016173745)
                ·
                  refine ⟨3885848150872356762130309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5181130867829809016173745 3885848150872356762130309)
                  ·
                    refine ⟨728596528288566892899433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885848150872356762130309 728596528288566892899433)
                    ·
                      rfl

theorem cell22_2128405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2128405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128405 prefixEnd_2128405 := by exact prefixLift 2128405
  have htrace : WordTrace (prefixWord ++ tailWord_2128405) baseStart_2128405 baseEnd_2128405 := by
    simpa [prefixWord, tailWord_2128405, baseEnd_2128405] using wordTrace_append hprefix tailTrace_2128405
  have hstable : (prefixWord ++ tailWord_2128405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128405).length < 2 ^ (prefixWord ++ tailWord_2128405).sum := by decide
  have hdescent : baseEnd_2128405 < baseStart_2128405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128407 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 1, 5]
def baseStart_2128407 : Nat := 118140960795 + 2128407 * 2 ^ 59
def prefixEnd_2128407 : Nat := 4983230072969 + 3 ^ 40 * 2128407 * 2
def baseEnd_2128407 : Nat := 728597212929439554349427

theorem tailTrace_2128407 : CollatzResearch.WordTrace tailWord_2128407 prefixEnd_2128407 728597212929439554349427 := by
  unfold tailWord_2128407
  simp only [CollatzResearch.WordTrace]
  refine ⟨77629380800152416820759475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51752920533434944547172983 77629380800152416820759475)
  ·
    refine ⟨116444071200228625231139213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77629380800152416820759475 116444071200228625231139213)
    ·
      refine ⟨43666526700085734461677205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116444071200228625231139213 43666526700085734461677205)
      ·
        refine ⟨2046868439066518802891119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43666526700085734461677205 2046868439066518802891119)
        ·
          refine ⟨3070302658599778204336679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046868439066518802891119 3070302658599778204336679)
          ·
            refine ⟨4605453987899667306505019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070302658599778204336679 4605453987899667306505019)
            ·
              refine ⟨6908180981849500959757529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605453987899667306505019 6908180981849500959757529)
              ·
                refine ⟨5181135736387125719818147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6908180981849500959757529 5181135736387125719818147)
                ·
                  refine ⟨7771703604580688579727221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181135736387125719818147 7771703604580688579727221)
                  ·
                    refine ⟨728597212929439554349427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7771703604580688579727221 728597212929439554349427)
                    ·
                      rfl

theorem cell22_2128407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_2128407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128407 prefixEnd_2128407 := by exact prefixLift 2128407
  have htrace : WordTrace (prefixWord ++ tailWord_2128407) baseStart_2128407 baseEnd_2128407 := by
    simpa [prefixWord, tailWord_2128407, baseEnd_2128407] using wordTrace_append hprefix tailTrace_2128407
  have hstable : (prefixWord ++ tailWord_2128407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128407).length < 2 ^ (prefixWord ++ tailWord_2128407).sum := by decide
  have hdescent : baseEnd_2128407 < baseStart_2128407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128420 : List Nat := [2, 3, 1, 5, 1, 10]
def baseStart_2128420 : Nat := 118140960795 + 2128420 * 2 ^ 59
def prefixEnd_2128420 : Nat := 4983230072969 + 3 ^ 40 * 2128420 * 2
def baseEnd_2128420 : Nat := 8995082260433479676227

theorem tailTrace_2128420 : CollatzResearch.WordTrace tailWord_2128420 prefixEnd_2128420 8995082260433479676227 := by
  unfold tailWord_2128420
  simp only [CollatzResearch.WordTrace]
  refine ⟨38814927474552660020491357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51753236632736880027321809 38814927474552660020491357)
  ·
    refine ⟨14555597802957247507684259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38814927474552660020491357 14555597802957247507684259)
    ·
      refine ⟨21833396704435871261526389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14555597802957247507684259 21833396704435871261526389)
      ·
        refine ⟨2046880941040862930768099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21833396704435871261526389 2046880941040862930768099)
        ·
          refine ⟨3070321411561294396152149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046880941040862930768099 3070321411561294396152149)
          ·
            refine ⟨8995082260433479676227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3070321411561294396152149 8995082260433479676227)
            ·
              rfl

theorem cell22_2128420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 10].length) (baseStart_2128420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128420 prefixEnd_2128420 := by exact prefixLift 2128420
  have htrace : WordTrace (prefixWord ++ tailWord_2128420) baseStart_2128420 baseEnd_2128420 := by
    simpa [prefixWord, tailWord_2128420, baseEnd_2128420] using wordTrace_append hprefix tailTrace_2128420
  have hstable : (prefixWord ++ tailWord_2128420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128420).length < 2 ^ (prefixWord ++ tailWord_2128420).sum := by decide
  have hdescent : baseEnd_2128420 < baseStart_2128420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128424 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2128424 : Nat := 118140960795 + 2128424 * 2 ^ 59
def prefixEnd_2128424 : Nat := 4983230072969 + 3 ^ 40 * 2128424 * 2
def baseEnd_2128424 : Nat := 728603032376857176674375

theorem tailTrace_2128424 : CollatzResearch.WordTrace tailWord_2128424 prefixEnd_2128424 728603032376857176674375 := by
  unfold tailWord_2128424
  simp only [CollatzResearch.WordTrace]
  refine ⟨38815000420545414362064163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51753333894060552482752217 38815000420545414362064163)
  ·
    refine ⟨58222500630818121543096245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38815000420545414362064163 58222500630818121543096245)
    ·
      refine ⟨5458359434139198894665273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58222500630818121543096245 5458359434139198894665273)
      ·
        refine ⟨4093769575604399170998955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5458359434139198894665273 4093769575604399170998955)
        ·
          refine ⟨6140654363406598756498433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093769575604399170998955 6140654363406598756498433)
          ·
            refine ⟨4605490772554949067373825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6140654363406598756498433 4605490772554949067373825)
            ·
              refine ⟨3454118079416211800530369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4605490772554949067373825 3454118079416211800530369)
              ·
                refine ⟨2590588559562158850397777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3454118079416211800530369 2590588559562158850397777)
                ·
                  refine ⟨1942941419671619137798333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590588559562158850397777 1942941419671619137798333)
                  ·
                    refine ⟨728603032376857176674375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942941419671619137798333 728603032376857176674375)
                    ·
                      rfl

theorem cell22_2128424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2128424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128424 prefixEnd_2128424 := by exact prefixLift 2128424
  have htrace : WordTrace (prefixWord ++ tailWord_2128424) baseStart_2128424 baseEnd_2128424 := by
    simpa [prefixWord, tailWord_2128424, baseEnd_2128424] using wordTrace_append hprefix tailTrace_2128424
  have hstable : (prefixWord ++ tailWord_2128424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128424).length < 2 ^ (prefixWord ++ tailWord_2128424).sum := by decide
  have hdescent : baseEnd_2128424 < baseStart_2128424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128433 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2128433 : Nat := 118140960795 + 2128433 * 2 ^ 59
def prefixEnd_2128433 : Nat := 4983230072969 + 3 ^ 40 * 2128433 * 2
def baseEnd_2128433 : Nat := 728606113260784153199347

theorem tailTrace_2128433 : CollatzResearch.WordTrace tailWord_2128433 prefixEnd_2128433 728606113260784153199347 := by
  unfold tailWord_2128433
  simp only [CollatzResearch.WordTrace]
  refine ⟨77630329098058223261205953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51753552732038815507470635 77630329098058223261205953)
  ·
    refine ⟨58222746823543667445904465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77630329098058223261205953 58222746823543667445904465)
    ·
      refine ⟨43667060117657750584428349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58222746823543667445904465 43667060117657750584428349)
      ·
        refine ⟨16375147544121656469160631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43667060117657750584428349 16375147544121656469160631)
        ·
          refine ⟨24562721316182484703740947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16375147544121656469160631 24562721316182484703740947)
          ·
            refine ⟨36844081974273727055611421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24562721316182484703740947 36844081974273727055611421)
            ·
              refine ⟨13816530740352647645854283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36844081974273727055611421 13816530740352647645854283)
              ·
                refine ⟨20724796110528971468781425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13816530740352647645854283 20724796110528971468781425)
                ·
                  refine ⟨15543597082896728601586069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20724796110528971468781425 15543597082896728601586069)
                  ·
                    refine ⟨728606113260784153199347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15543597082896728601586069 728606113260784153199347)
                    ·
                      rfl

theorem cell22_2128433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2128433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128433 prefixEnd_2128433 := by exact prefixLift 2128433
  have htrace : WordTrace (prefixWord ++ tailWord_2128433) baseStart_2128433 baseEnd_2128433 := by
    simpa [prefixWord, tailWord_2128433, baseEnd_2128433] using wordTrace_append hprefix tailTrace_2128433
  have hstable : (prefixWord ++ tailWord_2128433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128433).length < 2 ^ (prefixWord ++ tailWord_2128433).sum := by decide
  have hdescent : baseEnd_2128433 < baseStart_2128433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128435 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 3, 3]
def baseStart_2128435 : Nat := 118140960795 + 2128435 * 2 ^ 59
def prefixEnd_2128435 : Nat := 4983230072969 + 3 ^ 40 * 2128435 * 2
def baseEnd_2128435 : Nat := 728606797901656814649341

theorem tailTrace_2128435 : CollatzResearch.WordTrace tailWord_2128435 prefixEnd_2128435 728606797901656814649341 := by
  unfold tailWord_2128435
  simp only [CollatzResearch.WordTrace]
  refine ⟨77630402044050977602778759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51753601362700651735185839 77630402044050977602778759)
  ·
    refine ⟨116445603066076466404168139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77630402044050977602778759 116445603066076466404168139)
    ·
      refine ⟨174668404599114699606252209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116445603066076466404168139 174668404599114699606252209)
      ·
        refine ⟨131001303449336024704689157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174668404599114699606252209 131001303449336024704689157)
        ·
          refine ⟨24562744396750504632129217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131001303449336024704689157 24562744396750504632129217)
          ·
            refine ⟨18422058297562878474096913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24562744396750504632129217 18422058297562878474096913)
            ·
              refine ⟨13816543723172158855572685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18422058297562878474096913 13816543723172158855572685)
              ·
                refine ⟨5181203896189559570839757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13816543723172158855572685 5181203896189559570839757)
                ·
                  refine ⟨1942951461071084839064909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5181203896189559570839757 1942951461071084839064909)
                  ·
                    refine ⟨728606797901656814649341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942951461071084839064909 728606797901656814649341)
                    ·
                      rfl

theorem cell22_2128435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 3].length) (baseStart_2128435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128435 prefixEnd_2128435 := by exact prefixLift 2128435
  have htrace : WordTrace (prefixWord ++ tailWord_2128435) baseStart_2128435 baseEnd_2128435 := by
    simpa [prefixWord, tailWord_2128435, baseEnd_2128435] using wordTrace_append hprefix tailTrace_2128435
  have hstable : (prefixWord ++ tailWord_2128435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128435).length < 2 ^ (prefixWord ++ tailWord_2128435).sum := by decide
  have hdescent : baseEnd_2128435 < baseStart_2128435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128454 : List Nat := [6, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2128454 : Nat := 118140960795 + 2128454 * 2 ^ 59
def prefixEnd_2128454 : Nat := 4983230072969 + 3 ^ 40 * 2128454 * 2
def baseEnd_2128454 : Nat := 80957033554438566491587

theorem tailTrace_2128454 : CollatzResearch.WordTrace tailWord_2128454 prefixEnd_2128454 80957033554438566491587 := by
  unfold tailWord_2128454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2425971719718191995241263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51754063353988095898480277 2425971719718191995241263)
  ·
    refine ⟨3638957579577287992861895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2425971719718191995241263 3638957579577287992861895)
    ·
      refine ⟨5458436369365931989292843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3638957579577287992861895 5458436369365931989292843)
      ·
        refine ⟨8187654554048897983939265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458436369365931989292843 8187654554048897983939265)
        ·
          refine ⟨6140740915536673487954449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8187654554048897983939265 6140740915536673487954449)
          ·
            refine ⟨4605555686652505115965837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6140740915536673487954449 4605555686652505115965837)
            ·
              refine ⟨1727083382494689418487189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4605555686652505115965837 1727083382494689418487189)
              ·
                refine ⟨80957033554438566491587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1727083382494689418487189 80957033554438566491587)
                ·
                  rfl

theorem cell22_2128454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2128454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128454 prefixEnd_2128454 := by exact prefixLift 2128454
  have htrace : WordTrace (prefixWord ++ tailWord_2128454) baseStart_2128454 baseEnd_2128454 := by
    simpa [prefixWord, tailWord_2128454, baseEnd_2128454] using wordTrace_append hprefix tailTrace_2128454
  have hstable : (prefixWord ++ tailWord_2128454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128454).length < 2 ^ (prefixWord ++ tailWord_2128454).sum := by decide
  have hdescent : baseEnd_2128454 < baseStart_2128454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128512 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_2128512 : Nat := 118140960795 + 2128512 * 2 ^ 59
def prefixEnd_2128512 : Nat := 4983230072969 + 3 ^ 40 * 2128512 * 2
def baseEnd_2128512 : Nat := 728633156575254280474105

theorem tailTrace_2128512 : CollatzResearch.WordTrace tailWord_2128512 prefixEnd_2128512 728633156575254280474105 := by
  unfold tailWord_2128512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38816605232386009876665895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51755473643181346502221193 38816605232386009876665895)
  ·
    refine ⟨58224907848579014814998843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38816605232386009876665895 58224907848579014814998843)
    ·
      refine ⟨87337361772868522222498265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58224907848579014814998843 87337361772868522222498265)
      ·
        refine ⟨65503021329651391666873699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87337361772868522222498265 65503021329651391666873699)
        ·
          refine ⟨98254531994477087500310549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65503021329651391666873699 98254531994477087500310549)
          ·
            refine ⟨4605681187241113476577057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98254531994477087500310549 4605681187241113476577057)
            ·
              refine ⟨3454260890430835107432793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4605681187241113476577057 3454260890430835107432793)
              ·
                refine ⟨2590695667823126330574595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3454260890430835107432793 2590695667823126330574595)
                ·
                  refine ⟨3886043501734689495861893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590695667823126330574595 3886043501734689495861893)
                  ·
                    refine ⟨728633156575254280474105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3886043501734689495861893 728633156575254280474105)
                    ·
                      rfl

theorem cell22_2128512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_2128512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128512 prefixEnd_2128512 := by exact prefixLift 2128512
  have htrace : WordTrace (prefixWord ++ tailWord_2128512) baseStart_2128512 baseEnd_2128512 := by
    simpa [prefixWord, tailWord_2128512, baseEnd_2128512] using wordTrace_append hprefix tailTrace_2128512
  have hstable : (prefixWord ++ tailWord_2128512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128512).length < 2 ^ (prefixWord ++ tailWord_2128512).sum := by decide
  have hdescent : baseEnd_2128512 < baseStart_2128512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128544 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 6]
def baseStart_2128544 : Nat := 118140960795 + 2128544 * 2 ^ 59
def prefixEnd_2128544 : Nat := 4983230072969 + 3 ^ 40 * 2128544 * 2
def baseEnd_2128544 : Nat := 242881370276405621224669

theorem tailTrace_2128544 : CollatzResearch.WordTrace tailWord_2128544 prefixEnd_2128544 242881370276405621224669 := by
  unfold tailWord_2128544
  simp only [CollatzResearch.WordTrace]
  refine ⟨38817188800328044609248343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51756251733770726145664457 38817188800328044609248343)
  ·
    refine ⟨58225783200492066913872515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38817188800328044609248343 58225783200492066913872515)
    ·
      refine ⟨87338674800738100370808773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58225783200492066913872515 87338674800738100370808773)
      ·
        refine ⟨16376001525138393819526645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87338674800738100370808773 16376001525138393819526645)
        ·
          refine ⟨1535250142981724420580623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16376001525138393819526645 1535250142981724420580623)
          ·
            refine ⟨2302875214472586630870935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535250142981724420580623 2302875214472586630870935)
            ·
              refine ⟨3454312821708879946306403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302875214472586630870935 3454312821708879946306403)
              ·
                refine ⟨5181469232563319919459605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454312821708879946306403 5181469232563319919459605)
                ·
                  refine ⟨242881370276405621224669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5181469232563319919459605 242881370276405621224669)
                  ·
                    rfl

theorem cell22_2128544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_2128544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128544 prefixEnd_2128544 := by exact prefixLift 2128544
  have htrace : WordTrace (prefixWord ++ tailWord_2128544) baseStart_2128544 baseEnd_2128544 := by
    simpa [prefixWord, tailWord_2128544, baseEnd_2128544] using wordTrace_append hprefix tailTrace_2128544
  have hstable : (prefixWord ++ tailWord_2128544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128544).length < 2 ^ (prefixWord ++ tailWord_2128544).sum := by decide
  have hdescent : baseEnd_2128544 < baseStart_2128544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128559 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 2, 3]
def baseStart_2128559 : Nat := 118140960795 + 2128559 * 2 ^ 59
def prefixEnd_2128559 : Nat := 4983230072969 + 3 ^ 40 * 2128559 * 2
def baseEnd_2128559 : Nat := 728649245635761824548961

theorem tailTrace_2128559 : CollatzResearch.WordTrace tailWord_2128559 prefixEnd_2128559 728649245635761824548961 := by
  unfold tailWord_2128559
  simp only [CollatzResearch.WordTrace]
  refine ⟨77634924695601746780292731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51756616463734497853528487 77634924695601746780292731)
  ·
    refine ⟨116452387043402620170439097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77634924695601746780292731 116452387043402620170439097)
    ·
      refine ⟨87339290282551965127829323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116452387043402620170439097 87339290282551965127829323)
      ·
        refine ⟨131008935423827947691743985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87339290282551965127829323 131008935423827947691743985)
        ·
          refine ⟨98256701567870960768807989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131008935423827947691743985 98256701567870960768807989)
          ·
            refine ⟨9211565771987902572075749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98256701567870960768807989 9211565771987902572075749)
            ·
              refine ⟨1727168582247731732264203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9211565771987902572075749 1727168582247731732264203)
              ·
                refine ⟨2590752873371597598396305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727168582247731732264203 2590752873371597598396305)
                ·
                  refine ⟨1943064655028698198797229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590752873371597598396305 1943064655028698198797229)
                  ·
                    refine ⟨728649245635761824548961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943064655028698198797229 728649245635761824548961)
                    ·
                      rfl

theorem cell22_2128559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_2128559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128559 prefixEnd_2128559 := by exact prefixLift 2128559
  have htrace : WordTrace (prefixWord ++ tailWord_2128559) baseStart_2128559 baseEnd_2128559 := by
    simpa [prefixWord, tailWord_2128559, baseEnd_2128559] using wordTrace_append hprefix tailTrace_2128559
  have hstable : (prefixWord ++ tailWord_2128559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128559).length < 2 ^ (prefixWord ++ tailWord_2128559).sum := by decide
  have hdescent : baseEnd_2128559 < baseStart_2128559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128589 : List Nat := [1, 6, 2, 1, 3, 9]
def baseStart_2128589 : Nat := 118140960795 + 2128589 * 2 ^ 59
def prefixEnd_2128589 : Nat := 4983230072969 + 3 ^ 40 * 2128589 * 2
def baseEnd_2128589 : Nat := 8995796484553725262949

theorem tailTrace_2128589 : CollatzResearch.WordTrace tailWord_2128589 prefixEnd_2128589 8995796484553725262949 := by
  unfold tailWord_2128589
  simp only [CollatzResearch.WordTrace]
  refine ⟨77636018885493061903884821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51757345923662041269256547 77636018885493061903884821)
  ·
    refine ⟨3639188385257487276744601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77636018885493061903884821 3639188385257487276744601)
    ·
      refine ⟨2729391288943115457558451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3639188385257487276744601 2729391288943115457558451)
      ·
        refine ⟨4094086933414673186337677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729391288943115457558451 4094086933414673186337677)
        ·
          refine ⟨1535282600030502444876629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4094086933414673186337677 1535282600030502444876629)
          ·
            refine ⟨8995796484553725262949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1535282600030502444876629 8995796484553725262949)
            ·
              rfl

theorem cell22_2128589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 9].length) (baseStart_2128589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128589 prefixEnd_2128589 := by exact prefixLift 2128589
  have htrace : WordTrace (prefixWord ++ tailWord_2128589) baseStart_2128589 baseEnd_2128589 := by
    simpa [prefixWord, tailWord_2128589, baseEnd_2128589] using wordTrace_append hprefix tailTrace_2128589
  have hstable : (prefixWord ++ tailWord_2128589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128589).length < 2 ^ (prefixWord ++ tailWord_2128589).sum := by decide
  have hdescent : baseEnd_2128589 < baseStart_2128589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128638 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2128638 : Nat := 118140960795 + 2128638 * 2 ^ 59
def prefixEnd_2128638 : Nat := 4983230072969 + 3 ^ 40 * 2128638 * 2
def baseEnd_2128638 : Nat := 728676288950231951823719

theorem tailTrace_2128638 : CollatzResearch.WordTrace tailWord_2128638 prefixEnd_2128638 728676288950231951823719 := by
  unfold tailWord_2128638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9704725757789442909052321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51758537374877028848279045 9704725757789442909052321)
  ·
    refine ⟨7278544318342082181789241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9704725757789442909052321 7278544318342082181789241)
    ·
      refine ⟨5458908238756561636341931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7278544318342082181789241 5458908238756561636341931)
      ·
        refine ⟨8188362358134842454512897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458908238756561636341931 8188362358134842454512897)
        ·
          refine ⟨6141271768601131840884673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8188362358134842454512897 6141271768601131840884673)
          ·
            refine ⟨4605953826450848880663505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6141271768601131840884673 4605953826450848880663505)
            ·
              refine ⟨3454465369838136660497629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4605953826450848880663505 3454465369838136660497629)
              ·
                refine ⟨1295424513689301247686611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3454465369838136660497629 1295424513689301247686611)
                ·
                  refine ⟨1943136770533951871529917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295424513689301247686611 1943136770533951871529917)
                  ·
                    refine ⟨728676288950231951823719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943136770533951871529917 728676288950231951823719)
                    ·
                      rfl

theorem cell22_2128638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2128638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128638 prefixEnd_2128638 := by exact prefixLift 2128638
  have htrace : WordTrace (prefixWord ++ tailWord_2128638) baseStart_2128638 baseEnd_2128638 := by
    simpa [prefixWord, tailWord_2128638, baseEnd_2128638] using wordTrace_append hprefix tailTrace_2128638
  have hstable : (prefixWord ++ tailWord_2128638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128638).length < 2 ^ (prefixWord ++ tailWord_2128638).sum := by decide
  have hdescent : baseEnd_2128638 < baseStart_2128638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128724 : List Nat := [2, 4, 1, 1, 4, 1, 2, 7]
def baseStart_2128724 : Nat := 118140960795 + 2128724 * 2 ^ 59
def prefixEnd_2128724 : Nat := 4983230072969 + 3 ^ 40 * 2128724 * 2
def baseEnd_2128724 : Nat := 80967303167528488241495

theorem tailTrace_2128724 : CollatzResearch.WordTrace tailWord_2128724 prefixEnd_2128724 80967303167528488241495 := by
  unfold tailWord_2128724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38820471370001989980024613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51760628493335986640032817 38820471370001989980024613)
  ·
    refine ⟨7278838381875373121254615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38820471370001989980024613 7278838381875373121254615)
    ·
      refine ⟨10918257572813059681881923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7278838381875373121254615 10918257572813059681881923)
      ·
        refine ⟨16377386359219589522822885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10918257572813059681881923 16377386359219589522822885)
        ·
          refine ⟨3070759942353673035529291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16377386359219589522822885 3070759942353673035529291)
          ·
            refine ⟨4606139913530509553293937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070759942353673035529291 4606139913530509553293937)
            ·
              refine ⟨3454604935147882164970453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4606139913530509553293937 3454604935147882164970453)
              ·
                refine ⟨80967303167528488241495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3454604935147882164970453 80967303167528488241495)
                ·
                  rfl

theorem cell22_2128724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_2128724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128724 prefixEnd_2128724 := by exact prefixLift 2128724
  have htrace : WordTrace (prefixWord ++ tailWord_2128724) baseStart_2128724 baseEnd_2128724 := by
    simpa [prefixWord, tailWord_2128724, baseEnd_2128724] using wordTrace_append hprefix tailTrace_2128724
  have hstable : (prefixWord ++ tailWord_2128724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128724).length < 2 ^ (prefixWord ++ tailWord_2128724).sum := by decide
  have hdescent : baseEnd_2128724 < baseStart_2128724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128773 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_2128773 : Nat := 118140960795 + 2128773 * 2 ^ 59
def prefixEnd_2128773 : Nat := 4983230072969 + 3 ^ 40 * 2128773 * 2
def baseEnd_2128773 : Nat := 728722502209136599698305

theorem tailTrace_2128773 : CollatzResearch.WordTrace tailWord_2128773 prefixEnd_2128773 728722502209136599698305 := by
  unfold tailWord_2128773
  simp only [CollatzResearch.WordTrace]
  refine ⟨77642729916826461328582973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51761819944550974219055315 77642729916826461328582973)
  ·
    refine ⟨29116023718809922998218615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77642729916826461328582973 29116023718809922998218615)
    ·
      refine ⟨43674035578214884497327923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29116023718809922998218615 43674035578214884497327923)
      ·
        refine ⟨65511053367322326745991885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43674035578214884497327923 65511053367322326745991885)
        ·
          refine ⟨24566645012745872529746957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65511053367322326745991885 24566645012745872529746957)
          ·
            refine ⟨9212491879779702198655109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24566645012745872529746957 9212491879779702198655109)
            ·
              refine ⟨1727342227458694162247833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9212491879779702198655109 1727342227458694162247833)
              ·
                refine ⟨1295506670594020621685875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727342227458694162247833 1295506670594020621685875)
                ·
                  refine ⟨1943260005891030932528813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295506670594020621685875 1943260005891030932528813)
                  ·
                    refine ⟨728722502209136599698305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943260005891030932528813 728722502209136599698305)
                    ·
                      rfl

theorem cell22_2128773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_2128773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128773 prefixEnd_2128773 := by exact prefixLift 2128773
  have htrace : WordTrace (prefixWord ++ tailWord_2128773) baseStart_2128773 baseEnd_2128773 := by
    simpa [prefixWord, tailWord_2128773, baseEnd_2128773] using wordTrace_append hprefix tailTrace_2128773
  have hstable : (prefixWord ++ tailWord_2128773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128773).length < 2 ^ (prefixWord ++ tailWord_2128773).sum := by decide
  have hdescent : baseEnd_2128773 < baseStart_2128773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128790 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2128790 : Nat := 118140960795 + 2128790 * 2 ^ 59
def prefixEnd_2128790 : Nat := 4983230072969 + 3 ^ 40 * 2128790 * 2
def baseEnd_2128790 : Nat := 728728321656554222023253

theorem tailTrace_2128790 : CollatzResearch.WordTrace tailWord_2128790 prefixEnd_2128790 728728321656554222023253 := by
  unfold tailWord_2128790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852709372360304576996989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51762233305176582154634549 4852709372360304576996989)
  ·
    refine ⟨1819766014635114216373871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4852709372360304576996989 1819766014635114216373871)
    ·
      refine ⟨2729649021952671324560807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819766014635114216373871 2729649021952671324560807)
      ·
        refine ⟨4094473532929006986841211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729649021952671324560807 4094473532929006986841211)
        ·
          refine ⟨6141710299393510480261817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4094473532929006986841211 6141710299393510480261817)
          ·
            refine ⟨4606282724545132860196363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6141710299393510480261817 4606282724545132860196363)
            ·
              refine ⟨6909424086817699290294545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606282724545132860196363 6909424086817699290294545)
              ·
                refine ⟨5182068065113274467720909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6909424086817699290294545 5182068065113274467720909)
                ·
                  refine ⟨1943275524417477925395341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5182068065113274467720909 1943275524417477925395341)
                  ·
                    refine ⟨728728321656554222023253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943275524417477925395341 728728321656554222023253)
                    ·
                      rfl

theorem cell22_2128790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2128790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128790 prefixEnd_2128790 := by exact prefixLift 2128790
  have htrace : WordTrace (prefixWord ++ tailWord_2128790) baseStart_2128790 baseEnd_2128790 := by
    simpa [prefixWord, tailWord_2128790, baseEnd_2128790] using wordTrace_append hprefix tailTrace_2128790
  have hstable : (prefixWord ++ tailWord_2128790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128790).length < 2 ^ (prefixWord ++ tailWord_2128790).sum := by decide
  have hdescent : baseEnd_2128790 < baseStart_2128790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128799 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 3, 4]
def baseStart_2128799 : Nat := 118140960795 + 2128799 * 2 ^ 59
def prefixEnd_2128799 : Nat := 4983230072969 + 3 ^ 40 * 2128799 * 2
def baseEnd_2128799 : Nat := 728731402540481198548225

theorem tailTrace_2128799 : CollatzResearch.WordTrace tailWord_2128799 prefixEnd_2128799 728731402540481198548225 := by
  unfold tailWord_2128799
  simp only [CollatzResearch.WordTrace]
  refine ⟨77643678214732267769029451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51762452143154845179352967 77643678214732267769029451)
  ·
    refine ⟨116465517322098401653544177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77643678214732267769029451 116465517322098401653544177)
    ·
      refine ⟨87349137991573801240158133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116465517322098401653544177 87349137991573801240158133)
      ·
        refine ⟨8188981686710043866264825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87349137991573801240158133 8188981686710043866264825)
        ·
          refine ⟨6141736265032532899698619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8188981686710043866264825 6141736265032532899698619)
          ·
            refine ⟨9212604397548799349547929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6141736265032532899698619 9212604397548799349547929)
            ·
              refine ⟨6909453298161599512160947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9212604397548799349547929 6909453298161599512160947)
              ·
                refine ⟨10364179947242399268241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6909453298161599512160947 10364179947242399268241421)
                ·
                  refine ⟨3886567480215899725590533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10364179947242399268241421 3886567480215899725590533)
                  ·
                    refine ⟨728731402540481198548225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3886567480215899725590533 728731402540481198548225)
                    ·
                      rfl

theorem cell22_2128799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_2128799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128799 prefixEnd_2128799 := by exact prefixLift 2128799
  have htrace : WordTrace (prefixWord ++ tailWord_2128799) baseStart_2128799 baseEnd_2128799 := by
    simpa [prefixWord, tailWord_2128799, baseEnd_2128799] using wordTrace_append hprefix tailTrace_2128799
  have hstable : (prefixWord ++ tailWord_2128799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128799).length < 2 ^ (prefixWord ++ tailWord_2128799).sum := by decide
  have hdescent : baseEnd_2128799 < baseStart_2128799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128842 : List Nat := [3, 1, 2, 1, 2, 1, 1, 11]
def baseStart_2128842 : Nat := 118140960795 + 2128842 * 2 ^ 59
def prefixEnd_2128842 : Nat := 4983230072969 + 3 ^ 40 * 2128842 * 2
def baseEnd_2128842 : Nat := 80971791368804824413677

theorem tailTrace_2128842 : CollatzResearch.WordTrace tailWord_2128842 prefixEnd_2128842 80971791368804824413677 := by
  unfold tailWord_2128842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19411311638394121528211195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51763497702384324075229853 19411311638394121528211195)
  ·
    refine ⟨29116967457591182292316793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19411311638394121528211195 29116967457591182292316793)
    ·
      refine ⟨21837725593193386719237595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29116967457591182292316793 21837725593193386719237595)
      ·
        refine ⟨32756588389790080078856393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21837725593193386719237595 32756588389790080078856393)
        ·
          refine ⟨24567441292342560059142295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32756588389790080078856393 24567441292342560059142295)
          ·
            refine ⟨36851161938513840088713443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24567441292342560059142295 36851161938513840088713443)
            ·
              refine ⟨55276742907770760133070165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36851161938513840088713443 55276742907770760133070165)
              ·
                refine ⟨80971791368804824413677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55276742907770760133070165 80971791368804824413677)
                ·
                  rfl

theorem cell22_2128842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_2128842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128842 prefixEnd_2128842 := by exact prefixLift 2128842
  have htrace : WordTrace (prefixWord ++ tailWord_2128842) baseStart_2128842 baseEnd_2128842 := by
    simpa [prefixWord, tailWord_2128842, baseEnd_2128842] using wordTrace_append hprefix tailTrace_2128842
  have hstable : (prefixWord ++ tailWord_2128842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128842).length < 2 ^ (prefixWord ++ tailWord_2128842).sum := by decide
  have hdescent : baseEnd_2128842 < baseStart_2128842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128846 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2128846 : Nat := 118140960795 + 2128846 * 2 ^ 59
def prefixEnd_2128846 : Nat := 4983230072969 + 3 ^ 40 * 2128846 * 2
def baseEnd_2128846 : Nat := 728747491600988742623081

theorem tailTrace_2128846 : CollatzResearch.WordTrace tailWord_2128846 prefixEnd_2128846 728747491600988742623081 := by
  unfold tailWord_2128846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9705674055695249349498799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51763594963707996530660261 9705674055695249349498799)
  ·
    refine ⟨14558511083542874024248199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9705674055695249349498799 14558511083542874024248199)
    ·
      refine ⟨21837766625314311036372299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14558511083542874024248199 21837766625314311036372299)
      ·
        refine ⟨32756649937971466554558449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21837766625314311036372299 32756649937971466554558449)
        ·
          refine ⟨24567487453478599915918837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32756649937971466554558449 24567487453478599915918837)
          ·
            refine ⟨2303201948763618742117391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24567487453478599915918837 2303201948763618742117391)
            ·
              refine ⟨3454802923145428113176087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303201948763618742117391 3454802923145428113176087)
              ·
                refine ⟨5182204384718142169764131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454802923145428113176087 5182204384718142169764131)
                ·
                  refine ⟨7773306577077213254646197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182204384718142169764131 7773306577077213254646197)
                  ·
                    refine ⟨728747491600988742623081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7773306577077213254646197 728747491600988742623081)
                    ·
                      rfl

theorem cell22_2128846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2128846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128846 prefixEnd_2128846 := by exact prefixLift 2128846
  have htrace : WordTrace (prefixWord ++ tailWord_2128846) baseStart_2128846 baseEnd_2128846 := by
    simpa [prefixWord, tailWord_2128846, baseEnd_2128846] using wordTrace_append hprefix tailTrace_2128846
  have hstable : (prefixWord ++ tailWord_2128846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128846).length < 2 ^ (prefixWord ++ tailWord_2128846).sum := by decide
  have hdescent : baseEnd_2128846 < baseStart_2128846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128938 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_2128938 : Nat := 118140960795 + 2128938 * 2 ^ 59
def prefixEnd_2128938 : Nat := 4983230072969 + 3 ^ 40 * 2128938 * 2
def baseEnd_2128938 : Nat := 242926328360377056440933

theorem tailTrace_2128938 : CollatzResearch.WordTrace tailWord_2128938 prefixEnd_2128938 242926328360377056440933 := by
  unfold tailWord_2128938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19412186990307173627084867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51765831974152463005559645 19412186990307173627084867)
  ·
    refine ⟨29118280485460760440627301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19412186990307173627084867 29118280485460760440627301)
    ·
      refine ⟨5459677591023892582617619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29118280485460760440627301 5459677591023892582617619)
      ·
        refine ⟨8189516386535838873926429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459677591023892582617619 8189516386535838873926429)
        ·
          refine ⟨3071068644950939577722411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8189516386535838873926429 3071068644950939577722411)
          ·
            refine ⟨4606602967426409366583617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071068644950939577722411 4606602967426409366583617)
            ·
              refine ⟨3454952225569807024937713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4606602967426409366583617 3454952225569807024937713)
              ·
                refine ⟨2591214169177355268703285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3454952225569807024937713 2591214169177355268703285)
                ·
                  refine ⟨242926328360377056440933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2591214169177355268703285 242926328360377056440933)
                  ·
                    rfl

theorem cell22_2128938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_2128938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128938 prefixEnd_2128938 := by exact prefixLift 2128938
  have htrace : WordTrace (prefixWord ++ tailWord_2128938) baseStart_2128938 baseEnd_2128938 := by
    simpa [prefixWord, tailWord_2128938, baseEnd_2128938] using wordTrace_append hprefix tailTrace_2128938
  have hstable : (prefixWord ++ tailWord_2128938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128938).length < 2 ^ (prefixWord ++ tailWord_2128938).sum := by decide
  have hdescent : baseEnd_2128938 < baseStart_2128938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128949 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 6]
def baseStart_2128949 : Nat := 118140960795 + 2128949 * 2 ^ 59
def prefixEnd_2128949 : Nat := 4983230072969 + 3 ^ 40 * 2128949 * 2
def baseEnd_2128949 : Nat := 242927583535310269099255

theorem tailTrace_2128949 : CollatzResearch.WordTrace tailWord_2128949 prefixEnd_2128949 242927583535310269099255 := by
  unfold tailWord_2128949
  simp only [CollatzResearch.WordTrace]
  refine ⟨77649149164188843386989901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51766099442792562257993267 77649149164188843386989901)
  ·
    refine ⟨29118430936570816270121213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77649149164188843386989901 29118430936570816270121213)
    ·
      refine ⟨10919411601214056101295455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29118430936570816270121213 10919411601214056101295455)
      ·
        refine ⟨16379117401821084151943183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10919411601214056101295455 16379117401821084151943183)
        ·
          refine ⟨24568676102731626227914775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16379117401821084151943183 24568676102731626227914775)
          ·
            refine ⟨36853014154097439341872163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24568676102731626227914775 36853014154097439341872163)
            ·
              refine ⟨55279521231146159012808245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36853014154097439341872163 55279521231146159012808245)
              ·
                refine ⟨5182455115419952407450773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55279521231146159012808245 5182455115419952407450773)
                ·
                  refine ⟨242927583535310269099255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5182455115419952407450773 242927583535310269099255)
                  ·
                    rfl

theorem cell22_2128949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_2128949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128949 prefixEnd_2128949 := by exact prefixLift 2128949
  have htrace : WordTrace (prefixWord ++ tailWord_2128949) baseStart_2128949 baseEnd_2128949 := by
    simpa [prefixWord, tailWord_2128949, baseEnd_2128949] using wordTrace_append hprefix tailTrace_2128949
  have hstable : (prefixWord ++ tailWord_2128949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128949).length < 2 ^ (prefixWord ++ tailWord_2128949).sum := by decide
  have hdescent : baseEnd_2128949 < baseStart_2128949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128981 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_2128981 : Nat := 118140960795 + 2128981 * 2 ^ 59
def prefixEnd_2128981 : Nat := 4983230072969 + 3 ^ 40 * 2128981 * 2
def baseEnd_2128981 : Nat := 728793704859893390497667

theorem tailTrace_2128981 : CollatzResearch.WordTrace tailWord_2128981 prefixEnd_2128981 728793704859893390497667 := by
  unfold tailWord_2128981
  simp only [CollatzResearch.WordTrace]
  refine ⟨77650316300072912852154797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51766877533381941901436531 77650316300072912852154797)
  ·
    refine ⟨29118868612527342319558049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77650316300072912852154797 29118868612527342319558049)
    ·
      refine ⟨21839151459395506739668537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29118868612527342319558049 21839151459395506739668537)
      ·
        refine ⟨16379363594546630054751403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21839151459395506739668537 16379363594546630054751403)
        ·
          refine ⟨24569045391819945082127105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16379363594546630054751403 24569045391819945082127105)
          ·
            refine ⟨18426784043864958811595329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24569045391819945082127105 18426784043864958811595329)
            ·
              refine ⟨13820088032898719108696497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18426784043864958811595329 13820088032898719108696497)
              ·
                refine ⟨10365066024674039331522373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13820088032898719108696497 10365066024674039331522373)
                ·
                  refine ⟨1943449879626382374660445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10365066024674039331522373 1943449879626382374660445)
                  ·
                    refine ⟨728793704859893390497667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943449879626382374660445 728793704859893390497667)
                    ·
                      rfl

theorem cell22_2128981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_2128981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2128981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2128981 prefixEnd_2128981 := by exact prefixLift 2128981
  have htrace : WordTrace (prefixWord ++ tailWord_2128981) baseStart_2128981 baseEnd_2128981 := by
    simpa [prefixWord, tailWord_2128981, baseEnd_2128981] using wordTrace_append hprefix tailTrace_2128981
  have hstable : (prefixWord ++ tailWord_2128981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128981).length < 2 ^ (prefixWord ++ tailWord_2128981).sum := by decide
  have hdescent : baseEnd_2128981 < baseStart_2128981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129024 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_2129024 : Nat := 118140960795 + 2129024 * 2 ^ 59
def prefixEnd_2129024 : Nat := 4983230072969 + 3 ^ 40 * 2129024 * 2
def baseEnd_2129024 : Nat := 728808424638655611672535

theorem tailTrace_2129024 : CollatzResearch.WordTrace tailWord_2129024 prefixEnd_2129024 728808424638655611672535 := by
  unfold tailWord_2129024
  simp only [CollatzResearch.WordTrace]
  refine ⟨38825942319458565597985063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51767923092611420797313417 38825942319458565597985063)
  ·
    refine ⟨58238913479187848396977595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38825942319458565597985063 58238913479187848396977595)
    ·
      refine ⟨87358370218781772595466393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58238913479187848396977595 87358370218781772595466393)
      ·
        refine ⟨65518777664086329446599795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87358370218781772595466393 65518777664086329446599795)
        ·
          refine ⟨98278166496129494169899693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65518777664086329446599795 98278166496129494169899693)
          ·
            refine ⟨36854312436048560313712385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98278166496129494169899693 36854312436048560313712385)
            ·
              refine ⟨27640734327036420235284289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36854312436048560313712385 27640734327036420235284289)
              ·
                refine ⟨20730550745277315176463217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27640734327036420235284289 20730550745277315176463217)
                ·
                  refine ⟨15547913058957986382347413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20730550745277315176463217 15547913058957986382347413)
                  ·
                    refine ⟨728808424638655611672535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15547913058957986382347413 728808424638655611672535)
                    ·
                      rfl

theorem cell22_2129024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_2129024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129024 prefixEnd_2129024 := by exact prefixLift 2129024
  have htrace : WordTrace (prefixWord ++ tailWord_2129024) baseStart_2129024 baseEnd_2129024 := by
    simpa [prefixWord, tailWord_2129024, baseEnd_2129024] using wordTrace_append hprefix tailTrace_2129024
  have hstable : (prefixWord ++ tailWord_2129024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129024).length < 2 ^ (prefixWord ++ tailWord_2129024).sum := by decide
  have hdescent : baseEnd_2129024 < baseStart_2129024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129028 : List Nat := [2, 3, 2, 1, 2, 4, 2, 6]
def baseStart_2129028 : Nat := 118140960795 + 2129028 * 2 ^ 59
def prefixEnd_2129028 : Nat := 4983230072969 + 3 ^ 40 * 2129028 * 2
def baseEnd_2129028 : Nat := 80978865991155659396947

theorem tailTrace_2129028 : CollatzResearch.WordTrace tailWord_2129028 prefixEnd_2129028 80978865991155659396947 := by
  unfold tailWord_2129028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38826015265451319939557869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51768020353935093252743825 38826015265451319939557869)
  ·
    refine ⟨14559755724544244977334201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38826015265451319939557869 14559755724544244977334201)
    ·
      refine ⟨10919816793408183733000651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14559755724544244977334201 10919816793408183733000651)
      ·
        refine ⟨16379725190112275599500977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10919816793408183733000651 16379725190112275599500977)
        ·
          refine ⟨12284793892584206699625733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16379725190112275599500977 12284793892584206699625733)
          ·
            refine ⟨2303398854859538756179825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12284793892584206699625733 2303398854859538756179825)
            ·
              refine ⟨1727549141144654067134869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303398854859538756179825 1727549141144654067134869)
              ·
                refine ⟨80978865991155659396947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1727549141144654067134869 80978865991155659396947)
                ·
                  rfl

theorem cell22_2129028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 6].length) (baseStart_2129028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129028 prefixEnd_2129028 := by exact prefixLift 2129028
  have htrace : WordTrace (prefixWord ++ tailWord_2129028) baseStart_2129028 baseEnd_2129028 := by
    simpa [prefixWord, tailWord_2129028, baseEnd_2129028] using wordTrace_append hprefix tailTrace_2129028
  have hstable : (prefixWord ++ tailWord_2129028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129028).length < 2 ^ (prefixWord ++ tailWord_2129028).sum := by decide
  have hdescent : baseEnd_2129028 < baseStart_2129028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129056 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_2129056 : Nat := 118140960795 + 2129056 * 2 ^ 59
def prefixEnd_2129056 : Nat := 4983230072969 + 3 ^ 40 * 2129056 * 2
def baseEnd_2129056 : Nat := 242939792964206064957479

theorem tailTrace_2129056 : CollatzResearch.WordTrace tailWord_2129056 prefixEnd_2129056 242939792964206064957479 := by
  unfold tailWord_2129056
  simp only [CollatzResearch.WordTrace]
  refine ⟨38826525887400600330567511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51768701183200800440756681 38826525887400600330567511)
  ·
    refine ⟨58239788831100900495851267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38826525887400600330567511 58239788831100900495851267)
    ·
      refine ⟨87359683246651350743776901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58239788831100900495851267 87359683246651350743776901)
      ·
        refine ⟨16379940608747128264458169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87359683246651350743776901 16379940608747128264458169)
        ·
          refine ⟨12284955456560346198343627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16379940608747128264458169 12284955456560346198343627)
          ·
            refine ⟨18427433184840519297515441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12284955456560346198343627 18427433184840519297515441)
            ·
              refine ⟨13820574888630389473136581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18427433184840519297515441 13820574888630389473136581)
              ·
                refine ⟨2591357791618198026213109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13820574888630389473136581 2591357791618198026213109)
                ·
                  refine ⟨242939792964206064957479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2591357791618198026213109 242939792964206064957479)
                  ·
                    rfl

theorem cell22_2129056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_2129056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129056 prefixEnd_2129056 := by exact prefixLift 2129056
  have htrace : WordTrace (prefixWord ++ tailWord_2129056) baseStart_2129056 baseEnd_2129056 := by
    simpa [prefixWord, tailWord_2129056, baseEnd_2129056] using wordTrace_append hprefix tailTrace_2129056
  have hstable : (prefixWord ++ tailWord_2129056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129056).length < 2 ^ (prefixWord ++ tailWord_2129056).sum := by decide
  have hdescent : baseEnd_2129056 < baseStart_2129056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129060 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_2129060 : Nat := 118140960795 + 2129060 * 2 ^ 59
def prefixEnd_2129060 : Nat := 4983230072969 + 3 ^ 40 * 2129060 * 2
def baseEnd_2129060 : Nat := 728820748174363517772425

theorem tailTrace_2129060 : CollatzResearch.WordTrace tailWord_2129060 prefixEnd_2129060 728820748174363517772425 := by
  unfold tailWord_2129060
  simp only [CollatzResearch.WordTrace]
  refine ⟨38826598833393354672140317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51768798444524472896187089 38826598833393354672140317)
  ·
    refine ⟨14559974562522508002052619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38826598833393354672140317 14559974562522508002052619)
    ·
      refine ⟨21839961843783762003078929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14559974562522508002052619 21839961843783762003078929)
      ·
        refine ⟨16379971382837821502309197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21839961843783762003078929 16379971382837821502309197)
        ·
          refine ⟨6142489268564183063365949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16379971382837821502309197 6142489268564183063365949)
          ·
            refine ⟨2303433475711568648762231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6142489268564183063365949 2303433475711568648762231)
            ·
              refine ⟨3455150213567352973143347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303433475711568648762231 3455150213567352973143347)
              ·
                refine ⟨5182725320351029459715021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455150213567352973143347 5182725320351029459715021)
                ·
                  refine ⟨1943521995131636047393133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5182725320351029459715021 1943521995131636047393133)
                  ·
                    refine ⟨728820748174363517772425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943521995131636047393133 728820748174363517772425)
                    ·
                      rfl

theorem cell22_2129060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_2129060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129060 prefixEnd_2129060 := by exact prefixLift 2129060
  have htrace : WordTrace (prefixWord ++ tailWord_2129060) baseStart_2129060 baseEnd_2129060 := by
    simpa [prefixWord, tailWord_2129060, baseEnd_2129060] using wordTrace_append hprefix tailTrace_2129060
  have hstable : (prefixWord ++ tailWord_2129060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129060).length < 2 ^ (prefixWord ++ tailWord_2129060).sum := by decide
  have hdescent : baseEnd_2129060 < baseStart_2129060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129073 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 5]
def baseStart_2129073 : Nat := 118140960795 + 2129073 * 2 ^ 59
def prefixEnd_2129073 : Nat := 4983230072969 + 3 ^ 40 * 2129073 * 2
def baseEnd_2129073 : Nat := 242941732780011939065795

theorem tailTrace_2129073 : CollatzResearch.WordTrace tailWord_2129073 prefixEnd_2129073 242941732780011939065795 := by
  unfold tailWord_2129073
  simp only [CollatzResearch.WordTrace]
  refine ⟨77653671815739612564503873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51769114543826408376335915 77653671815739612564503873)
  ·
    refine ⟨58240253861804709423377905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77653671815739612564503873 58240253861804709423377905)
    ·
      refine ⟨43680190396353532067533429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58240253861804709423377905 43680190396353532067533429)
      ·
        refine ⟨4095017849658143631331259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43680190396353532067533429 4095017849658143631331259)
        ·
          refine ⟨6142526774487215446996889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095017849658143631331259 6142526774487215446996889)
          ·
            refine ⟨4606895080865411585247667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6142526774487215446996889 4606895080865411585247667)
            ·
              refine ⟨6910342621298117377871501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606895080865411585247667 6910342621298117377871501)
              ·
                refine ⟨2591378482986794016701813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6910342621298117377871501 2591378482986794016701813)
                ·
                  refine ⟨242941732780011939065795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2591378482986794016701813 242941732780011939065795)
                  ·
                    rfl

theorem cell22_2129073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_2129073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129073 prefixEnd_2129073 := by exact prefixLift 2129073
  have htrace : WordTrace (prefixWord ++ tailWord_2129073) baseStart_2129073 baseEnd_2129073 := by
    simpa [prefixWord, tailWord_2129073, baseEnd_2129073] using wordTrace_append hprefix tailTrace_2129073
  have hstable : (prefixWord ++ tailWord_2129073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129073).length < 2 ^ (prefixWord ++ tailWord_2129073).sum := by decide
  have hdescent : baseEnd_2129073 < baseStart_2129073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129133 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2129133 : Nat := 118140960795 + 2129133 * 2 ^ 59
def prefixEnd_2129133 : Nat := 4983230072969 + 3 ^ 40 * 2129133 * 2
def baseEnd_2129133 : Nat := 728845737566215660697201

theorem tailTrace_2129133 : CollatzResearch.WordTrace tailWord_2129133 prefixEnd_2129133 728845737566215660697201 := by
  unfold tailWord_2129133
  simp only [CollatzResearch.WordTrace]
  refine ⟨77655860195522242811688053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51770573463681495207792035 77655860195522242811688053)
  ·
    refine ⟨7280236893330210263595755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77655860195522242811688053 7280236893330210263595755)
    ·
      refine ⟨10920355339995315395393633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280236893330210263595755 10920355339995315395393633)
      ·
        refine ⟨8190266504996486546545225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10920355339995315395393633 8190266504996486546545225)
        ·
          refine ⟨6142699878747364909908919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8190266504996486546545225 6142699878747364909908919)
          ·
            refine ⟨9214049818121047364863379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6142699878747364909908919 9214049818121047364863379)
            ·
              refine ⟨13821074727181571047295069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9214049818121047364863379 13821074727181571047295069)
              ·
                refine ⟨5182903022693089142735651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13821074727181571047295069 5182903022693089142735651)
                ·
                  refine ⟨7774354534039633714103477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182903022693089142735651 7774354534039633714103477)
                  ·
                    refine ⟨728845737566215660697201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7774354534039633714103477 728845737566215660697201)
                    ·
                      rfl

theorem cell22_2129133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2129133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129133 prefixEnd_2129133 := by exact prefixLift 2129133
  have htrace : WordTrace (prefixWord ++ tailWord_2129133) baseStart_2129133 baseEnd_2129133 := by
    simpa [prefixWord, tailWord_2129133, baseEnd_2129133] using wordTrace_append hprefix tailTrace_2129133
  have hstable : (prefixWord ++ tailWord_2129133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129133).length < 2 ^ (prefixWord ++ tailWord_2129133).sum := by decide
  have hdescent : baseEnd_2129133 < baseStart_2129133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129148 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_2129148 : Nat := 118140960795 + 2129148 * 2 ^ 59
def prefixEnd_2129148 : Nat := 4983230072969 + 3 ^ 40 * 2129148 * 2
def baseEnd_2129148 : Nat := 728850872372760621572155

theorem tailTrace_2129148 : CollatzResearch.WordTrace tailWord_2129148 prefixEnd_2129148 728850872372760621572155 := by
  unfold tailWord_2129148
  simp only [CollatzResearch.WordTrace]
  refine ⟨38828203645233950186742049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51770938193645266915656065 38828203645233950186742049)
  ·
    refine ⟨29121152733925462640056537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38828203645233950186742049 29121152733925462640056537)
    ·
      refine ⟨21840864550444096980042403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29121152733925462640056537 21840864550444096980042403)
      ·
        refine ⟨32761296825666145470063605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21840864550444096980042403 32761296825666145470063605)
        ·
          refine ⟨3071371577406201137818463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32761296825666145470063605 3071371577406201137818463)
          ·
            refine ⟨4607057366109301706727695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071371577406201137818463 4607057366109301706727695)
            ·
              refine ⟨6910586049163952560091543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607057366109301706727695 6910586049163952560091543)
              ·
                refine ⟨10365879073745928840137315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6910586049163952560091543 10365879073745928840137315)
                ·
                  refine ⟨15548818610618893260205973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10365879073745928840137315 15548818610618893260205973)
                  ·
                    refine ⟨728850872372760621572155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15548818610618893260205973 728850872372760621572155)
                    ·
                      rfl

theorem cell22_2129148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_2129148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129148 prefixEnd_2129148 := by exact prefixLift 2129148
  have htrace : WordTrace (prefixWord ++ tailWord_2129148) baseStart_2129148 baseEnd_2129148 := by
    simpa [prefixWord, tailWord_2129148, baseEnd_2129148] using wordTrace_append hprefix tailTrace_2129148
  have hstable : (prefixWord ++ tailWord_2129148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129148).length < 2 ^ (prefixWord ++ tailWord_2129148).sum := by decide
  have hdescent : baseEnd_2129148 < baseStart_2129148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129154 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2129154 : Nat := 118140960795 + 2129154 * 2 ^ 59
def prefixEnd_2129154 : Nat := 4983230072969 + 3 ^ 40 * 2129154 * 2
def baseEnd_2129154 : Nat := 728852926295378605922137

theorem tailTrace_2129154 : CollatzResearch.WordTrace tailWord_2129154 prefixEnd_2129154 728852926295378605922137 := by
  unfold tailWord_2129154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19414156532111540849550629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51771084085630775598801677 19414156532111540849550629)
  ·
    refine ⟨3640154349770913909290743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19414156532111540849550629 3640154349770913909290743)
    ·
      refine ⟨5460231524656370863936115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3640154349770913909290743 5460231524656370863936115)
      ·
        refine ⟨8190347286984556295904173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5460231524656370863936115 8190347286984556295904173)
        ·
          refine ⟨3071380232619208610964065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8190347286984556295904173 3071380232619208610964065)
          ·
            refine ⟨2303535174464406458223049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071380232619208610964065 2303535174464406458223049)
            ·
              refine ⟨1727651380848304843667287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303535174464406458223049 1727651380848304843667287)
              ·
                refine ⟨2591477071272457265500931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727651380848304843667287 2591477071272457265500931)
                ·
                  refine ⟨3887215606908685898251397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591477071272457265500931 3887215606908685898251397)
                  ·
                    refine ⟨728852926295378605922137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3887215606908685898251397 728852926295378605922137)
                    ·
                      rfl

theorem cell22_2129154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2129154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129154 prefixEnd_2129154 := by exact prefixLift 2129154
  have htrace : WordTrace (prefixWord ++ tailWord_2129154) baseStart_2129154 baseEnd_2129154 := by
    simpa [prefixWord, tailWord_2129154, baseEnd_2129154] using wordTrace_append hprefix tailTrace_2129154
  have hstable : (prefixWord ++ tailWord_2129154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129154).length < 2 ^ (prefixWord ++ tailWord_2129154).sum := by decide
  have hdescent : baseEnd_2129154 < baseStart_2129154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129197 : List Nat := [1, 5, 3, 1, 1, 3, 2, 6]
def baseStart_2129197 : Nat := 118140960795 + 2129197 * 2 ^ 59
def prefixEnd_2129197 : Nat := 4983230072969 + 3 ^ 40 * 2129197 * 2
def baseEnd_2129197 : Nat := 80985294008237869677445

theorem tailTrace_2129197 : CollatzResearch.WordTrace tailWord_2129197 prefixEnd_2129197 80985294008237869677445 := by
  unfold tailWord_2129197
  simp only [CollatzResearch.WordTrace]
  refine ⟨77658194467290381742017845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51772129644860254494678563 77658194467290381742017845)
  ·
    refine ⟨7280455731308473288314173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77658194467290381742017845 7280455731308473288314173)
    ·
      refine ⟨2730170899240677483117815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7280455731308473288314173 2730170899240677483117815)
      ·
        refine ⟨4095256348861016224676723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730170899240677483117815 4095256348861016224676723)
        ·
          refine ⟨6142884523291524337015085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095256348861016224676723 6142884523291524337015085)
          ·
            refine ⟨2303581696234321626380657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6142884523291524337015085 2303581696234321626380657)
            ·
              refine ⟨1727686272175741219785493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303581696234321626380657 1727686272175741219785493)
              ·
                refine ⟨80985294008237869677445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1727686272175741219785493 80985294008237869677445)
                ·
                  rfl

theorem cell22_2129197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 6].length) (baseStart_2129197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129197 prefixEnd_2129197 := by exact prefixLift 2129197
  have htrace : WordTrace (prefixWord ++ tailWord_2129197) baseStart_2129197 baseEnd_2129197 := by
    simpa [prefixWord, tailWord_2129197, baseEnd_2129197] using wordTrace_append hprefix tailTrace_2129197
  have hstable : (prefixWord ++ tailWord_2129197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129197).length < 2 ^ (prefixWord ++ tailWord_2129197).sum := by decide
  have hdescent : baseEnd_2129197 < baseStart_2129197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129212 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_2129212 : Nat := 118140960795 + 2129212 * 2 ^ 59
def prefixEnd_2129212 : Nat := 4983230072969 + 3 ^ 40 * 2129212 * 2
def baseEnd_2129212 : Nat := 728872780880685787971959

theorem tailTrace_2129212 : CollatzResearch.WordTrace tailWord_2129212 prefixEnd_2129212 728872780880685787971959 := by
  unfold tailWord_2129212
  simp only [CollatzResearch.WordTrace]
  refine ⟨38829370781118019651906945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51772494374824026202542593 38829370781118019651906945)
  ·
    refine ⟨29122028085838514738930209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38829370781118019651906945 29122028085838514738930209)
    ·
      refine ⟨21841521064378886054197657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29122028085838514738930209 21841521064378886054197657)
      ·
        refine ⟨16381140798284164540648243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21841521064378886054197657 16381140798284164540648243)
        ·
          refine ⟨24571711197426246810972365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16381140798284164540648243 24571711197426246810972365)
          ·
            refine ⟨9214391699034842554114637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24571711197426246810972365 9214391699034842554114637)
            ·
              refine ⟨3455396887138065957792989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9214391699034842554114637 3455396887138065957792989)
              ·
                refine ⟨1295773832676774734172371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455396887138065957792989 1295773832676774734172371)
                ·
                  refine ⟨1943660749015162101258557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295773832676774734172371 1943660749015162101258557)
                  ·
                    refine ⟨728872780880685787971959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943660749015162101258557 728872780880685787971959)
                    ·
                      rfl

theorem cell22_2129212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_2129212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129212 prefixEnd_2129212 := by exact prefixLift 2129212
  have htrace : WordTrace (prefixWord ++ tailWord_2129212) baseStart_2129212 baseEnd_2129212 := by
    simpa [prefixWord, tailWord_2129212, baseEnd_2129212] using wordTrace_append hprefix tailTrace_2129212
  have hstable : (prefixWord ++ tailWord_2129212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129212).length < 2 ^ (prefixWord ++ tailWord_2129212).sum := by decide
  have hdescent : baseEnd_2129212 < baseStart_2129212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129255 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2129255 : Nat := 118140960795 + 2129255 * 2 ^ 59
def prefixEnd_2129255 : Nat := 4983230072969 + 3 ^ 40 * 2129255 * 2
def baseEnd_2129255 : Nat := 728887500659448009146827

theorem tailTrace_2129255 : CollatzResearch.WordTrace tailWord_2129255 prefixEnd_2129255 728887500659448009146827 := by
  unfold tailWord_2129255
  simp only [CollatzResearch.WordTrace]
  refine ⟨77660309901080257647629219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51773539934053505098419479 77660309901080257647629219)
  ·
    refine ⟨116490464851620386471443829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77660309901080257647629219 116490464851620386471443829)
    ·
      refine ⟨10920981079839411231697859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116490464851620386471443829 10920981079839411231697859)
      ·
        refine ⟨16381471619759116847546789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10920981079839411231697859 16381471619759116847546789)
        ·
          refine ⟨3071525928704834408915023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16381471619759116847546789 3071525928704834408915023)
          ·
            refine ⟨4607288893057251613372535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071525928704834408915023 4607288893057251613372535)
            ·
              refine ⟨6910933339585877420058803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607288893057251613372535 6910933339585877420058803)
              ·
                refine ⟨10366400009378816130088205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6910933339585877420058803 10366400009378816130088205)
                ·
                  refine ⟨3887400003517056048783077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10366400009378816130088205 3887400003517056048783077)
                  ·
                    refine ⟨728887500659448009146827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3887400003517056048783077 728887500659448009146827)
                    ·
                      rfl

theorem cell22_2129255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2129255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129255 prefixEnd_2129255 := by exact prefixLift 2129255
  have htrace : WordTrace (prefixWord ++ tailWord_2129255) baseStart_2129255 baseEnd_2129255 := by
    simpa [prefixWord, tailWord_2129255, baseEnd_2129255] using wordTrace_append hprefix tailTrace_2129255
  have hstable : (prefixWord ++ tailWord_2129255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129255).length < 2 ^ (prefixWord ++ tailWord_2129255).sum := by decide
  have hdescent : baseEnd_2129255 < baseStart_2129255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129285 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_2129285 : Nat := 118140960795 + 2129285 * 2 ^ 59
def prefixEnd_2129285 : Nat := 4983230072969 + 3 ^ 40 * 2129285 * 2
def baseEnd_2129285 : Nat := 728897770272537930896735

theorem tailTrace_2129285 : CollatzResearch.WordTrace tailWord_2129285 prefixEnd_2129285 728897770272537930896735 := by
  unfold tailWord_2129285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77661404090971572771221309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51774269393981048514147539 77661404090971572771221309)
  ·
    refine ⟨29123026534114339789207991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77661404090971572771221309 29123026534114339789207991)
    ·
      refine ⟨43684539801171509683811987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29123026534114339789207991 43684539801171509683811987)
      ·
        refine ⟨65526809701757264525717981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43684539801171509683811987 65526809701757264525717981)
        ·
          refine ⟨24572553638158974197144243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65526809701757264525717981 24572553638158974197144243)
          ·
            refine ⟨36858830457238461295716365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24572553638158974197144243 36858830457238461295716365)
            ·
              refine ⟨13822061421464422985893637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36858830457238461295716365 13822061421464422985893637)
              ·
                refine ⟨2591636516524579309855057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13822061421464422985893637 2591636516524579309855057)
                ·
                  refine ⟨1943727387393434482391293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591636516524579309855057 1943727387393434482391293)
                  ·
                    refine ⟨728897770272537930896735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943727387393434482391293 728897770272537930896735)
                    ·
                      rfl

theorem cell22_2129285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_2129285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129285 prefixEnd_2129285 := by exact prefixLift 2129285
  have htrace : WordTrace (prefixWord ++ tailWord_2129285) baseStart_2129285 baseEnd_2129285 := by
    simpa [prefixWord, tailWord_2129285, baseEnd_2129285] using wordTrace_append hprefix tailTrace_2129285
  have hstable : (prefixWord ++ tailWord_2129285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129285).length < 2 ^ (prefixWord ++ tailWord_2129285).sum := by decide
  have hdescent : baseEnd_2129285 < baseStart_2129285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129287 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 4]
def baseStart_2129287 : Nat := 118140960795 + 2129287 * 2 ^ 59
def prefixEnd_2129287 : Nat := 4983230072969 + 3 ^ 40 * 2129287 * 2
def baseEnd_2129287 : Nat := 242966151637803530782243

theorem tailTrace_2129287 : CollatzResearch.WordTrace tailWord_2129287 prefixEnd_2129287 242966151637803530782243 := by
  unfold tailWord_2129287
  simp only [CollatzResearch.WordTrace]
  refine ⟨77661477036964327112794115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51774318024642884741862743 77661477036964327112794115)
  ·
    refine ⟨116492215555446490669191173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77661477036964327112794115 116492215555446490669191173)
    ·
      refine ⟨21842290416646217000473345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116492215555446490669191173 21842290416646217000473345)
      ·
        refine ⟨16381717812484662750355009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21842290416646217000473345 16381717812484662750355009)
        ·
          refine ⟨12286288359363497062766257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16381717812484662750355009 12286288359363497062766257)
          ·
            refine ⟨9214716269522622797074693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12286288359363497062766257 9214716269522622797074693)
            ·
              refine ⟨1727759300535491774451505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9214716269522622797074693 1727759300535491774451505)
              ·
                refine ⟨1295819475401618830838629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727759300535491774451505 1295819475401618830838629)
                ·
                  refine ⟨242966151637803530782243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295819475401618830838629 242966151637803530782243)
                  ·
                    rfl

theorem cell22_2129287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 4].length) (baseStart_2129287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129287 prefixEnd_2129287 := by exact prefixLift 2129287
  have htrace : WordTrace (prefixWord ++ tailWord_2129287) baseStart_2129287 baseEnd_2129287 := by
    simpa [prefixWord, tailWord_2129287, baseEnd_2129287] using wordTrace_append hprefix tailTrace_2129287
  have hstable : (prefixWord ++ tailWord_2129287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129287).length < 2 ^ (prefixWord ++ tailWord_2129287).sum := by decide
  have hdescent : baseEnd_2129287 < baseStart_2129287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129347 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 1, 3]
def baseStart_2129347 : Nat := 118140960795 + 2129347 * 2 ^ 59
def prefixEnd_2129347 : Nat := 4983230072969 + 3 ^ 40 * 2129347 * 2
def baseEnd_2129347 : Nat := 728918994139590435846545

theorem tailTrace_2129347 : CollatzResearch.WordTrace tailWord_2129347 prefixEnd_2129347 728918994139590435846545 := by
  unfold tailWord_2129347
  simp only [CollatzResearch.WordTrace]
  refine ⟨77663665416746957359978295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51775776944497971573318863 77663665416746957359978295)
  ·
    refine ⟨116495498125120436039967443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77663665416746957359978295 116495498125120436039967443)
    ·
      refine ⟨174743247187680654059951165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116495498125120436039967443 174743247187680654059951165)
      ·
        refine ⟨65528717695380245272481687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174743247187680654059951165 65528717695380245272481687)
        ·
          refine ⟨98293076543070367908722531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65528717695380245272481687 98293076543070367908722531)
          ·
            refine ⟨147439614814605551863083797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98293076543070367908722531 147439614814605551863083797)
            ·
              refine ⟨6911231944434635243582053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147439614814605551863083797 6911231944434635243582053)
              ·
                refine ⟨1295855989581494108171635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6911231944434635243582053 1295855989581494108171635)
                ·
                  refine ⟨1943783984372241162257453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295855989581494108171635 1943783984372241162257453)
                  ·
                    refine ⟨728918994139590435846545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943783984372241162257453 728918994139590435846545)
                    ·
                      rfl

theorem cell22_2129347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 3].length) (baseStart_2129347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129347 prefixEnd_2129347 := by exact prefixLift 2129347
  have htrace : WordTrace (prefixWord ++ tailWord_2129347) baseStart_2129347 baseEnd_2129347 := by
    simpa [prefixWord, tailWord_2129347, baseEnd_2129347] using wordTrace_append hprefix tailTrace_2129347
  have hstable : (prefixWord ++ tailWord_2129347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129347).length < 2 ^ (prefixWord ++ tailWord_2129347).sum := by decide
  have hdescent : baseEnd_2129347 < baseStart_2129347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129381 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_2129381 : Nat := 118140960795 + 2129381 * 2 ^ 59
def prefixEnd_2129381 : Nat := 4983230072969 + 3 ^ 40 * 2129381 * 2
def baseEnd_2129381 : Nat := 728930633034425680496441

theorem tailTrace_2129381 : CollatzResearch.WordTrace tailWord_2129381 prefixEnd_2129381 728930633034425680496441 := by
  unfold tailWord_2129381
  simp only [CollatzResearch.WordTrace]
  refine ⟨77664905498623781166715997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51776603665749187444477331 77664905498623781166715997)
  ·
    refine ⟨29124339561983917937518499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77664905498623781166715997 29124339561983917937518499)
    ·
      refine ⟨43686509342975876906277749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29124339561983917937518499 43686509342975876906277749)
      ·
        refine ⟨4095610250903988459963539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43686509342975876906277749 4095610250903988459963539)
        ·
          refine ⟨6143415376355982689945309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095610250903988459963539 6143415376355982689945309)
          ·
            refine ⟨2303780766133493508729491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6143415376355982689945309 2303780766133493508729491)
            ·
              refine ⟨3455671149200240263094237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303780766133493508729491 3455671149200240263094237)
              ·
                refine ⟨1295876680950090098660339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455671149200240263094237 1295876680950090098660339)
                ·
                  refine ⟨1943815021425135147990509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295876680950090098660339 1943815021425135147990509)
                  ·
                    refine ⟨728930633034425680496441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943815021425135147990509 728930633034425680496441)
                    ·
                      rfl

theorem cell22_2129381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_2129381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129381 prefixEnd_2129381 := by exact prefixLift 2129381
  have htrace : WordTrace (prefixWord ++ tailWord_2129381) baseStart_2129381 baseEnd_2129381 := by
    simpa [prefixWord, tailWord_2129381, baseEnd_2129381] using wordTrace_append hprefix tailTrace_2129381
  have hstable : (prefixWord ++ tailWord_2129381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129381).length < 2 ^ (prefixWord ++ tailWord_2129381).sum := by decide
  have hdescent : baseEnd_2129381 < baseStart_2129381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129403 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_2129403 : Nat := 118140960795 + 2129403 * 2 ^ 59
def prefixEnd_2129403 : Nat := 4983230072969 + 3 ^ 40 * 2129403 * 2
def baseEnd_2129403 : Nat := 728938164084024956446373

theorem tailTrace_2129403 : CollatzResearch.WordTrace tailWord_2129403 prefixEnd_2129403 728938164084024956446373 := by
  unfold tailWord_2129403
  simp only [CollatzResearch.WordTrace]
  refine ⟨77665707904544078924016863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51777138603029385949344575 77665707904544078924016863)
  ·
    refine ⟨116498561856816118386025295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77665707904544078924016863 116498561856816118386025295)
    ·
      refine ⟨174747842785224177579037943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116498561856816118386025295 174747842785224177579037943)
      ·
        refine ⟨262121764177836266368556915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174747842785224177579037943 262121764177836266368556915)
        ·
          refine ⟨393182646266754399552835373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262121764177836266368556915 393182646266754399552835373)
          ·
            refine ⟨147443492350032899832313265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393182646266754399552835373 147443492350032899832313265)
            ·
              refine ⟨110582619262524674874234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147443492350032899832313265 110582619262524674874234949)
              ·
                refine ⟨20734241111723376538919053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110582619262524674874234949 20734241111723376538919053)
                ·
                  refine ⟨7775340416896266202094645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20734241111723376538919053 7775340416896266202094645)
                  ·
                    refine ⟨728938164084024956446373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7775340416896266202094645 728938164084024956446373)
                    ·
                      rfl

theorem cell22_2129403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_2129403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129403 prefixEnd_2129403 := by exact prefixLift 2129403
  have htrace : WordTrace (prefixWord ++ tailWord_2129403) baseStart_2129403 baseEnd_2129403 := by
    simpa [prefixWord, tailWord_2129403, baseEnd_2129403] using wordTrace_append hprefix tailTrace_2129403
  have hstable : (prefixWord ++ tailWord_2129403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129403).length < 2 ^ (prefixWord ++ tailWord_2129403).sum := by decide
  have hdescent : baseEnd_2129403 < baseStart_2129403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129405 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 6]
def baseStart_2129405 : Nat := 118140960795 + 2129405 * 2 ^ 59
def prefixEnd_2129405 : Nat := 4983230072969 + 3 ^ 40 * 2129405 * 2
def baseEnd_2129405 : Nat := 242979616241632539298789

theorem tailTrace_2129405 : CollatzResearch.WordTrace tailWord_2129405 prefixEnd_2129405 242979616241632539298789 := by
  unfold tailWord_2129405
  simp only [CollatzResearch.WordTrace]
  refine ⟨77665780850536833265589669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51777187233691222177059779 77665780850536833265589669)
  ·
    refine ⟨14562333909475656237298063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77665780850536833265589669 14562333909475656237298063)
    ·
      refine ⟨21843500864213484355947095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14562333909475656237298063 21843500864213484355947095)
      ·
        refine ⟨32765251296320226533920643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21843500864213484355947095 32765251296320226533920643)
        ·
          refine ⟨49147876944480339800880965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32765251296320226533920643 49147876944480339800880965)
          ·
            refine ⟨9215226927090063712665181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49147876944480339800880965 9215226927090063712665181)
            ·
              refine ⟨3455710097658773892249443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9215226927090063712665181 3455710097658773892249443)
              ·
                refine ⟨5183565146488160838374165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455710097658773892249443 5183565146488160838374165)
                ·
                  refine ⟨242979616241632539298789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5183565146488160838374165 242979616241632539298789)
                  ·
                    rfl

theorem cell22_2129405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_2129405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129405 prefixEnd_2129405 := by exact prefixLift 2129405
  have htrace : WordTrace (prefixWord ++ tailWord_2129405) baseStart_2129405 baseEnd_2129405 := by
    simpa [prefixWord, tailWord_2129405, baseEnd_2129405] using wordTrace_append hprefix tailTrace_2129405
  have hstable : (prefixWord ++ tailWord_2129405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129405).length < 2 ^ (prefixWord ++ tailWord_2129405).sum := by decide
  have hdescent : baseEnd_2129405 < baseStart_2129405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129454 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2129454 : Nat := 118140960795 + 2129454 * 2 ^ 59
def prefixEnd_2129454 : Nat := 4983230072969 + 3 ^ 40 * 2129454 * 2
def baseEnd_2129454 : Nat := 728955622426277823421217

theorem tailTrace_2129454 : CollatzResearch.WordTrace tailWord_2129454 prefixEnd_2129454 728955622426277823421217 := by
  unfold tailWord_2129454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9708446003419914329265427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51778378684906209756082277 9708446003419914329265427)
  ·
    refine ⟨14562669005129871493898141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9708446003419914329265427 14562669005129871493898141)
    ·
      refine ⟨5461000876923701810211803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14562669005129871493898141 5461000876923701810211803)
      ·
        refine ⟨8191501315385552715317705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5461000876923701810211803 8191501315385552715317705)
        ·
          refine ⟨6143625986539164536488279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8191501315385552715317705 6143625986539164536488279)
          ·
            refine ⟨9215438979808746804732419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143625986539164536488279 9215438979808746804732419)
            ·
              refine ⟨13823158469713120207098629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9215438979808746804732419 13823158469713120207098629)
              ·
                refine ⟨2591842213071210038830993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13823158469713120207098629 2591842213071210038830993)
                ·
                  refine ⟨1943881659803407529123245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591842213071210038830993 1943881659803407529123245)
                  ·
                    refine ⟨728955622426277823421217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943881659803407529123245 728955622426277823421217)
                    ·
                      rfl

theorem cell22_2129454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2129454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129454 prefixEnd_2129454 := by exact prefixLift 2129454
  have htrace : WordTrace (prefixWord ++ tailWord_2129454) baseStart_2129454 baseEnd_2129454 := by
    simpa [prefixWord, tailWord_2129454, baseEnd_2129454] using wordTrace_append hprefix tailTrace_2129454
  have hstable : (prefixWord ++ tailWord_2129454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129454).length < 2 ^ (prefixWord ++ tailWord_2129454).sum := by decide
  have hdescent : baseEnd_2129454 < baseStart_2129454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129482 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_2129482 : Nat := 118140960795 + 2129482 * 2 ^ 59
def prefixEnd_2129482 : Nat := 4983230072969 + 3 ^ 40 * 2129482 * 2
def baseEnd_2129482 : Nat := 728965207398495083721131

theorem tailTrace_2129482 : CollatzResearch.WordTrace tailWord_2129482 prefixEnd_2129482 728965207398495083721131 := by
  unfold tailWord_2129482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19417147317814468854035675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51779059514171916944095133 19417147317814468854035675)
  ·
    refine ⟨29125720976721703281053513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19417147317814468854035675 29125720976721703281053513)
    ·
      refine ⟨21844290732541277460790135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29125720976721703281053513 21844290732541277460790135)
      ·
        refine ⟨32766436098811916191185203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21844290732541277460790135 32766436098811916191185203)
        ·
          refine ⟨49149654148217874286777805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32766436098811916191185203 49149654148217874286777805)
          ·
            refine ⟨18431120305581702857541677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49149654148217874286777805 18431120305581702857541677)
            ·
              refine ⟨6911670114593138571578129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18431120305581702857541677 6911670114593138571578129)
              ·
                refine ⟨5183752585944853928683597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6911670114593138571578129 5183752585944853928683597)
                ·
                  refine ⟨1943907219729320223256349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5183752585944853928683597 1943907219729320223256349)
                  ·
                    refine ⟨728965207398495083721131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943907219729320223256349 728965207398495083721131)
                    ·
                      rfl

theorem cell22_2129482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_2129482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129482 prefixEnd_2129482 := by exact prefixLift 2129482
  have htrace : WordTrace (prefixWord ++ tailWord_2129482) baseStart_2129482 baseEnd_2129482 := by
    simpa [prefixWord, tailWord_2129482, baseEnd_2129482] using wordTrace_append hprefix tailTrace_2129482
  have hstable : (prefixWord ++ tailWord_2129482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129482).length < 2 ^ (prefixWord ++ tailWord_2129482).sum := by decide
  have hdescent : baseEnd_2129482 < baseStart_2129482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129512 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_2129512 : Nat := 118140960795 + 2129512 * 2 ^ 59
def prefixEnd_2129512 : Nat := 4983230072969 + 3 ^ 40 * 2129512 * 2
def baseEnd_2129512 : Nat := 242991825670528335157013

theorem tailTrace_2129512 : CollatzResearch.WordTrace tailWord_2129512 prefixEnd_2129512 242991825670528335157013 := by
  unfold tailWord_2129512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38834841730574595269867395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51779788974099460359823193 38834841730574595269867395)
  ·
    refine ⟨58252262595861892904801093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38834841730574595269867395 58252262595861892904801093)
    ·
      refine ⟨10922299236724104919650205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58252262595861892904801093 10922299236724104919650205)
      ·
        refine ⟨4095862213771539344868827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10922299236724104919650205 4095862213771539344868827)
        ·
          refine ⟨6143793320657309017303241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095862213771539344868827 6143793320657309017303241)
          ·
            refine ⟨4607844990492981762977431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6143793320657309017303241 4607844990492981762977431)
            ·
              refine ⟨6911767485739472644466147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607844990492981762977431 6911767485739472644466147)
              ·
                refine ⟨10367651228609208966699221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6911767485739472644466147 10367651228609208966699221)
                ·
                  refine ⟨242991825670528335157013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10367651228609208966699221 242991825670528335157013)
                  ·
                    rfl

theorem cell22_2129512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_2129512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129512 prefixEnd_2129512 := by exact prefixLift 2129512
  have htrace : WordTrace (prefixWord ++ tailWord_2129512) baseStart_2129512 baseEnd_2129512 := by
    simpa [prefixWord, tailWord_2129512, baseEnd_2129512] using wordTrace_append hprefix tailTrace_2129512
  have hstable : (prefixWord ++ tailWord_2129512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129512).length < 2 ^ (prefixWord ++ tailWord_2129512).sum := by decide
  have hdescent : baseEnd_2129512 < baseStart_2129512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129604 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2129604 : Nat := 118140960795 + 2129604 * 2 ^ 59
def prefixEnd_2129604 : Nat := 4983230072969 + 3 ^ 40 * 2129604 * 2
def baseEnd_2129604 : Nat := 729006970491727432170757

theorem tailTrace_2129604 : CollatzResearch.WordTrace tailWord_2129604 prefixEnd_2129604 729006970491727432170757 := by
  unfold tailWord_2129604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38836519488407945126041933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51782025984543926834722577 38836519488407945126041933)
  ·
    refine ⟨14563694808152979422265725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38836519488407945126041933 14563694808152979422265725)
    ·
      refine ⟨5461385553057367283349647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14563694808152979422265725 5461385553057367283349647)
      ·
        refine ⟨8192078329586050925024471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5461385553057367283349647 8192078329586050925024471)
        ·
          refine ⟨12288117494379076387536707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8192078329586050925024471 12288117494379076387536707)
          ·
            refine ⟨18432176241568614581305061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12288117494379076387536707 18432176241568614581305061)
            ·
              refine ⟨3456033045294115233994699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18432176241568614581305061 3456033045294115233994699)
              ·
                refine ⟨5184049567941172850992049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456033045294115233994699 5184049567941172850992049)
                ·
                  refine ⟨3888037175955879638244037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5184049567941172850992049 3888037175955879638244037)
                  ·
                    refine ⟨729006970491727432170757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3888037175955879638244037 729006970491727432170757)
                    ·
                      rfl

theorem cell22_2129604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2129604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129604 prefixEnd_2129604 := by exact prefixLift 2129604
  have htrace : WordTrace (prefixWord ++ tailWord_2129604) baseStart_2129604 baseEnd_2129604 := by
    simpa [prefixWord, tailWord_2129604, baseEnd_2129604] using wordTrace_append hprefix tailTrace_2129604
  have hstable : (prefixWord ++ tailWord_2129604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129604).length < 2 ^ (prefixWord ++ tailWord_2129604).sum := by decide
  have hdescent : baseEnd_2129604 < baseStart_2129604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129606 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2129606 : Nat := 118140960795 + 2129606 * 2 ^ 59
def prefixEnd_2129606 : Nat := 4983230072969 + 3 ^ 40 * 2129606 * 2
def baseEnd_2129606 : Nat := 729007655132600093620751

theorem tailTrace_2129606 : CollatzResearch.WordTrace tailWord_2129606 prefixEnd_2129606 729007655132600093620751 := by
  unfold tailWord_2129606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427284747587770143551771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51782074615205763062437781 2427284747587770143551771)
  ·
    refine ⟨3640927121381655215327657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2427284747587770143551771 3640927121381655215327657)
    ·
      refine ⟨2730695341036241411495743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3640927121381655215327657 2730695341036241411495743)
      ·
        refine ⟨4096043011554362117243615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730695341036241411495743 4096043011554362117243615)
        ·
          refine ⟨6144064517331543175865423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096043011554362117243615 6144064517331543175865423)
          ·
            refine ⟨9216096775997314763798135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6144064517331543175865423 9216096775997314763798135)
            ·
              refine ⟨13824145163995972145697203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9216096775997314763798135 13824145163995972145697203)
              ·
                refine ⟨20736217745993958218545805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13824145163995972145697203 20736217745993958218545805)
                ·
                  refine ⟨7776081654747734331954677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20736217745993958218545805 7776081654747734331954677)
                  ·
                    refine ⟨729007655132600093620751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7776081654747734331954677 729007655132600093620751)
                    ·
                      rfl

theorem cell22_2129606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2129606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129606 prefixEnd_2129606 := by exact prefixLift 2129606
  have htrace : WordTrace (prefixWord ++ tailWord_2129606) baseStart_2129606 baseEnd_2129606 := by
    simpa [prefixWord, tailWord_2129606, baseEnd_2129606] using wordTrace_append hprefix tailTrace_2129606
  have hstable : (prefixWord ++ tailWord_2129606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129606).length < 2 ^ (prefixWord ++ tailWord_2129606).sum := by decide
  have hdescent : baseEnd_2129606 < baseStart_2129606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129615 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_2129615 : Nat := 118140960795 + 2129615 * 2 ^ 59
def prefixEnd_2129615 : Nat := 4983230072969 + 3 ^ 40 * 2129615 * 2
def baseEnd_2129615 : Nat := 729010736016527070145723

theorem tailTrace_2129615 : CollatzResearch.WordTrace tailWord_2129615 prefixEnd_2129615 729010736016527070145723 := by
  unfold tailWord_2129615
  simp only [CollatzResearch.WordTrace]
  refine ⟨77673440179776039130734299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51782293453184026087156199 77673440179776039130734299)
  ·
    refine ⟨116510160269664058696101449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77673440179776039130734299 116510160269664058696101449)
    ·
      refine ⟨87382620202248044022076087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116510160269664058696101449 87382620202248044022076087)
      ·
        refine ⟨131073930303372066033114131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87382620202248044022076087 131073930303372066033114131)
        ·
          refine ⟨196610895455058099049671197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131073930303372066033114131 196610895455058099049671197)
          ·
            refine ⟨73729085795646787143626699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196610895455058099049671197 73729085795646787143626699)
            ·
              refine ⟨110593628693470180715440049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73729085795646787143626699 110593628693470180715440049)
              ·
                refine ⟨82945221520102635536580037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110593628693470180715440049 82945221520102635536580037)
                ·
                  refine ⟨15552229035019244163108757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82945221520102635536580037 15552229035019244163108757)
                  ·
                    refine ⟨729010736016527070145723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15552229035019244163108757 729010736016527070145723)
                    ·
                      rfl

theorem cell22_2129615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_2129615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129615 prefixEnd_2129615 := by exact prefixLift 2129615
  have htrace : WordTrace (prefixWord ++ tailWord_2129615) baseStart_2129615 baseEnd_2129615 := by
    simpa [prefixWord, tailWord_2129615, baseEnd_2129615] using wordTrace_append hprefix tailTrace_2129615
  have hstable : (prefixWord ++ tailWord_2129615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129615).length < 2 ^ (prefixWord ++ tailWord_2129615).sum := by decide
  have hdescent : baseEnd_2129615 < baseStart_2129615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129647 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 5]
def baseStart_2129647 : Nat := 118140960795 + 2129647 * 2 ^ 59
def prefixEnd_2129647 : Nat := 4983230072969 + 3 ^ 40 * 2129647 * 2
def baseEnd_2129647 : Nat := 243007230090163217781875

theorem tailTrace_2129647 : CollatzResearch.WordTrace tailWord_2129647 prefixEnd_2129647 243007230090163217781875 := by
  unfold tailWord_2129647
  simp only [CollatzResearch.WordTrace]
  refine ⟨77674607315660108595899195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51783071543773405730599463 77674607315660108595899195)
  ·
    refine ⟨116511910973490162893848793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77674607315660108595899195 116511910973490162893848793)
    ·
      refine ⟨87383933230117622170386595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116511910973490162893848793 87383933230117622170386595)
      ·
        refine ⟨131075899845176433255579893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87383933230117622170386595 131075899845176433255579893)
        ·
          refine ⟨12288365610485290617710615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131075899845176433255579893 12288365610485290617710615)
          ·
            refine ⟨18432548415727935926565923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12288365610485290617710615 18432548415727935926565923)
            ·
              refine ⟨27648822623591903889848885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18432548415727935926565923 27648822623591903889848885)
              ·
                refine ⟨2592077120961740989673333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27648822623591903889848885 2592077120961740989673333)
                ·
                  refine ⟨243007230090163217781875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2592077120961740989673333 243007230090163217781875)
                  ·
                    rfl

theorem cell22_2129647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 5].length) (baseStart_2129647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129647 prefixEnd_2129647 := by exact prefixLift 2129647
  have htrace : WordTrace (prefixWord ++ tailWord_2129647) baseStart_2129647 baseEnd_2129647 := by
    simpa [prefixWord, tailWord_2129647, baseEnd_2129647] using wordTrace_append hprefix tailTrace_2129647
  have hstable : (prefixWord ++ tailWord_2129647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129647).length < 2 ^ (prefixWord ++ tailWord_2129647).sum := by decide
  have hdescent : baseEnd_2129647 < baseStart_2129647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129668 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2129668 : Nat := 118140960795 + 2129668 * 2 ^ 59
def prefixEnd_2129668 : Nat := 4983230072969 + 3 ^ 40 * 2129668 * 2
def baseEnd_2129668 : Nat := 729028878999652598570561

theorem tailTrace_2129668 : CollatzResearch.WordTrace tailWord_2129668 prefixEnd_2129668 729028878999652598570561 := by
  unfold tailWord_2129668
  simp only [CollatzResearch.WordTrace]
  refine ⟨38837686624292014591206829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51783582165722686121609105 38837686624292014591206829)
  ·
    refine ⟨14564132484109505471702561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38837686624292014591206829 14564132484109505471702561)
    ·
      refine ⟨10923099363082129103776921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14564132484109505471702561 10923099363082129103776921)
      ·
        refine ⟨8192324522311596827832691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10923099363082129103776921 8192324522311596827832691)
        ·
          refine ⟨12288486783467395241749037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8192324522311596827832691 12288486783467395241749037)
          ·
            refine ⟨4608182543800273215655889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12288486783467395241749037 4608182543800273215655889)
            ·
              refine ⟨3456136907850204911741917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4608182543800273215655889 3456136907850204911741917)
              ·
                refine ⟨1296051340443826841903219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3456136907850204911741917 1296051340443826841903219)
                ·
                  refine ⟨1944077010665740262854829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296051340443826841903219 1944077010665740262854829)
                  ·
                    refine ⟨729028878999652598570561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944077010665740262854829 729028878999652598570561)
                    ·
                      rfl

theorem cell22_2129668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2129668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129668 prefixEnd_2129668 := by exact prefixLift 2129668
  have htrace : WordTrace (prefixWord ++ tailWord_2129668) baseStart_2129668 baseEnd_2129668 := by
    simpa [prefixWord, tailWord_2129668, baseEnd_2129668] using wordTrace_append hprefix tailTrace_2129668
  have hstable : (prefixWord ++ tailWord_2129668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129668).length < 2 ^ (prefixWord ++ tailWord_2129668).sum := by decide
  have hdescent : baseEnd_2129668 < baseStart_2129668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129670 : List Nat := [6, 2, 2, 1, 1, 1, 9]
def baseStart_2129670 : Nat := 118140960795 + 2129670 * 2 ^ 59
def prefixEnd_2129670 : Nat := 4983230072969 + 3 ^ 40 * 2129670 * 2
def baseEnd_2129670 : Nat := 27001094949649083704465

theorem tailTrace_2129670 : CollatzResearch.WordTrace tailWord_2129670 prefixEnd_2129670 27001094949649083704465 := by
  unfold tailWord_2129670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427357693580524485124577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51783630796384522349324309 2427357693580524485124577)
  ·
    refine ⟨1820518270185393363843433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2427357693580524485124577 1820518270185393363843433)
    ·
      refine ⟨1365388702639045022882575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1820518270185393363843433 1365388702639045022882575)
      ·
        refine ⟨2048083053958567534323863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365388702639045022882575 2048083053958567534323863)
        ·
          refine ⟨3072124580937851301485795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048083053958567534323863 3072124580937851301485795)
          ·
            refine ⟨4608186871406776952228693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072124580937851301485795 4608186871406776952228693)
            ·
              refine ⟨27001094949649083704465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4608186871406776952228693 27001094949649083704465)
              ·
                rfl

theorem cell22_2129670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 9].length) (baseStart_2129670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129670 prefixEnd_2129670 := by exact prefixLift 2129670
  have htrace : WordTrace (prefixWord ++ tailWord_2129670) baseStart_2129670 baseEnd_2129670 := by
    simpa [prefixWord, tailWord_2129670, baseEnd_2129670] using wordTrace_append hprefix tailTrace_2129670
  have hstable : (prefixWord ++ tailWord_2129670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129670).length < 2 ^ (prefixWord ++ tailWord_2129670).sum := by decide
  have hdescent : baseEnd_2129670 < baseStart_2129670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129724 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_2129724 : Nat := 118140960795 + 2129724 * 2 ^ 59
def prefixEnd_2129724 : Nat := 4983230072969 + 3 ^ 40 * 2129724 * 2
def baseEnd_2129724 : Nat := 729048048944087119170389

theorem tailTrace_2129724 : CollatzResearch.WordTrace tailWord_2129724 prefixEnd_2129724 729048048944087119170389 := by
  unfold tailWord_2129724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38838707868190575373226113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51784943824254100497634817 38838707868190575373226113)
  ·
    refine ⟨29129030901142931529919585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38838707868190575373226113 29129030901142931529919585)
    ·
      refine ⟨21846773175857198647439689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29129030901142931529919585 21846773175857198647439689)
      ·
        refine ⟨16385079881892898985579767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21846773175857198647439689 16385079881892898985579767)
        ·
          refine ⟨24577619822839348478369651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16385079881892898985579767 24577619822839348478369651)
          ·
            refine ⟨36866429734259022717554477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24577619822839348478369651 36866429734259022717554477)
            ·
              refine ⟨13824911150347133519082929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36866429734259022717554477 13824911150347133519082929)
              ·
                refine ⟨10368683362760350139312197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13824911150347133519082929 10368683362760350139312197)
                ·
                  refine ⟨1944128130517565651121037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10368683362760350139312197 1944128130517565651121037)
                  ·
                    refine ⟨729048048944087119170389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944128130517565651121037 729048048944087119170389)
                    ·
                      rfl

theorem cell22_2129724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_2129724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129724 prefixEnd_2129724 := by exact prefixLift 2129724
  have htrace : WordTrace (prefixWord ++ tailWord_2129724) baseStart_2129724 baseEnd_2129724 := by
    simpa [prefixWord, tailWord_2129724, baseEnd_2129724] using wordTrace_append hprefix tailTrace_2129724
  have hstable : (prefixWord ++ tailWord_2129724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129724).length < 2 ^ (prefixWord ++ tailWord_2129724).sum := by decide
  have hdescent : baseEnd_2129724 < baseStart_2129724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129769 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_2129769 : Nat := 118140960795 + 2129769 * 2 ^ 59
def prefixEnd_2129769 : Nat := 4983230072969 + 3 ^ 40 * 2129769 * 2
def baseEnd_2129769 : Nat := 729063453363722001795251

theorem tailTrace_2129769 : CollatzResearch.WordTrace tailWord_2129769 prefixEnd_2129769 729063453363722001795251 := by
  unfold tailWord_2129769
  simp only [CollatzResearch.WordTrace]
  refine ⟨77679057021218123431840361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51786038014145415621226907 77679057021218123431840361)
  ·
    refine ⟨58259292765913592573880271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77679057021218123431840361 58259292765913592573880271)
    ·
      refine ⟨87388939148870388860820407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58259292765913592573880271 87388939148870388860820407)
      ·
        refine ⟨131083408723305583291230611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87388939148870388860820407 131083408723305583291230611)
        ·
          refine ⟨196625113084958374936845917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131083408723305583291230611 196625113084958374936845917)
          ·
            refine ⟨73734417406859390601317219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196625113084958374936845917 73734417406859390601317219)
            ·
              refine ⟨110601626110289085901975829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73734417406859390601317219 110601626110289085901975829)
              ·
                refine ⟨5184451223919800901655117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110601626110289085901975829 5184451223919800901655117)
                ·
                  refine ⟨1944169208969925338120669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5184451223919800901655117 1944169208969925338120669)
                  ·
                    refine ⟨729063453363722001795251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944169208969925338120669 729063453363722001795251)
                    ·
                      rfl

theorem cell22_2129769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_2129769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129769 prefixEnd_2129769 := by exact prefixLift 2129769
  have htrace : WordTrace (prefixWord ++ tailWord_2129769) baseStart_2129769 baseEnd_2129769 := by
    simpa [prefixWord, tailWord_2129769, baseEnd_2129769] using wordTrace_append hprefix tailTrace_2129769
  have hstable : (prefixWord ++ tailWord_2129769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129769).length < 2 ^ (prefixWord ++ tailWord_2129769).sum := by decide
  have hdescent : baseEnd_2129769 < baseStart_2129769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129895 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 4]
def baseStart_2129895 : Nat := 118140960795 + 2129895 * 2 ^ 59
def prefixEnd_2129895 : Nat := 4983230072969 + 3 ^ 40 * 2129895 * 2
def baseEnd_2129895 : Nat := 243035528579566557714955

theorem tailTrace_2129895 : CollatzResearch.WordTrace tailWord_2129895 prefixEnd_2129895 243035528579566557714955 := by
  unfold tailWord_2129895
  simp only [CollatzResearch.WordTrace]
  refine ⟨77683652618761646950927139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51789101745841097967284759 77683652618761646950927139)
  ·
    refine ⟨116525478928142470426390709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77683652618761646950927139 116525478928142470426390709)
    ·
      refine ⟨10924263649513356602474129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116525478928142470426390709 10924263649513356602474129)
      ·
        refine ⟨8193197737135017451855597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10924263649513356602474129 8193197737135017451855597)
        ·
          refine ⟨3072449151425631544445849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8193197737135017451855597 3072449151425631544445849)
          ·
            refine ⟨2304336863569223658334387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3072449151425631544445849 2304336863569223658334387)
            ·
              refine ⟨3456505295353835487501581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304336863569223658334387 3456505295353835487501581)
              ·
                refine ⟨1296189485757688307813093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3456505295353835487501581 1296189485757688307813093)
                ·
                  refine ⟨243035528579566557714955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296189485757688307813093 243035528579566557714955)
                  ·
                    rfl

theorem cell22_2129895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 4].length) (baseStart_2129895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129895 prefixEnd_2129895 := by exact prefixLift 2129895
  have htrace : WordTrace (prefixWord ++ tailWord_2129895) baseStart_2129895 baseEnd_2129895 := by
    simpa [prefixWord, tailWord_2129895, baseEnd_2129895] using wordTrace_append hprefix tailTrace_2129895
  have hstable : (prefixWord ++ tailWord_2129895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129895).length < 2 ^ (prefixWord ++ tailWord_2129895).sum := by decide
  have hdescent : baseEnd_2129895 < baseStart_2129895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129981 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_2129981 : Nat := 118140960795 + 2129981 * 2 ^ 59
def prefixEnd_2129981 : Nat := 4983230072969 + 3 ^ 40 * 2129981 * 2
def baseEnd_2129981 : Nat := 729136025296224115494601

theorem tailTrace_2129981 : CollatzResearch.WordTrace tailWord_2129981 prefixEnd_2129981 729136025296224115494601 := by
  unfold tailWord_2129981
  simp only [CollatzResearch.WordTrace]
  refine ⟨77686789296450083638557797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51791192864300055759038531 77686789296450083638557797)
  ·
    refine ⟨14566272993084390682229587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77686789296450083638557797 14566272993084390682229587)
    ·
      refine ⟨21849409489626586023344381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14566272993084390682229587 21849409489626586023344381)
      ·
        refine ⟨8193528558609969758754143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21849409489626586023344381 8193528558609969758754143)
        ·
          refine ⟨12290292837914954638131215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8193528558609969758754143 12290292837914954638131215)
          ·
            refine ⟨18435439256872431957196823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12290292837914954638131215 18435439256872431957196823)
            ·
              refine ⟨27653158885308647935795235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18435439256872431957196823 27653158885308647935795235)
              ·
                refine ⟨41479738327962971903692853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27653158885308647935795235 41479738327962971903692853)
                ·
                  refine ⟨3888725468246528615971205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41479738327962971903692853 3888725468246528615971205)
                  ·
                    refine ⟨729136025296224115494601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3888725468246528615971205 729136025296224115494601)
                    ·
                      rfl

theorem cell22_2129981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_2129981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2129981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2129981 prefixEnd_2129981 := by exact prefixLift 2129981
  have htrace : WordTrace (prefixWord ++ tailWord_2129981) baseStart_2129981 baseEnd_2129981 := by
    simpa [prefixWord, tailWord_2129981, baseEnd_2129981] using wordTrace_append hprefix tailTrace_2129981
  have hstable : (prefixWord ++ tailWord_2129981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129981).length < 2 ^ (prefixWord ++ tailWord_2129981).sum := by decide
  have hdescent : baseEnd_2129981 < baseStart_2129981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130028 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_2130028 : Nat := 118140960795 + 2130028 * 2 ^ 59
def prefixEnd_2130028 : Nat := 4983230072969 + 3 ^ 40 * 2130028 * 2
def baseEnd_2130028 : Nat := 729152114356731659569457

theorem tailTrace_2130028 : CollatzResearch.WordTrace tailWord_2130028 prefixEnd_2130028 729152114356731659569457 := by
  unfold tailWord_2130028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38844251763639905332759369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51792335684853207110345825 38844251763639905332759369)
  ·
    refine ⟨29133188822729928999569527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38844251763639905332759369 29133188822729928999569527)
    ·
      refine ⟨43699783234094893499354291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29133188822729928999569527 43699783234094893499354291)
      ·
        refine ⟨65549674851142340249031437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43699783234094893499354291 65549674851142340249031437)
        ·
          refine ⟨24581128069178377593386789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65549674851142340249031437 24581128069178377593386789)
          ·
            refine ⟨4608961512970945798760023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24581128069178377593386789 4608961512970945798760023)
            ·
              refine ⟨6913442269456418698140035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608961512970945798760023 6913442269456418698140035)
              ·
                refine ⟨10370163404184628047210053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6913442269456418698140035 10370163404184628047210053)
                ·
                  refine ⟨1944405638284617758851885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10370163404184628047210053 1944405638284617758851885)
                  ·
                    refine ⟨729152114356731659569457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944405638284617758851885 729152114356731659569457)
                    ·
                      rfl

theorem cell22_2130028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_2130028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130028 prefixEnd_2130028 := by exact prefixLift 2130028
  have htrace : WordTrace (prefixWord ++ tailWord_2130028) baseStart_2130028 baseEnd_2130028 := by
    simpa [prefixWord, tailWord_2130028, baseEnd_2130028] using wordTrace_append hprefix tailTrace_2130028
  have hstable : (prefixWord ++ tailWord_2130028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130028).length < 2 ^ (prefixWord ++ tailWord_2130028).sum := by decide
  have hdescent : baseEnd_2130028 < baseStart_2130028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130058 : List Nat := [3, 1, 2, 3, 1, 2, 4, 6]
def baseStart_2130058 : Nat := 118140960795 + 2130058 * 2 ^ 59
def prefixEnd_2130058 : Nat := 4983230072969 + 3 ^ 40 * 2130058 * 2
def baseEnd_2130058 : Nat := 81018042663313509035485

theorem tailTrace_2130058 : CollatzResearch.WordTrace tailWord_2130058 prefixEnd_2130058 81018042663313509035485 := by
  unfold tailWord_2130058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19422399429292781447277707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51793065144780750526073885 19422399429292781447277707)
  ·
    refine ⟨29133599143939172170916561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19422399429292781447277707 29133599143939172170916561)
    ·
      refine ⟨21850199357954379128187421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29133599143939172170916561 21850199357954379128187421)
      ·
        refine ⟨8193824759232892173070283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21850199357954379128187421 8193824759232892173070283)
        ·
          refine ⟨12290737138849338259605425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8193824759232892173070283 12290737138849338259605425)
          ·
            refine ⟨9218052854137003694704069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12290737138849338259605425 9218052854137003694704069)
            ·
              refine ⟨1728384910150688192757013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9218052854137003694704069 1728384910150688192757013)
              ·
                refine ⟨81018042663313509035485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1728384910150688192757013 81018042663313509035485)
                ·
                  rfl

theorem cell22_2130058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_2130058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130058 prefixEnd_2130058 := by exact prefixLift 2130058
  have htrace : WordTrace (prefixWord ++ tailWord_2130058) baseStart_2130058 baseEnd_2130058 := by
    simpa [prefixWord, tailWord_2130058, baseEnd_2130058] using wordTrace_append hprefix tailTrace_2130058
  have hstable : (prefixWord ++ tailWord_2130058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130058).length < 2 ^ (prefixWord ++ tailWord_2130058).sum := by decide
  have hdescent : baseEnd_2130058 < baseStart_2130058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130103 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 5]
def baseStart_2130103 : Nat := 118140960795 + 2130103 * 2 ^ 59
def prefixEnd_2130103 : Nat := 4983230072969 + 3 ^ 40 * 2130103 * 2
def baseEnd_2130103 : Nat := 243059262796485487981409

theorem tailTrace_2130103 : CollatzResearch.WordTrace tailWord_2130103 prefixEnd_2130103 243059262796485487981409 := by
  unfold tailWord_2130103
  simp only [CollatzResearch.WordTrace]
  refine ⟨77691239002008098474498963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51794159334672065649665975 77691239002008098474498963)
  ·
    refine ⟨116536858503012147711748445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77691239002008098474498963 116536858503012147711748445)
    ·
      refine ⟨43701321938629555391905667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116536858503012147711748445 43701321938629555391905667)
      ·
        refine ⟨65551982907944333087858501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43701321938629555391905667 65551982907944333087858501)
        ·
          refine ⟨12290996795239562453973469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65551982907944333087858501 12290996795239562453973469)
          ·
            refine ⟨4609123798214835920240051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12290996795239562453973469 4609123798214835920240051)
            ·
              refine ⟨6913685697322253880360077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609123798214835920240051 6913685697322253880360077)
              ·
                refine ⟨2592632136495845205135029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6913685697322253880360077 2592632136495845205135029)
                ·
                  refine ⟨243059262796485487981409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2592632136495845205135029 243059262796485487981409)
                  ·
                    rfl

theorem cell22_2130103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 5].length) (baseStart_2130103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130103 prefixEnd_2130103 := by exact prefixLift 2130103
  have htrace : WordTrace (prefixWord ++ tailWord_2130103) baseStart_2130103 baseEnd_2130103 := by
    simpa [prefixWord, tailWord_2130103, baseEnd_2130103] using wordTrace_append hprefix tailTrace_2130103
  have hstable : (prefixWord ++ tailWord_2130103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130103).length < 2 ^ (prefixWord ++ tailWord_2130103).sum := by decide
  have hdescent : baseEnd_2130103 < baseStart_2130103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130141 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2130141 : Nat := 118140960795 + 2130141 * 2 ^ 59
def prefixEnd_2130141 : Nat := 4983230072969 + 3 ^ 40 * 2130141 * 2
def baseEnd_2130141 : Nat := 729190796566037031494111

theorem tailTrace_2130141 : CollatzResearch.WordTrace tailWord_2130141 prefixEnd_2130141 729190796566037031494111 := by
  unfold tailWord_2130141
  simp only [CollatzResearch.WordTrace]
  refine ⟨77692624975870430964382277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51795083317246953976254851 77692624975870430964382277)
  ·
    refine ⟨14567367182975705805821677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77692624975870430964382277 14567367182975705805821677)
    ·
      refine ⟨5462762693615889677183129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14567367182975705805821677 5462762693615889677183129)
      ·
        refine ⟨4097072020211917257887347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5462762693615889677183129 4097072020211917257887347)
        ·
          refine ⟨6145608030317875886831021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4097072020211917257887347 6145608030317875886831021)
          ·
            refine ⟨2304603011369203457561633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6145608030317875886831021 2304603011369203457561633)
            ·
              refine ⟨1728452258526902593171225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2304603011369203457561633 1728452258526902593171225)
              ·
                refine ⟨1296339193895176944878419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1728452258526902593171225 1296339193895176944878419)
                ·
                  refine ⟨1944508790842765417317629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296339193895176944878419 1944508790842765417317629)
                  ·
                    refine ⟨729190796566037031494111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944508790842765417317629 729190796566037031494111)
                    ·
                      rfl

theorem cell22_2130141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2130141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130141 prefixEnd_2130141 := by exact prefixLift 2130141
  have htrace : WordTrace (prefixWord ++ tailWord_2130141) baseStart_2130141 baseEnd_2130141 := by
    simpa [prefixWord, tailWord_2130141, baseEnd_2130141] using wordTrace_append hprefix tailTrace_2130141
  have hstable : (prefixWord ++ tailWord_2130141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130141).length < 2 ^ (prefixWord ++ tailWord_2130141).sum := by decide
  have hdescent : baseEnd_2130141 < baseStart_2130141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130163 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 1, 5]
def baseStart_2130163 : Nat := 118140960795 + 2130163 * 2 ^ 59
def prefixEnd_2130163 : Nat := 4983230072969 + 3 ^ 40 * 2130163 * 2
def baseEnd_2130163 : Nat := 729198327615636307444043

theorem tailTrace_2130163 : CollatzResearch.WordTrace tailWord_2130163 prefixEnd_2130163 729198327615636307444043 := by
  unfold tailWord_2130163
  simp only [CollatzResearch.WordTrace]
  refine ⟨77693427381790728721683143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51795618254527152481122095 77693427381790728721683143)
  ·
    refine ⟨116540141072686093082524715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77693427381790728721683143 116540141072686093082524715)
    ·
      refine ⟨174810211609029139623787073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116540141072686093082524715 174810211609029139623787073)
      ·
        refine ⟨131107658706771854717840305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174810211609029139623787073 131107658706771854717840305)
        ·
          refine ⟨98330744030078891038380229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131107658706771854717840305 98330744030078891038380229)
          ·
            refine ⟨18437014505639792069696293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98330744030078891038380229 18437014505639792069696293)
            ·
              refine ⟨3456940219807461013068055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18437014505639792069696293 3456940219807461013068055)
              ·
                refine ⟨5185410329711191519602083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456940219807461013068055 5185410329711191519602083)
                ·
                  refine ⟨7778115494566787279403125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185410329711191519602083 7778115494566787279403125)
                  ·
                    refine ⟨729198327615636307444043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7778115494566787279403125 729198327615636307444043)
                    ·
                      rfl

theorem cell22_2130163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].length) (baseStart_2130163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130163 prefixEnd_2130163 := by exact prefixLift 2130163
  have htrace : WordTrace (prefixWord ++ tailWord_2130163) baseStart_2130163 baseEnd_2130163 := by
    simpa [prefixWord, tailWord_2130163, baseEnd_2130163] using wordTrace_append hprefix tailTrace_2130163
  have hstable : (prefixWord ++ tailWord_2130163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130163).length < 2 ^ (prefixWord ++ tailWord_2130163).sum := by decide
  have hdescent : baseEnd_2130163 < baseStart_2130163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130176 : List Nat := [2, 1, 1, 2, 1, 1, 4, 10]
def baseStart_2130176 : Nat := 118140960795 + 2130176 * 2 ^ 59
def prefixEnd_2130176 : Nat := 4983230072969 + 3 ^ 40 * 2130176 * 2
def baseEnd_2130176 : Nat := 81022530864589845207667

theorem tailTrace_2130176 : CollatzResearch.WordTrace tailWord_2130176 prefixEnd_2130176 81022530864589845207667 := by
  unfold tailWord_2130176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38846950765371815970953191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51795934353829087961270921 38846950765371815970953191)
  ·
    refine ⟨58270426148057723956429787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38846950765371815970953191 58270426148057723956429787)
    ·
      refine ⟨87405639222086585934644681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58270426148057723956429787 87405639222086585934644681)
      ·
        refine ⟨65554229416564939450983511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87405639222086585934644681 65554229416564939450983511)
        ·
          refine ⟨98331344124847409176475267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65554229416564939450983511 98331344124847409176475267)
          ·
            refine ⟨147497016187271113764712901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98331344124847409176475267 147497016187271113764712901)
            ·
              refine ⟨27655690535113333830883669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147497016187271113764712901 27655690535113333830883669)
              ·
                refine ⟨81022530864589845207667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27655690535113333830883669 81022530864589845207667)
                ·
                  rfl

theorem cell22_2130176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_2130176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130176 prefixEnd_2130176 := by exact prefixLift 2130176
  have htrace : WordTrace (prefixWord ++ tailWord_2130176) baseStart_2130176 baseEnd_2130176 := by
    simpa [prefixWord, tailWord_2130176, baseEnd_2130176] using wordTrace_append hprefix tailTrace_2130176
  have hstable : (prefixWord ++ tailWord_2130176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130176).length < 2 ^ (prefixWord ++ tailWord_2130176).sum := by decide
  have hdescent : baseEnd_2130176 < baseStart_2130176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130191 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_2130191 : Nat := 118140960795 + 2130191 * 2 ^ 59
def prefixEnd_2130191 : Nat := 4983230072969 + 3 ^ 40 * 2130191 * 2
def baseEnd_2130191 : Nat := 729207912587853567743957

theorem tailTrace_2130191 : CollatzResearch.WordTrace tailWord_2130191 prefixEnd_2130191 729207912587853567743957 := by
  unfold tailWord_2130191
  simp only [CollatzResearch.WordTrace]
  refine ⟨77694448625689289503702427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51796299083792859669134951 77694448625689289503702427)
  ·
    refine ⟨116541672938533934255553641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77694448625689289503702427 116541672938533934255553641)
    ·
      refine ⟨87406254703900450691665231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116541672938533934255553641 87406254703900450691665231)
      ·
        refine ⟨131109382055850676037497847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87406254703900450691665231 131109382055850676037497847)
        ·
          refine ⟨196664073083776014056246771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131109382055850676037497847 196664073083776014056246771)
          ·
            refine ⟨294996109625664021084370157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196664073083776014056246771 294996109625664021084370157)
            ·
              refine ⟨110623541109624007906638809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 294996109625664021084370157 110623541109624007906638809)
              ·
                refine ⟨82967655832218005929979107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110623541109624007906638809 82967655832218005929979107)
                ·
                  refine ⟨124451483748327008894968661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82967655832218005929979107 124451483748327008894968661)
                  ·
                    refine ⟨729207912587853567743957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 124451483748327008894968661 729207912587853567743957)
                    ·
                      rfl

theorem cell22_2130191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_2130191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130191 prefixEnd_2130191 := by exact prefixLift 2130191
  have htrace : WordTrace (prefixWord ++ tailWord_2130191) baseStart_2130191 baseEnd_2130191 := by
    simpa [prefixWord, tailWord_2130191, baseEnd_2130191] using wordTrace_append hprefix tailTrace_2130191
  have hstable : (prefixWord ++ tailWord_2130191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130191).length < 2 ^ (prefixWord ++ tailWord_2130191).sum := by decide
  have hdescent : baseEnd_2130191 < baseStart_2130191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130285 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2130285 : Nat := 118140960795 + 2130285 * 2 ^ 59
def prefixEnd_2130285 : Nat := 4983230072969 + 3 ^ 40 * 2130285 * 2
def baseEnd_2130285 : Nat := 729240090708868655893669

theorem tailTrace_2130285 : CollatzResearch.WordTrace tailWord_2130285 prefixEnd_2130285 729240090708868655893669 := by
  unfold tailWord_2130285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77697877087348743557624309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51798584724899162371749539 77697877087348743557624309)
  ·
    refine ⟨7284175976938944708527279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77697877087348743557624309 7284175976938944708527279)
    ·
      refine ⟨10926263965408417062790919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7284175976938944708527279 10926263965408417062790919)
      ·
        refine ⟨16389395948112625594186379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10926263965408417062790919 16389395948112625594186379)
        ·
          refine ⟨24584093922168938391279569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16389395948112625594186379 24584093922168938391279569)
          ·
            refine ⟨18438070441626703793459677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24584093922168938391279569 18438070441626703793459677)
            ·
              refine ⟨6914276415610013922547379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18438070441626703793459677 6914276415610013922547379)
              ·
                refine ⟨10371414623415020883821069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6914276415610013922547379 10371414623415020883821069)
                ·
                  refine ⟨3889280483780632831432901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10371414623415020883821069 3889280483780632831432901)
                  ·
                    refine ⟨729240090708868655893669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889280483780632831432901 729240090708868655893669)
                    ·
                      rfl

theorem cell22_2130285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2130285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130285 prefixEnd_2130285 := by exact prefixLift 2130285
  have htrace : WordTrace (prefixWord ++ tailWord_2130285) baseStart_2130285 baseEnd_2130285 := by
    simpa [prefixWord, tailWord_2130285, baseEnd_2130285] using wordTrace_append hprefix tailTrace_2130285
  have hstable : (prefixWord ++ tailWord_2130285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130285).length < 2 ^ (prefixWord ++ tailWord_2130285).sum := by decide
  have hdescent : baseEnd_2130285 < baseStart_2130285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130360 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_2130360 : Nat := 118140960795 + 2130360 * 2 ^ 59
def prefixEnd_2130360 : Nat := 4983230072969 + 3 ^ 40 * 2130360 * 2
def baseEnd_2130360 : Nat := 729265764741593460268439

theorem tailTrace_2130360 : CollatzResearch.WordTrace tailWord_2130360 prefixEnd_2130360 729265764741593460268439 := by
  unfold tailWord_2130360
  simp only [CollatzResearch.WordTrace]
  refine ⟨38850306281038515683302267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51800408374718020911069689 38850306281038515683302267)
  ·
    refine ⟨58275459421557773524953401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38850306281038515683302267 58275459421557773524953401)
    ·
      refine ⟨43706594566168330143715051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58275459421557773524953401 43706594566168330143715051)
      ·
        refine ⟨65559891849252495215572577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43706594566168330143715051 65559891849252495215572577)
        ·
          refine ⟨49169918886939371411679433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65559891849252495215572577 49169918886939371411679433)
          ·
            refine ⟨36877439165204528558759575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49169918886939371411679433 36877439165204528558759575)
            ·
              refine ⟨55316158747806792838139363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36877439165204528558759575 55316158747806792838139363)
              ·
                refine ⟨82974238121710189257209045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55316158747806792838139363 82974238121710189257209045)
                ·
                  refine ⟨1944708705977582560715837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82974238121710189257209045 1944708705977582560715837)
                  ·
                    refine ⟨729265764741593460268439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944708705977582560715837 729265764741593460268439)
                    ·
                      rfl

theorem cell22_2130360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_2130360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130360 prefixEnd_2130360 := by exact prefixLift 2130360
  have htrace : WordTrace (prefixWord ++ tailWord_2130360) baseStart_2130360 baseEnd_2130360 := by
    simpa [prefixWord, tailWord_2130360, baseEnd_2130360] using wordTrace_append hprefix tailTrace_2130360
  have hstable : (prefixWord ++ tailWord_2130360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130360).length < 2 ^ (prefixWord ++ tailWord_2130360).sum := by decide
  have hdescent : baseEnd_2130360 < baseStart_2130360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130467 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 1, 5]
def baseStart_2130467 : Nat := 118140960795 + 2130467 * 2 ^ 59
def prefixEnd_2130467 : Nat := 4983230072969 + 3 ^ 40 * 2130467 * 2
def baseEnd_2130467 : Nat := 729302393028280847843111

theorem tailTrace_2130467 : CollatzResearch.WordTrace tailWord_2130467 prefixEnd_2130467 729302393028280847843111 := by
  unfold tailWord_2130467
  simp only [CollatzResearch.WordTrace]
  refine ⟨77704515172689388640749655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51803010115126259093833103 77704515172689388640749655)
  ·
    refine ⟨116556772759034082961124483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77704515172689388640749655 116556772759034082961124483)
    ·
      refine ⟨174835159138551124441686725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116556772759034082961124483 174835159138551124441686725)
      ·
        refine ⟨32781592338478335832816261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174835159138551124441686725 32781592338478335832816261)
        ·
          refine ⟨6146548563464687968653049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32781592338478335832816261 6146548563464687968653049)
          ·
            refine ⟨4609911422598515976489787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6146548563464687968653049 4609911422598515976489787)
            ·
              refine ⟨6914867133897773964734681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609911422598515976489787 6914867133897773964734681)
              ·
                refine ⟨5186150350423330473551011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914867133897773964734681 5186150350423330473551011)
                ·
                  refine ⟨7779225525634995710326517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186150350423330473551011 7779225525634995710326517)
                  ·
                    refine ⟨729302393028280847843111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7779225525634995710326517 729302393028280847843111)
                    ·
                      rfl

theorem cell22_2130467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_2130467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130467 prefixEnd_2130467 := by exact prefixLift 2130467
  have htrace : WordTrace (prefixWord ++ tailWord_2130467) baseStart_2130467 baseEnd_2130467 := by
    simpa [prefixWord, tailWord_2130467, baseEnd_2130467] using wordTrace_append hprefix tailTrace_2130467
  have hstable : (prefixWord ++ tailWord_2130467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130467).length < 2 ^ (prefixWord ++ tailWord_2130467).sum := by decide
  have hdescent : baseEnd_2130467 < baseStart_2130467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130482 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_2130482 : Nat := 118140960795 + 2130482 * 2 ^ 59
def prefixEnd_2130482 : Nat := 4983230072969 + 3 ^ 40 * 2130482 * 2
def baseEnd_2130482 : Nat := 729307527834825808718065

theorem tailTrace_2130482 : CollatzResearch.WordTrace tailWord_2130482 prefixEnd_2130482 729307527834825808718065 := by
  unfold tailWord_2130482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19426265566908761550636425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51803374845090030801697133 19426265566908761550636425)
  ·
    refine ⟨14569699175181571162977319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19426265566908761550636425 14569699175181571162977319)
    ·
      refine ⟨21854548762772356744465979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14569699175181571162977319 21854548762772356744465979)
      ·
        refine ⟨32781823144158535116698969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21854548762772356744465979 32781823144158535116698969)
        ·
          refine ⟨24586367358118901337524227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32781823144158535116698969 24586367358118901337524227)
          ·
            refine ⟨36879551037178352006286341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24586367358118901337524227 36879551037178352006286341)
            ·
              refine ⟨6914915819470941001178689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36879551037178352006286341 6914915819470941001178689)
              ·
                refine ⟨5186186864603205750884017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914915819470941001178689 5186186864603205750884017)
                ·
                  refine ⟨3889640148452404313163013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5186186864603205750884017 3889640148452404313163013)
                  ·
                    refine ⟨729307527834825808718065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889640148452404313163013 729307527834825808718065)
                    ·
                      rfl

theorem cell22_2130482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_2130482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130482 prefixEnd_2130482 := by exact prefixLift 2130482
  have htrace : WordTrace (prefixWord ++ tailWord_2130482) baseStart_2130482 baseEnd_2130482 := by
    simpa [prefixWord, tailWord_2130482, baseEnd_2130482] using wordTrace_append hprefix tailTrace_2130482
  have hstable : (prefixWord ++ tailWord_2130482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130482).length < 2 ^ (prefixWord ++ tailWord_2130482).sum := by decide
  have hdescent : baseEnd_2130482 < baseStart_2130482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130486 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2130486 : Nat := 118140960795 + 2130486 * 2 ^ 59
def prefixEnd_2130486 : Nat := 4983230072969 + 3 ^ 40 * 2130486 * 2
def baseEnd_2130486 : Nat := 243102965705523710539351

theorem tailTrace_2130486 : CollatzResearch.WordTrace tailWord_2130486 prefixEnd_2130486 243102965705523710539351 := by
  unfold tailWord_2130486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856575509976284680355707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51803472106413703257127541 4856575509976284680355707)
  ·
    refine ⟨7284863264964427020533561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4856575509976284680355707 7284863264964427020533561)
    ·
      refine ⟨5463647448723320265400171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7284863264964427020533561 5463647448723320265400171)
      ·
        refine ⟨8195471173084980398100257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5463647448723320265400171 8195471173084980398100257)
        ·
          refine ⟨6146603379813735298575193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8195471173084980398100257 6146603379813735298575193)
          ·
            refine ⟨4609952534860301473931395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6146603379813735298575193 4609952534860301473931395)
            ·
              refine ⟨6914928802290452210897093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609952534860301473931395 6914928802290452210897093)
              ·
                refine ⟨1296549150429459789543205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6914928802290452210897093 1296549150429459789543205)
                ·
                  refine ⟨243102965705523710539351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296549150429459789543205 243102965705523710539351)
                  ·
                    rfl

theorem cell22_2130486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2130486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130486 prefixEnd_2130486 := by exact prefixLift 2130486
  have htrace : WordTrace (prefixWord ++ tailWord_2130486) baseStart_2130486 baseEnd_2130486 := by
    simpa [prefixWord, tailWord_2130486, baseEnd_2130486] using wordTrace_append hprefix tailTrace_2130486
  have hstable : (prefixWord ++ tailWord_2130486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130486).length < 2 ^ (prefixWord ++ tailWord_2130486).sum := by decide
  have hdescent : baseEnd_2130486 < baseStart_2130486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130497 : List Nat := [1, 2, 5, 1, 1, 2, 3, 7]
def baseStart_2130497 : Nat := 118140960795 + 2130497 * 2 ^ 59
def prefixEnd_2130497 : Nat := 4983230072969 + 3 ^ 40 * 2130497 * 2
def baseEnd_2130497 : Nat := 81034740293485641065891

theorem tailTrace_2130497 : CollatzResearch.WordTrace tailWord_2130497 prefixEnd_2130497 81034740293485641065891 := by
  unfold tailWord_2130497
  simp only [CollatzResearch.WordTrace]
  refine ⟨77705609362580703764341745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51803739575053802509561163 77705609362580703764341745)
  ·
    refine ⟨58279207021935527823256309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77705609362580703764341745 58279207021935527823256309)
    ·
      refine ⟨5463675658306455733430279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58279207021935527823256309 5463675658306455733430279)
      ·
        refine ⟨8195513487459683600145419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5463675658306455733430279 8195513487459683600145419)
        ·
          refine ⟨12293270231189525400218129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8195513487459683600145419 12293270231189525400218129)
          ·
            refine ⟨9219952673392144050163597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12293270231189525400218129 9219952673392144050163597)
            ·
              refine ⟨3457482252522054018811349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9219952673392144050163597 3457482252522054018811349)
              ·
                refine ⟨81034740293485641065891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3457482252522054018811349 81034740293485641065891)
                ·
                  rfl

theorem cell22_2130497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 7].length) (baseStart_2130497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130497 prefixEnd_2130497 := by exact prefixLift 2130497
  have htrace : WordTrace (prefixWord ++ tailWord_2130497) baseStart_2130497 baseEnd_2130497 := by
    simpa [prefixWord, tailWord_2130497, baseEnd_2130497] using wordTrace_append hprefix tailTrace_2130497
  have hstable : (prefixWord ++ tailWord_2130497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130497).length < 2 ^ (prefixWord ++ tailWord_2130497).sum := by decide
  have hdescent : baseEnd_2130497 < baseStart_2130497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130546 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_2130546 : Nat := 118140960795 + 2130546 * 2 ^ 59
def prefixEnd_2130546 : Nat := 4983230072969 + 3 ^ 40 * 2130546 * 2
def baseEnd_2130546 : Nat := 729329436342750975117869

theorem tailTrace_2130546 : CollatzResearch.WordTrace tailWord_2130546 prefixEnd_2130546 729329436342750975117869 := by
  unfold tailWord_2130546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19426849134850796283218873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51804931026268790088583661 19426849134850796283218873)
  ·
    refine ⟨14570136851138097212414155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19426849134850796283218873 14570136851138097212414155)
    ·
      refine ⟨21855205276707145818621233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14570136851138097212414155 21855205276707145818621233)
      ·
        refine ⟨16391403957530359363965925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21855205276707145818621233 16391403957530359363965925)
        ·
          refine ⟨3073388242036942380743611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16391403957530359363965925 3073388242036942380743611)
          ·
            refine ⟨4610082363055413571115417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073388242036942380743611 4610082363055413571115417)
            ·
              refine ⟨3457561772291560178336563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610082363055413571115417 3457561772291560178336563)
              ·
                refine ⟨5186342658437340267504845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457561772291560178336563 5186342658437340267504845)
                ·
                  refine ⟨1944878496914002600314317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5186342658437340267504845 1944878496914002600314317)
                  ·
                    refine ⟨729329436342750975117869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944878496914002600314317 729329436342750975117869)
                    ·
                      rfl

theorem cell22_2130546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_2130546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130546 prefixEnd_2130546 := by exact prefixLift 2130546
  have htrace : WordTrace (prefixWord ++ tailWord_2130546) baseStart_2130546 baseEnd_2130546 := by
    simpa [prefixWord, tailWord_2130546, baseEnd_2130546] using wordTrace_append hprefix tailTrace_2130546
  have hstable : (prefixWord ++ tailWord_2130546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130546).length < 2 ^ (prefixWord ++ tailWord_2130546).sum := by decide
  have hdescent : baseEnd_2130546 < baseStart_2130546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130555 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_2130555 : Nat := 118140960795 + 2130555 * 2 ^ 59
def prefixEnd_2130555 : Nat := 4983230072969 + 3 ^ 40 * 2130555 * 2
def baseEnd_2130555 : Nat := 729332517226677951642841

theorem tailTrace_2130555 : CollatzResearch.WordTrace tailWord_2130555 prefixEnd_2130555 729332517226677951642841 := by
  unfold tailWord_2130555
  simp only [CollatzResearch.WordTrace]
  refine ⟨77707724796370579669953119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51805149864247053113302079 77707724796370579669953119)
  ·
    refine ⟨116561587194555869504929679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77707724796370579669953119 116561587194555869504929679)
    ·
      refine ⟨174842380791833804257394519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116561587194555869504929679 174842380791833804257394519)
      ·
        refine ⟨262263571187750706386091779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174842380791833804257394519 262263571187750706386091779)
        ·
          refine ⟨393395356781626059579137669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262263571187750706386091779 393395356781626059579137669)
          ·
            refine ⟨73761629396554886171088313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393395356781626059579137669 73761629396554886171088313)
            ·
              refine ⟨55321222047416164628316235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73761629396554886171088313 55321222047416164628316235)
              ·
                refine ⟨82981833071124246942474353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55321222047416164628316235 82981833071124246942474353)
                ·
                  refine ⟨62236374803343185206855765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82981833071124246942474353 62236374803343185206855765)
                  ·
                    refine ⟨729332517226677951642841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62236374803343185206855765 729332517226677951642841)
                    ·
                      rfl

theorem cell22_2130555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_2130555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130555 prefixEnd_2130555 := by exact prefixLift 2130555
  have htrace : WordTrace (prefixWord ++ tailWord_2130555) baseStart_2130555 baseEnd_2130555 := by
    simpa [prefixWord, tailWord_2130555, baseEnd_2130555] using wordTrace_append hprefix tailTrace_2130555
  have hstable : (prefixWord ++ tailWord_2130555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130555).length < 2 ^ (prefixWord ++ tailWord_2130555).sum := by decide
  have hdescent : baseEnd_2130555 < baseStart_2130555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130580 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2130580 : Nat := 118140960795 + 2130580 * 2 ^ 59
def prefixEnd_2130580 : Nat := 4983230072969 + 3 ^ 40 * 2130580 * 2
def baseEnd_2130580 : Nat := 729341075237586219767765

theorem tailTrace_2130580 : CollatzResearch.WordTrace tailWord_2130580 prefixEnd_2130580 729341075237586219767765 := by
  unfold tailWord_2130580
  simp only [CollatzResearch.WordTrace]
  refine ⟨38854318310640004469806597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51805757747520005959742129 38854318310640004469806597)
  ·
    refine ⟨7285184683245000838088737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38854318310640004469806597 7285184683245000838088737)
    ·
      refine ⟨5463888512433750628566553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7285184683245000838088737 5463888512433750628566553)
      ·
        refine ⟨4097916384325312971424915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5463888512433750628566553 4097916384325312971424915)
        ·
          refine ⟨6146874576487969457137373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4097916384325312971424915 6146874576487969457137373)
          ·
            refine ⟨2305077966182988546426515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6146874576487969457137373 2305077966182988546426515)
            ·
              refine ⟨3457616949274482819639773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305077966182988546426515 3457616949274482819639773)
              ·
                refine ⟨1296606355977931057364915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3457616949274482819639773 1296606355977931057364915)
                ·
                  refine ⟨1944909533966896586047373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296606355977931057364915 1944909533966896586047373)
                  ·
                    refine ⟨729341075237586219767765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1944909533966896586047373 729341075237586219767765)
                    ·
                      rfl

theorem cell22_2130580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2130580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130580 prefixEnd_2130580 := by exact prefixLift 2130580
  have htrace : WordTrace (prefixWord ++ tailWord_2130580) baseStart_2130580 baseEnd_2130580 := by
    simpa [prefixWord, tailWord_2130580, baseEnd_2130580] using wordTrace_append hprefix tailTrace_2130580
  have hstable : (prefixWord ++ tailWord_2130580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130580).length < 2 ^ (prefixWord ++ tailWord_2130580).sum := by decide
  have hdescent : baseEnd_2130580 < baseStart_2130580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130589 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_2130589 : Nat := 118140960795 + 2130589 * 2 ^ 59
def prefixEnd_2130589 : Nat := 4983230072969 + 3 ^ 40 * 2130589 * 2
def baseEnd_2130589 : Nat := 729344156121513196292737

theorem tailTrace_2130589 : CollatzResearch.WordTrace tailWord_2130589 prefixEnd_2130589 729344156121513196292737 := by
  unfold tailWord_2130589
  simp only [CollatzResearch.WordTrace]
  refine ⟨77708964878247403476690821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51805976585498268984460547 77708964878247403476690821)
  ·
    refine ⟨14570430914671388151879529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77708964878247403476690821 14570430914671388151879529)
    ·
      refine ⟨10927823186003541113909647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14570430914671388151879529 10927823186003541113909647)
      ·
        refine ⟨16391734779005311670864471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10927823186003541113909647 16391734779005311670864471)
        ·
          refine ⟨24587602168507967506296707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16391734779005311670864471 24587602168507967506296707)
          ·
            refine ⟨36881403252761951259445061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24587602168507967506296707 36881403252761951259445061)
            ·
              refine ⟨6915263109892865861145949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36881403252761951259445061 6915263109892865861145949)
              ·
                refine ⟨2593223666209824697929731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6915263109892865861145949 2593223666209824697929731)
                ·
                  refine ⟨3889835499314737046894597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593223666209824697929731 3889835499314737046894597)
                  ·
                    refine ⟨729344156121513196292737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889835499314737046894597 729344156121513196292737)
                    ·
                      rfl

theorem cell22_2130589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_2130589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130589 prefixEnd_2130589 := by exact prefixLift 2130589
  have htrace : WordTrace (prefixWord ++ tailWord_2130589) baseStart_2130589 baseEnd_2130589 := by
    simpa [prefixWord, tailWord_2130589, baseEnd_2130589] using wordTrace_append hprefix tailTrace_2130589
  have hstable : (prefixWord ++ tailWord_2130589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130589).length < 2 ^ (prefixWord ++ tailWord_2130589).sum := by decide
  have hdescent : baseEnd_2130589 < baseStart_2130589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130617 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_2130617 : Nat := 118140960795 + 2130617 * 2 ^ 59
def prefixEnd_2130617 : Nat := 4983230072969 + 3 ^ 40 * 2130617 * 2
def baseEnd_2130617 : Nat := 729353741093730456592651

theorem tailTrace_2130617 : CollatzResearch.WordTrace tailWord_2130617 prefixEnd_2130617 729353741093730456592651 := by
  unfold tailWord_2130617
  simp only [CollatzResearch.WordTrace]
  refine ⟨77709986122145964258710105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51806657414763976172473403 77709986122145964258710105)
  ·
    refine ⟨58282489591609473194032579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77709986122145964258710105 58282489591609473194032579)
    ·
      refine ⟨87423734387414209791048869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58282489591609473194032579 87423734387414209791048869)
      ·
        refine ⟨16391950197640164335821663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87423734387414209791048869 16391950197640164335821663)
        ·
          refine ⟨24587925296460246503732495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16391950197640164335821663 24587925296460246503732495)
          ·
            refine ⟨36881887944690369755598743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24587925296460246503732495 36881887944690369755598743)
            ·
              refine ⟨55322831917035554633398115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36881887944690369755598743 55322831917035554633398115)
              ·
                refine ⟨82984247875553331950097173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55322831917035554633398115 82984247875553331950097173)
                ·
                  refine ⟨3889886619166562435160805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82984247875553331950097173 3889886619166562435160805)
                  ·
                    refine ⟨729353741093730456592651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889886619166562435160805 729353741093730456592651)
                    ·
                      rfl

theorem cell22_2130617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_2130617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130617 prefixEnd_2130617 := by exact prefixLift 2130617
  have htrace : WordTrace (prefixWord ++ tailWord_2130617) baseStart_2130617 baseEnd_2130617 := by
    simpa [prefixWord, tailWord_2130617, baseEnd_2130617] using wordTrace_append hprefix tailTrace_2130617
  have hstable : (prefixWord ++ tailWord_2130617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130617).length < 2 ^ (prefixWord ++ tailWord_2130617).sum := by decide
  have hdescent : baseEnd_2130617 < baseStart_2130617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130632 : List Nat := [2, 1, 3, 1, 2, 3, 2, 8]
def baseStart_2130632 : Nat := 118140960795 + 2130632 * 2 ^ 59
def prefixEnd_2130632 : Nat := 4983230072969 + 3 ^ 40 * 2130632 * 2
def baseEnd_2130632 : Nat := 81039875100030601940845

theorem tailTrace_2130632 : CollatzResearch.WordTrace tailWord_2130632 prefixEnd_2130632 81039875100030601940845 := by
  unfold tailWord_2130632
  simp only [CollatzResearch.WordTrace]
  refine ⟨38855266608545810910253075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51807022144727747880337433 38855266608545810910253075)
  ·
    refine ⟨58282899912818716365379613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38855266608545810910253075 58282899912818716365379613)
    ·
      refine ⟨21856087467307018637017355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58282899912818716365379613 21856087467307018637017355)
      ·
        refine ⟨32784131200960527955526033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21856087467307018637017355 32784131200960527955526033)
        ·
          refine ⟨24588098400720395966644525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32784131200960527955526033 24588098400720395966644525)
          ·
            refine ⟨9220536900270148487491697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24588098400720395966644525 9220536900270148487491697)
            ·
              refine ⟨6915402675202611365618773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9220536900270148487491697 6915402675202611365618773)
              ·
                refine ⟨81039875100030601940845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6915402675202611365618773 81039875100030601940845)
                ·
                  rfl

theorem cell22_2130632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_2130632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130632 prefixEnd_2130632 := by exact prefixLift 2130632
  have htrace : WordTrace (prefixWord ++ tailWord_2130632) baseStart_2130632 baseEnd_2130632 := by
    simpa [prefixWord, tailWord_2130632, baseEnd_2130632] using wordTrace_append hprefix tailTrace_2130632
  have hstable : (prefixWord ++ tailWord_2130632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130632).length < 2 ^ (prefixWord ++ tailWord_2130632).sum := by decide
  have hdescent : baseEnd_2130632 < baseStart_2130632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130634 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2130634 : Nat := 118140960795 + 2130634 * 2 ^ 59
def prefixEnd_2130634 : Nat := 4983230072969 + 3 ^ 40 * 2130634 * 2
def baseEnd_2130634 : Nat := 729359560541148078917599

theorem tailTrace_2130634 : CollatzResearch.WordTrace tailWord_2130634 prefixEnd_2130634 729359560541148078917599 := by
  unfold tailWord_2130634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19427651540771094040519739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51807070775389584108052637 19427651540771094040519739)
  ·
    refine ⟨29141477311156641060779609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19427651540771094040519739 29141477311156641060779609)
    ·
      refine ⟨21856107983367480795584707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29141477311156641060779609 21856107983367480795584707)
      ·
        refine ⟨32784161975051221193377061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21856107983367480795584707 32784161975051221193377061)
        ·
          refine ⟨6147030370322103973758199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32784161975051221193377061 6147030370322103973758199)
          ·
            refine ⟨9220545555483155960637299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147030370322103973758199 9220545555483155960637299)
            ·
              refine ⟨13830818333224733940955949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9220545555483155960637299 13830818333224733940955949)
              ·
                refine ⟨5186556874959275227858481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13830818333224733940955949 5186556874959275227858481)
                ·
                  refine ⟨3889917656219456420893861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5186556874959275227858481 3889917656219456420893861)
                  ·
                    refine ⟨729359560541148078917599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889917656219456420893861 729359560541148078917599)
                    ·
                      rfl

theorem cell22_2130634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2130634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130634 prefixEnd_2130634 := by exact prefixLift 2130634
  have htrace : WordTrace (prefixWord ++ tailWord_2130634) baseStart_2130634 baseEnd_2130634 := by
    simpa [prefixWord, tailWord_2130634, baseEnd_2130634] using wordTrace_append hprefix tailTrace_2130634
  have hstable : (prefixWord ++ tailWord_2130634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130634).length < 2 ^ (prefixWord ++ tailWord_2130634).sum := by decide
  have hdescent : baseEnd_2130634 < baseStart_2130634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130698 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_2130698 : Nat := 118140960795 + 2130698 * 2 ^ 59
def prefixEnd_2130698 : Nat := 4983230072969 + 3 ^ 40 * 2130698 * 2
def baseEnd_2130698 : Nat := 729381469049073245317403

theorem tailTrace_2130698 : CollatzResearch.WordTrace tailWord_2130698 prefixEnd_2130698 729381469049073245317403 := by
  unfold tailWord_2130698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19428235108713128773102187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51808626956568343394939165 19428235108713128773102187)
  ·
    refine ⟨29142352663069693159653281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19428235108713128773102187 29142352663069693159653281)
    ·
      refine ⟨21856764497302269869739961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29142352663069693159653281 21856764497302269869739961)
      ·
        refine ⟨16392573372976702402304971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21856764497302269869739961 16392573372976702402304971)
        ·
          refine ⟨24588860059465053603457457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16392573372976702402304971 24588860059465053603457457)
          ·
            refine ⟨18441645044598790202593093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24588860059465053603457457 18441645044598790202593093)
            ·
              refine ⟨3457808445862273162986205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18441645044598790202593093 3457808445862273162986205)
              ·
                refine ⟨1296678167198352436119827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3457808445862273162986205 1296678167198352436119827)
                ·
                  refine ⟨1945017250797528654179741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296678167198352436119827 1945017250797528654179741)
                  ·
                    refine ⟨729381469049073245317403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945017250797528654179741 729381469049073245317403)
                    ·
                      rfl

theorem cell22_2130698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_2130698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130698 prefixEnd_2130698 := by exact prefixLift 2130698
  have htrace : WordTrace (prefixWord ++ tailWord_2130698) baseStart_2130698 baseEnd_2130698 := by
    simpa [prefixWord, tailWord_2130698, baseEnd_2130698] using wordTrace_append hprefix tailTrace_2130698
  have hstable : (prefixWord ++ tailWord_2130698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130698).length < 2 ^ (prefixWord ++ tailWord_2130698).sum := by decide
  have hdescent : baseEnd_2130698 < baseStart_2130698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130739 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 6]
def baseStart_2130739 : Nat := 118140960795 + 2130739 * 2 ^ 59
def prefixEnd_2130739 : Nat := 4983230072969 + 3 ^ 40 * 2130739 * 2
def baseEnd_2130739 : Nat := 243131834728987601680759

theorem tailTrace_2130739 : CollatzResearch.WordTrace tailWord_2130739 prefixEnd_2130739 243131834728987601680759 := by
  unfold tailWord_2130739
  simp only [CollatzResearch.WordTrace]
  refine ⟨77714435827703979094651271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51809623885135986063100847 77714435827703979094651271)
  ·
    refine ⟨116571653741555968641976907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77714435827703979094651271 116571653741555968641976907)
    ·
      refine ⟨174857480612333952962965361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116571653741555968641976907 174857480612333952962965361)
      ·
        refine ⟨131143110459250464722224021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174857480612333952962965361 131143110459250464722224021)
        ·
          refine ⟨6147333302777365533854251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131143110459250464722224021 6147333302777365533854251)
          ·
            refine ⟨9220999954166048300781377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147333302777365533854251 9220999954166048300781377)
            ·
              refine ⟨6915749965624536225586033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9220999954166048300781377 6915749965624536225586033)
              ·
                refine ⟨5186812474218402169189525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6915749965624536225586033 5186812474218402169189525)
                ·
                  refine ⟨243131834728987601680759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5186812474218402169189525 243131834728987601680759)
                  ·
                    rfl

theorem cell22_2130739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_2130739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130739 prefixEnd_2130739 := by exact prefixLift 2130739
  have htrace : WordTrace (prefixWord ++ tailWord_2130739) baseStart_2130739 baseEnd_2130739 := by
    simpa [prefixWord, tailWord_2130739, baseEnd_2130739] using wordTrace_append hprefix tailTrace_2130739
  have hstable : (prefixWord ++ tailWord_2130739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130739).length < 2 ^ (prefixWord ++ tailWord_2130739).sum := by decide
  have hdescent : baseEnd_2130739 < baseStart_2130739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130741 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2130741 : Nat := 118140960795 + 2130741 * 2 ^ 59
def prefixEnd_2130741 : Nat := 4983230072969 + 3 ^ 40 * 2130741 * 2
def baseEnd_2130741 : Nat := 729396188827835466492271

theorem tailTrace_2130741 : CollatzResearch.WordTrace tailWord_2130741 prefixEnd_2130741 729396188827835466492271 := by
  unfold tailWord_2130741
  simp only [CollatzResearch.WordTrace]
  refine ⟨77714508773696733436224077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51809672515797822290816051 77714508773696733436224077)
  ·
    refine ⟨29142940790136275038584029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77714508773696733436224077 29142940790136275038584029)
    ·
      refine ⟨10928602796301103139469011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29142940790136275038584029 10928602796301103139469011)
      ·
        refine ⟨16392904194451654709203517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928602796301103139469011 16392904194451654709203517)
        ·
          refine ⟨6147339072919370515951319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16392904194451654709203517 6147339072919370515951319)
          ·
            refine ⟨9221008609379055773926979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147339072919370515951319 9221008609379055773926979)
            ·
              refine ⟨13831512914068583660890469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9221008609379055773926979 13831512914068583660890469)
              ·
                refine ⟨2593408671387859436416963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13831512914068583660890469 2593408671387859436416963)
                ·
                  refine ⟨3890113007081789154625445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593408671387859436416963 3890113007081789154625445)
                  ·
                    refine ⟨729396188827835466492271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890113007081789154625445 729396188827835466492271)
                    ·
                      rfl

theorem cell22_2130741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2130741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130741 prefixEnd_2130741 := by exact prefixLift 2130741
  have htrace : WordTrace (prefixWord ++ tailWord_2130741) baseStart_2130741 baseEnd_2130741 := by
    simpa [prefixWord, tailWord_2130741, baseEnd_2130741] using wordTrace_append hprefix tailTrace_2130741
  have hstable : (prefixWord ++ tailWord_2130741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130741).length < 2 ^ (prefixWord ++ tailWord_2130741).sum := by decide
  have hdescent : baseEnd_2130741 < baseStart_2130741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130773 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 4]
def baseStart_2130773 : Nat := 118140960795 + 2130773 * 2 ^ 59
def prefixEnd_2130773 : Nat := 4983230072969 + 3 ^ 40 * 2130773 * 2
def baseEnd_2130773 : Nat := 243135714360599349897391

theorem tailTrace_2130773 : CollatzResearch.WordTrace tailWord_2130773 prefixEnd_2130773 243135714360599349897391 := by
  unfold tailWord_2130773
  simp only [CollatzResearch.WordTrace]
  refine ⟨77715675909580802901388973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51810450606387201934259315 77715675909580802901388973)
  ·
    refine ⟨29143378466092801088020865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77715675909580802901388973 29143378466092801088020865)
    ·
      refine ⟨21857533849569600816015649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29143378466092801088020865 21857533849569600816015649)
      ·
        refine ⟨16393150387177200612011737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21857533849569600816015649 16393150387177200612011737)
        ·
          refine ⟨12294862790382900459008803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16393150387177200612011737 12294862790382900459008803)
          ·
            refine ⟨18442294185574350688513205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12294862790382900459008803 18442294185574350688513205)
            ·
              refine ⟨1728965079897595377048113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18442294185574350688513205 1728965079897595377048113)
              ·
                refine ⟨1296723809923196532786085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1728965079897595377048113 1296723809923196532786085)
                ·
                  refine ⟨243135714360599349897391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296723809923196532786085 243135714360599349897391)
                  ·
                    rfl

theorem cell22_2130773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_2130773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130773 prefixEnd_2130773 := by exact prefixLift 2130773
  have htrace : WordTrace (prefixWord ++ tailWord_2130773) baseStart_2130773 baseEnd_2130773 := by
    simpa [prefixWord, tailWord_2130773, baseEnd_2130773] using wordTrace_append hprefix tailTrace_2130773
  have hstable : (prefixWord ++ tailWord_2130773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130773).length < 2 ^ (prefixWord ++ tailWord_2130773).sum := by decide
  have hdescent : baseEnd_2130773 < baseStart_2130773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130784 : List Nat := [2, 1, 1, 3, 3, 1, 4, 7]
def baseStart_2130784 : Nat := 118140960795 + 2130784 * 2 ^ 59
def prefixEnd_2130784 : Nat := 4983230072969 + 3 ^ 40 * 2130784 * 2
def baseEnd_2130784 : Nat := 81045656511844187518571

theorem tailTrace_2130784 : CollatzResearch.WordTrace tailWord_2130784 prefixEnd_2130784 81045656511844187518571 := by
  unfold tailWord_2130784
  simp only [CollatzResearch.WordTrace]
  refine ⟨38858038556270475890019703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51810718075027301186692937 38858038556270475890019703)
  ·
    refine ⟨58287057834405713835029555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38858038556270475890019703 58287057834405713835029555)
    ·
      refine ⟨87430586751608570752544333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58287057834405713835029555 87430586751608570752544333)
      ·
        refine ⟨32786470031853214032204125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87430586751608570752544333 32786470031853214032204125)
        ·
          refine ⟨12294926261944955262076547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32786470031853214032204125 12294926261944955262076547)
          ·
            refine ⟨18442389392917432893114821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12294926261944955262076547 18442389392917432893114821)
            ·
              refine ⟨3457948011172018667459029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18442389392917432893114821 3457948011172018667459029)
              ·
                refine ⟨81045656511844187518571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3457948011172018667459029 81045656511844187518571)
                ·
                  rfl

theorem cell22_2130784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_2130784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130784 prefixEnd_2130784 := by exact prefixLift 2130784
  have htrace : WordTrace (prefixWord ++ tailWord_2130784) baseStart_2130784 baseEnd_2130784 := by
    simpa [prefixWord, tailWord_2130784, baseEnd_2130784] using wordTrace_append hprefix tailTrace_2130784
  have hstable : (prefixWord ++ tailWord_2130784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130784).length < 2 ^ (prefixWord ++ tailWord_2130784).sum := by decide
  have hdescent : baseEnd_2130784 < baseStart_2130784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130788 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_2130788 : Nat := 118140960795 + 2130788 * 2 ^ 59
def prefixEnd_2130788 : Nat := 4983230072969 + 3 ^ 40 * 2130788 * 2
def baseEnd_2130788 : Nat := 729412277888343010567127

theorem tailTrace_2130788 : CollatzResearch.WordTrace tailWord_2130788 prefixEnd_2130788 729412277888343010567127 := by
  unfold tailWord_2130788
  simp only [CollatzResearch.WordTrace]
  refine ⟨38858111502263230231592509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51810815336350973642123345 38858111502263230231592509)
  ·
    refine ⟨14571791813348711336847191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38858111502263230231592509 14571791813348711336847191)
    ·
      refine ⟨21857687720023067005270787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14571791813348711336847191 21857687720023067005270787)
      ·
        refine ⟨32786531580034600507906181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21857687720023067005270787 32786531580034600507906181)
        ·
          refine ⟨6147474671256487595232409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32786531580034600507906181 6147474671256487595232409)
          ·
            refine ⟨4610606003442365696424307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6147474671256487595232409 4610606003442365696424307)
            ·
              refine ⟨6915909005163548544636461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610606003442365696424307 6915909005163548544636461)
              ·
                refine ⟨2593465876936330704238673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6915909005163548544636461 2593465876936330704238673)
                ·
                  refine ⟨1945099407702248028179005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2593465876936330704238673 1945099407702248028179005)
                  ·
                    refine ⟨729412277888343010567127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945099407702248028179005 729412277888343010567127)
                    ·
                      rfl

theorem cell22_2130788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_2130788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130788 prefixEnd_2130788 := by exact prefixLift 2130788
  have htrace : WordTrace (prefixWord ++ tailWord_2130788) baseStart_2130788 baseEnd_2130788 := by
    simpa [prefixWord, tailWord_2130788, baseEnd_2130788] using wordTrace_append hprefix tailTrace_2130788
  have hstable : (prefixWord ++ tailWord_2130788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130788).length < 2 ^ (prefixWord ++ tailWord_2130788).sum := by decide
  have hdescent : baseEnd_2130788 < baseStart_2130788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130818 : List Nat := [3, 4, 2, 2, 1, 10]
def baseStart_2130818 : Nat := 118140960795 + 2130818 * 2 ^ 59
def prefixEnd_2130818 : Nat := 4983230072969 + 3 ^ 40 * 2130818 * 2
def baseEnd_2130818 : Nat := 9005216635820159658235

theorem tailTrace_2130818 : CollatzResearch.WordTrace tailWord_2130818 prefixEnd_2130818 9005216635820159658235 := by
  unfold tailWord_2130818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19429329298604443896694277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51811544796278517057851405 19429329298604443896694277)
  ·
    refine ⟨3642999243488333230630177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19429329298604443896694277 3642999243488333230630177)
    ·
      refine ⟨2732249432616249922972633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3642999243488333230630177 2732249432616249922972633)
      ·
        refine ⟨2049187074462187442229475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2732249432616249922972633 2049187074462187442229475)
        ·
          refine ⟨3073780611693281163344213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049187074462187442229475 3073780611693281163344213)
          ·
            refine ⟨9005216635820159658235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3073780611693281163344213 9005216635820159658235)
            ·
              rfl

theorem cell22_2130818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 10].length) (baseStart_2130818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130818 prefixEnd_2130818 := by exact prefixLift 2130818
  have htrace : WordTrace (prefixWord ++ tailWord_2130818) baseStart_2130818 baseEnd_2130818 := by
    simpa [prefixWord, tailWord_2130818, baseEnd_2130818] using wordTrace_append hprefix tailTrace_2130818
  have hstable : (prefixWord ++ tailWord_2130818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130818).length < 2 ^ (prefixWord ++ tailWord_2130818).sum := by decide
  have hdescent : baseEnd_2130818 < baseStart_2130818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130874 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_2130874 : Nat := 118140960795 + 2130874 * 2 ^ 59
def prefixEnd_2130874 : Nat := 4983230072969 + 3 ^ 40 * 2130874 * 2
def baseEnd_2130874 : Nat := 243147239148622484305621

theorem tailTrace_2130874 : CollatzResearch.WordTrace tailWord_2130874 prefixEnd_2130874 243147239148622484305621 := by
  unfold tailWord_2130874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19429839920553724287703919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51812906454809931433877117 19429839920553724287703919)
  ·
    refine ⟨29144759880830586431555879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19429839920553724287703919 29144759880830586431555879)
    ·
      refine ⟨43717139821245879647333819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29144759880830586431555879 43717139821245879647333819)
      ·
        refine ⟨65575709731868819471000729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43717139821245879647333819 65575709731868819471000729)
        ·
          refine ⟨49181782298901614603250547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65575709731868819471000729 49181782298901614603250547)
          ·
            refine ⟨73772673448352421904875821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49181782298901614603250547 73772673448352421904875821)
            ·
              refine ⟨27664752543132158214328433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73772673448352421904875821 27664752543132158214328433)
              ·
                refine ⟨20748564407349118660746325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27664752543132158214328433 20748564407349118660746325)
                ·
                  refine ⟨243147239148622484305621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20748564407349118660746325 243147239148622484305621)
                  ·
                    rfl

theorem cell22_2130874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_2130874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130874 prefixEnd_2130874 := by exact prefixLift 2130874
  have htrace : WordTrace (prefixWord ++ tailWord_2130874) baseStart_2130874 baseEnd_2130874 := by
    simpa [prefixWord, tailWord_2130874, baseEnd_2130874] using wordTrace_append hprefix tailTrace_2130874
  have hstable : (prefixWord ++ tailWord_2130874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130874).length < 2 ^ (prefixWord ++ tailWord_2130874).sum := by decide
  have hdescent : baseEnd_2130874 < baseStart_2130874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2130891 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 6]
def baseStart_2130891 : Nat := 118140960795 + 2130891 * 2 ^ 59
def prefixEnd_2130891 : Nat := 4983230072969 + 3 ^ 40 * 2130891 * 2
def baseEnd_2130891 : Nat := 243149178964428358413937

theorem tailTrace_2130891 : CollatzResearch.WordTrace tailWord_2130891 prefixEnd_2130891 243149178964428358413937 := by
  unfold tailWord_2130891
  simp only [CollatzResearch.WordTrace]
  refine ⟨77719979723153309054184527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51813319815435539369456351 77719979723153309054184527)
  ·
    refine ⟨116579969584729963581276791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77719979723153309054184527 116579969584729963581276791)
    ·
      refine ⟨174869954377094945371915187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116579969584729963581276791 174869954377094945371915187)
      ·
        refine ⟨262304931565642418057872781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174869954377094945371915187 262304931565642418057872781)
        ·
          refine ⟨98364349337115906771702293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262304931565642418057872781 98364349337115906771702293)
          ·
            refine ⟨4610828875177308129923545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98364349337115906771702293 4610828875177308129923545)
            ·
              refine ⟨3458121656382981097442659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610828875177308129923545 3458121656382981097442659)
              ·
                refine ⟨5187182484574471646163989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458121656382981097442659 5187182484574471646163989)
                ·
                  refine ⟨243149178964428358413937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5187182484574471646163989 243149178964428358413937)
                  ·
                    rfl

theorem cell22_2130891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 6].length) (baseStart_2130891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130891 prefixEnd_2130891 := by exact prefixLift 2130891
  have htrace : WordTrace (prefixWord ++ tailWord_2130891) baseStart_2130891 baseEnd_2130891 := by
    simpa [prefixWord, tailWord_2130891, baseEnd_2130891] using wordTrace_append hprefix tailTrace_2130891
  have hstable : (prefixWord ++ tailWord_2130891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130891).length < 2 ^ (prefixWord ++ tailWord_2130891).sum := by decide
  have hdescent : baseEnd_2130891 < baseStart_2130891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
