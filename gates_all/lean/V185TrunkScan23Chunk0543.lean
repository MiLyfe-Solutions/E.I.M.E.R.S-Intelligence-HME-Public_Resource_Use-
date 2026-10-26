import V185TrunkScan23Chunk0542

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3211262 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3211262 : Nat := 118140960795 + 3211262 * 2 ^ 59
def prefixEnd_3211262 : Nat := 4983230072969 + 3 ^ 40 * 3211262 * 2
def baseEnd_3211262 : Nat := 549640304506173385452227

theorem tailTrace_3211262 : CollatzResearch.WordTrace tailWord_3211262 prefixEnd_3211262 549640304506173385452227 := by
  unfold tailWord_3211262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640543411519211091397505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78082898194769125820786693 14640543411519211091397505)
  ·
    refine ⟨10980407558639408318548129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14640543411519211091397505 10980407558639408318548129)
    ·
      refine ⟨8235305668979556238911097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10980407558639408318548129 8235305668979556238911097)
      ·
        refine ⟨6176479251734667179183323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8235305668979556238911097 6176479251734667179183323)
        ·
          refine ⟨9264718877602000768774985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176479251734667179183323 9264718877602000768774985)
          ·
            refine ⟨6948539158201500576581239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9264718877602000768774985 6948539158201500576581239)
            ·
              refine ⟨10422808737302250864871859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6948539158201500576581239 10422808737302250864871859)
              ·
                refine ⟨15634213105953376297307789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422808737302250864871859 15634213105953376297307789)
                ·
                  refine ⟨5862829914732516111490421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15634213105953376297307789 5862829914732516111490421)
                  ·
                    refine ⟨549640304506173385452227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5862829914732516111490421 549640304506173385452227)
                    ·
                      rfl

theorem cell23_3211262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3211262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211262 prefixEnd_3211262 := by exact prefixLift 3211262
  have htrace : WordTrace (prefixWord ++ tailWord_3211262) baseStart_3211262 baseEnd_3211262 := by
    simpa [prefixWord, tailWord_3211262, baseEnd_3211262] using wordTrace_append hprefix tailTrace_3211262
  have hstable : (prefixWord ++ tailWord_3211262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211262).length < 2 ^ (prefixWord ++ tailWord_3211262).sum := by decide
  have hdescent : baseEnd_3211262 < baseStart_3211262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211265 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3211265 : Nat := 118140960795 + 3211265 * 2 ^ 59
def prefixEnd_3211265 : Nat := 4983230072969 + 3 ^ 40 * 3211265 * 2
def baseEnd_3211265 : Nat := 1648922453960483644619167

theorem tailTrace_3211265 : CollatzResearch.WordTrace tailWord_3211265 prefixEnd_3211265 1648922453960483644619167 := by
  unfold tailWord_3211265
  simp only [CollatzResearch.WordTrace]
  refine ⟨117124456711142820243539249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78082971140761880162359499 117124456711142820243539249)
  ·
    refine ⟨87843342533357115182654437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117124456711142820243539249 87843342533357115182654437)
    ·
      refine ⟨16470626725004459096747707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87843342533357115182654437 16470626725004459096747707)
      ·
        refine ⟨24705940087506688645121561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16470626725004459096747707 24705940087506688645121561)
        ·
          refine ⟨18529455065630016483841171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24705940087506688645121561 18529455065630016483841171)
          ·
            refine ⟨27794182598445024725761757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18529455065630016483841171 27794182598445024725761757)
            ·
              refine ⟨10422818474416884272160659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27794182598445024725761757 10422818474416884272160659)
              ·
                refine ⟨15634227711625326408240989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422818474416884272160659 15634227711625326408240989)
                ·
                  refine ⟨5862835391859497403090371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15634227711625326408240989 5862835391859497403090371)
                  ·
                    refine ⟨8794253087789246104635557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5862835391859497403090371 8794253087789246104635557)
                    ·
                      refine ⟨1648922453960483644619167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8794253087789246104635557 1648922453960483644619167)
                      ·
                        rfl

theorem cell23_3211265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3211265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211265 prefixEnd_3211265 := by exact prefixLift 3211265
  have htrace : WordTrace (prefixWord ++ tailWord_3211265) baseStart_3211265 baseEnd_3211265 := by
    simpa [prefixWord, tailWord_3211265, baseEnd_3211265] using wordTrace_append hprefix tailTrace_3211265
  have hstable : (prefixWord ++ tailWord_3211265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211265).length < 2 ^ (prefixWord ++ tailWord_3211265).sum := by decide
  have hdescent : baseEnd_3211265 < baseStart_3211265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211292 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_3211292 : Nat := 118140960795 + 3211292 * 2 ^ 59
def prefixEnd_3211292 : Nat := 4983230072969 + 3 ^ 40 * 3211292 * 2
def baseEnd_3211292 : Nat := 549645439312718346327181

theorem tailTrace_3211292 : CollatzResearch.WordTrace tailWord_3211292 prefixEnd_3211292 549645439312718346327181 := by
  unfold tailWord_3211292
  simp only [CollatzResearch.WordTrace]
  refine ⟨58562720741022501927386065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78083627654696669236514753 58562720741022501927386065)
  ·
    refine ⟨43922040555766876445539549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58562720741022501927386065 43922040555766876445539549)
    ·
      refine ⟨16470765208412578667077331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43922040555766876445539549 16470765208412578667077331)
      ·
        refine ⟨24706147812618868000615997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16470765208412578667077331 24706147812618868000615997)
        ·
          refine ⟨9264805429732075500230999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24706147812618868000615997 9264805429732075500230999)
          ·
            refine ⟨13897208144598113250346499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264805429732075500230999 13897208144598113250346499)
            ·
              refine ⟨20845812216897169875519749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13897208144598113250346499 20845812216897169875519749)
              ·
                refine ⟨3908589790668219351659953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20845812216897169875519749 3908589790668219351659953)
                ·
                  refine ⟨2931442343001164513744965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3908589790668219351659953 2931442343001164513744965)
                  ·
                    refine ⟨549645439312718346327181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2931442343001164513744965 549645439312718346327181)
                    ·
                      rfl

theorem cell23_3211292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_3211292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211292 prefixEnd_3211292 := by exact prefixLift 3211292
  have htrace : WordTrace (prefixWord ++ tailWord_3211292) baseStart_3211292 baseEnd_3211292 := by
    simpa [prefixWord, tailWord_3211292, baseEnd_3211292] using wordTrace_append hprefix tailTrace_3211292
  have hstable : (prefixWord ++ tailWord_3211292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211292).length < 2 ^ (prefixWord ++ tailWord_3211292).sum := by decide
  have hdescent : baseEnd_3211292 < baseStart_3211292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211293 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_3211293 : Nat := 118140960795 + 3211293 * 2 ^ 59
def prefixEnd_3211293 : Nat := 4983230072969 + 3 ^ 40 * 3211293 * 2
def baseEnd_3211293 : Nat := 1648936831418809535069039

theorem tailTrace_3211293 : CollatzResearch.WordTrace tailWord_3211293 prefixEnd_3211293 1648936831418809535069039 := by
  unfold tailWord_3211293
  simp only [CollatzResearch.WordTrace]
  refine ⟨117125477955041381025558533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78083651970027587350372355 117125477955041381025558533)
  ·
    refine ⟨21961027116570258942292225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117125477955041381025558533 21961027116570258942292225)
    ·
      refine ⟨16470770337427694206719169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21961027116570258942292225 16470770337427694206719169)
      ·
        refine ⟨12353077753070770655039377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16470770337427694206719169 12353077753070770655039377)
        ·
          refine ⟨9264808314803077991279533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12353077753070770655039377 9264808314803077991279533)
          ·
            refine ⟨3474303118051154246729825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9264808314803077991279533 3474303118051154246729825)
            ·
              refine ⟨2605727338538365685047369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3474303118051154246729825 2605727338538365685047369)
              ·
                refine ⟨1954295503903774263785527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2605727338538365685047369 1954295503903774263785527)
                ·
                  refine ⟨2931443255855661395678291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954295503903774263785527 2931443255855661395678291)
                  ·
                    refine ⟨4397164883783492093517437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931443255855661395678291 4397164883783492093517437)
                    ·
                      refine ⟨1648936831418809535069039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397164883783492093517437 1648936831418809535069039)
                      ·
                        rfl

theorem cell23_3211293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_3211293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211293 prefixEnd_3211293 := by exact prefixLift 3211293
  have htrace : WordTrace (prefixWord ++ tailWord_3211293) baseStart_3211293 baseEnd_3211293 := by
    simpa [prefixWord, tailWord_3211293, baseEnd_3211293] using wordTrace_append hprefix tailTrace_3211293
  have hstable : (prefixWord ++ tailWord_3211293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211293).length < 2 ^ (prefixWord ++ tailWord_3211293).sum := by decide
  have hdescent : baseEnd_3211293 < baseStart_3211293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211315 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 3]
def baseStart_3211315 : Nat := 118140960795 + 3211315 * 2 ^ 59
def prefixEnd_3211315 : Nat := 4983230072969 + 3 ^ 40 * 3211315 * 2
def baseEnd_3211315 : Nat := 1648948127993208448993937

theorem tailTrace_3211315 : CollatzResearch.WordTrace tailWord_3211315 prefixEnd_3211315 1648948127993208448993937 := by
  unfold tailWord_3211315
  simp only [CollatzResearch.WordTrace]
  refine ⟨117126280360961678782859399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78084186907307785855239599 117126280360961678782859399)
  ·
    refine ⟨175689420541442518174289099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117126280360961678782859399 175689420541442518174289099)
    ·
      refine ⟨263534130812163777261433649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175689420541442518174289099 263534130812163777261433649)
      ·
        refine ⟨197650598109122832946075237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263534130812163777261433649 197650598109122832946075237)
        ·
          refine ⟨37059487145460531177389107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197650598109122832946075237 37059487145460531177389107)
          ·
            refine ⟨55589230718190796766083661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37059487145460531177389107 55589230718190796766083661)
            ·
              refine ⟨20845961519321548787281373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55589230718190796766083661 20845961519321548787281373)
              ·
                refine ⟨7817235569745580795230515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20845961519321548787281373 7817235569745580795230515)
                ·
                  refine ⟨11725853354618371192845773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817235569745580795230515 11725853354618371192845773)
                  ·
                    refine ⟨4397195007981889197317165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11725853354618371192845773 4397195007981889197317165)
                    ·
                      refine ⟨1648948127993208448993937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397195007981889197317165 1648948127993208448993937)
                      ·
                        rfl

theorem cell23_3211315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_3211315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211315 prefixEnd_3211315 := by exact prefixLift 3211315
  have htrace : WordTrace (prefixWord ++ tailWord_3211315) baseStart_3211315 baseEnd_3211315 := by
    simpa [prefixWord, tailWord_3211315, baseEnd_3211315] using wordTrace_append hprefix tailTrace_3211315
  have hstable : (prefixWord ++ tailWord_3211315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211315).length < 2 ^ (prefixWord ++ tailWord_3211315).sum := by decide
  have hdescent : baseEnd_3211315 < baseStart_3211315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211349 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3211349 : Nat := 118140960795 + 3211349 * 2 ^ 59
def prefixEnd_3211349 : Nat := 4983230072969 + 3 ^ 40 * 3211349 * 2
def baseEnd_3211349 : Nat := 1648965586335461315968781

theorem tailTrace_3211349 : CollatzResearch.WordTrace tailWord_3211349 prefixEnd_3211349 1648965586335461315968781 := by
  unfold tailWord_3211349
  simp only [CollatzResearch.WordTrace]
  refine ⟨117127520442838502589597101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78085013628559001726398067 117127520442838502589597101)
  ·
    refine ⟨43922820166064438471098913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117127520442838502589597101 43922820166064438471098913)
    ·
      refine ⟨32942115124548328853324185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43922820166064438471098913 32942115124548328853324185)
      ·
        refine ⟨24706586343411246639993139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32942115124548328853324185 24706586343411246639993139)
        ·
          refine ⟨37059879515116869959989709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24706586343411246639993139 37059879515116869959989709)
          ·
            refine ⟨13897454818168826234996141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37059879515116869959989709 13897454818168826234996141)
            ·
              refine ⟨5211545556813309838123553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13897454818168826234996141 5211545556813309838123553)
              ·
                refine ⟨3908659167609982378592665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211545556813309838123553 3908659167609982378592665)
                ·
                  refine ⟨2931494375707486783944499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3908659167609982378592665 2931494375707486783944499)
                  ·
                    refine ⟨4397241563561230175916749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931494375707486783944499 4397241563561230175916749)
                    ·
                      refine ⟨1648965586335461315968781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397241563561230175916749 1648965586335461315968781)
                      ·
                        rfl

theorem cell23_3211349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3211349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211349 prefixEnd_3211349 := by exact prefixLift 3211349
  have htrace : WordTrace (prefixWord ++ tailWord_3211349) baseStart_3211349 baseEnd_3211349 := by
    simpa [prefixWord, tailWord_3211349, baseEnd_3211349] using wordTrace_append hprefix tailTrace_3211349
  have hstable : (prefixWord ++ tailWord_3211349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211349).length < 2 ^ (prefixWord ++ tailWord_3211349).sum := by decide
  have hdescent : baseEnd_3211349 < baseStart_3211349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211350 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3211350 : Nat := 118140960795 + 3211350 * 2 ^ 59
def prefixEnd_3211350 : Nat := 4983230072969 + 3 ^ 40 * 3211350 * 2
def baseEnd_3211350 : Nat := 1648966099816115812056277

theorem tailTrace_3211350 : CollatzResearch.WordTrace tailWord_3211350 prefixEnd_3211350 1648966099816115812056277 := by
  unfold tailWord_3211350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7320472307239679985023969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78085037943889919840255669 7320472307239679985023969)
  ·
    refine ⟨5490354230429759988767977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7320472307239679985023969 5490354230429759988767977)
    ·
      refine ⟨4117765672822319991575983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5490354230429759988767977 4117765672822319991575983)
      ·
        refine ⟨6176648509233479987363975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117765672822319991575983 6176648509233479987363975)
        ·
          refine ⟨9264972763850219981045963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176648509233479987363975 9264972763850219981045963)
          ·
            refine ⟨13897459145775329971568945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264972763850219981045963 13897459145775329971568945)
            ·
              refine ⟨10423094359331497478676709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13897459145775329971568945 10423094359331497478676709)
              ·
                refine ⟨1954330192374655777251883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10423094359331497478676709 1954330192374655777251883)
                ·
                  refine ⟨2931495288561983665877825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954330192374655777251883 2931495288561983665877825)
                  ·
                    refine ⟨2198621466421487749408369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2931495288561983665877825 2198621466421487749408369)
                    ·
                      refine ⟨1648966099816115812056277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198621466421487749408369 1648966099816115812056277)
                      ·
                        rfl

theorem cell23_3211350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3211350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211350 prefixEnd_3211350 := by exact prefixLift 3211350
  have htrace : WordTrace (prefixWord ++ tailWord_3211350) baseStart_3211350 baseEnd_3211350 := by
    simpa [prefixWord, tailWord_3211350, baseEnd_3211350] using wordTrace_append hprefix tailTrace_3211350
  have hstable : (prefixWord ++ tailWord_3211350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211350).length < 2 ^ (prefixWord ++ tailWord_3211350).sum := by decide
  have hdescent : baseEnd_3211350 < baseStart_3211350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211365 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_3211365 : Nat := 118140960795 + 3211365 * 2 ^ 59
def prefixEnd_3211365 : Nat := 4983230072969 + 3 ^ 40 * 3211365 * 2
def baseEnd_3211365 : Nat := 549657934008644417789569

theorem tailTrace_3211365 : CollatzResearch.WordTrace tailWord_3211365 prefixEnd_3211365 549657934008644417789569 := by
  unfold tailWord_3211365
  simp only [CollatzResearch.WordTrace]
  refine ⟨117128104010780537322179549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78085402673853691548119699 117128104010780537322179549)
  ·
    refine ⟨43923039004042701495817331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117128104010780537322179549 43923039004042701495817331)
    ·
      refine ⟨65884558506064052243725997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43923039004042701495817331 65884558506064052243725997)
      ·
        refine ⟨24706709439774019591397249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65884558506064052243725997 24706709439774019591397249)
        ·
          refine ⟨18530032079830514693547937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24706709439774019591397249 18530032079830514693547937)
          ·
            refine ⟨13897524059872886020160953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18530032079830514693547937 13897524059872886020160953)
            ·
              refine ⟨10423143044904664515120715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13897524059872886020160953 10423143044904664515120715)
              ·
                refine ⟨15634714567356996772681073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10423143044904664515120715 15634714567356996772681073)
                ·
                  refine ⟨11726035925517747579510805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15634714567356996772681073 11726035925517747579510805)
                  ·
                    refine ⟨549657934008644417789569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11726035925517747579510805 549657934008644417789569)
                    ·
                      rfl

theorem cell23_3211365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_3211365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211365 prefixEnd_3211365 := by exact prefixLift 3211365
  have htrace : WordTrace (prefixWord ++ tailWord_3211365) baseStart_3211365 baseEnd_3211365 := by
    simpa [prefixWord, tailWord_3211365, baseEnd_3211365] using wordTrace_append hprefix tailTrace_3211365
  have hstable : (prefixWord ++ tailWord_3211365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211365).length < 2 ^ (prefixWord ++ tailWord_3211365).sum := by decide
  have hdescent : baseEnd_3211365 < baseStart_3211365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211389 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_3211389 : Nat := 118140960795 + 3211389 * 2 ^ 59
def prefixEnd_3211389 : Nat := 4983230072969 + 3 ^ 40 * 3211389 * 2
def baseEnd_3211389 : Nat := 1648986125561641159468597

theorem tailTrace_3211389 : CollatzResearch.WordTrace tailWord_3211389 prefixEnd_3211389 1648986125561641159468597 := by
  unfold tailWord_3211389
  simp only [CollatzResearch.WordTrace]
  refine ⟨117128979362693589421053221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78085986241795726280702147 117128979362693589421053221)
  ·
    refine ⟨21961683630505048016447479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117128979362693589421053221 21961683630505048016447479)
    ·
      refine ⟨32942525445757572024671219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21961683630505048016447479 32942525445757572024671219)
      ·
        refine ⟨49413788168636358037006829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32942525445757572024671219 49413788168636358037006829)
        ·
          refine ⟨18530170563238634263877561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49413788168636358037006829 18530170563238634263877561)
          ·
            refine ⟨13897627922428975697908171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18530170563238634263877561 13897627922428975697908171)
            ·
              refine ⟨20846441883643463546862257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13897627922428975697908171 20846441883643463546862257)
              ·
                refine ⟨15634831412732597660146693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20846441883643463546862257 15634831412732597660146693)
                ·
                  refine ⟨2931530889887362061277505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15634831412732597660146693 2931530889887362061277505)
                  ·
                    refine ⟨2198648167415521545958129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2931530889887362061277505 2198648167415521545958129)
                    ·
                      refine ⟨1648986125561641159468597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198648167415521545958129 1648986125561641159468597)
                      ·
                        rfl

theorem cell23_3211389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_3211389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211389 prefixEnd_3211389 := by exact prefixLift 3211389
  have htrace : WordTrace (prefixWord ++ tailWord_3211389) baseStart_3211389 baseEnd_3211389 := by
    simpa [prefixWord, tailWord_3211389, baseEnd_3211389] using wordTrace_append hprefix tailTrace_3211389
  have hstable : (prefixWord ++ tailWord_3211389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211389).length < 2 ^ (prefixWord ++ tailWord_3211389).sum := by decide
  have hdescent : baseEnd_3211389 < baseStart_3211389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211423 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3211423 : Nat := 118140960795 + 3211423 * 2 ^ 59
def prefixEnd_3211423 : Nat := 4983230072969 + 3 ^ 40 * 3211423 * 2
def baseEnd_3211423 : Nat := 1649003583903894026443441

theorem tailTrace_3211423 : CollatzResearch.WordTrace tailWord_3211423 prefixEnd_3211423 1649003583903894026443441 := by
  unfold tailWord_3211423
  simp only [CollatzResearch.WordTrace]
  refine ⟨117130219444570413227790923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78086812963046942151860615 117130219444570413227790923)
  ·
    refine ⟨175695329166855619841686385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117130219444570413227790923 175695329166855619841686385)
    ·
      refine ⟨131771496875141714881264789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175695329166855619841686385 131771496875141714881264789)
      ·
        refine ⟨6176788916022267885059287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131771496875141714881264789 6176788916022267885059287)
        ·
          refine ⟨9265183374033401827588931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176788916022267885059287 9265183374033401827588931)
          ·
            refine ⟨13897775061050102741383397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9265183374033401827588931 13897775061050102741383397)
            ·
              refine ⟨2605832823946894264009387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13897775061050102741383397 2605832823946894264009387)
              ·
                refine ⟨3908749235920341396014081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605832823946894264009387 3908749235920341396014081)
                ·
                  refine ⟨2931561926940256047010561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3908749235920341396014081 2931561926940256047010561)
                  ·
                    refine ⟨2198671445205192035257921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2931561926940256047010561 2198671445205192035257921)
                    ·
                      refine ⟨1649003583903894026443441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198671445205192035257921 1649003583903894026443441)
                      ·
                        rfl

theorem cell23_3211423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3211423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211423 prefixEnd_3211423 := by exact prefixLift 3211423
  have htrace : WordTrace (prefixWord ++ tailWord_3211423) baseStart_3211423 baseEnd_3211423 := by
    simpa [prefixWord, tailWord_3211423, baseEnd_3211423] using wordTrace_append hprefix tailTrace_3211423
  have hstable : (prefixWord ++ tailWord_3211423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211423).length < 2 ^ (prefixWord ++ tailWord_3211423).sum := by decide
  have hdescent : baseEnd_3211423 < baseStart_3211423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211442 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_3211442 : Nat := 118140960795 + 3211442 * 2 ^ 59
def prefixEnd_3211442 : Nat := 4983230072969 + 3 ^ 40 * 3211442 * 2
def baseEnd_3211442 : Nat := 549671113345443150701951

theorem tailTrace_3211442 : CollatzResearch.WordTrace tailWord_3211442 prefixEnd_3211442 549671113345443150701951 := by
  unfold tailWord_3211442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29282728107875394868183145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78087274954334386315155053 29282728107875394868183145)
  ·
    refine ⟨21962046080906546151137359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29282728107875394868183145 21962046080906546151137359)
    ·
      refine ⟨32943069121359819226706039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21962046080906546151137359 32943069121359819226706039)
      ·
        refine ⟨49414603682039728840059059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32943069121359819226706039 49414603682039728840059059)
        ·
          refine ⟨74121905523059593260088589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49414603682039728840059059 74121905523059593260088589)
          ·
            refine ⟨27795714571147347472533221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74121905523059593260088589 27795714571147347472533221)
            ·
              refine ⟨5211696482090127651099979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27795714571147347472533221 5211696482090127651099979)
              ·
                refine ⟨7817544723135191476649969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211696482090127651099979 7817544723135191476649969)
                ·
                  refine ⟨5863158542351393607487477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7817544723135191476649969 5863158542351393607487477)
                  ·
                    refine ⟨549671113345443150701951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5863158542351393607487477 549671113345443150701951)
                    ·
                      rfl

theorem cell23_3211442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_3211442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211442 prefixEnd_3211442 := by exact prefixLift 3211442
  have htrace : WordTrace (prefixWord ++ tailWord_3211442) baseStart_3211442 baseEnd_3211442 := by
    simpa [prefixWord, tailWord_3211442, baseEnd_3211442] using wordTrace_append hprefix tailTrace_3211442
  have hstable : (prefixWord ++ tailWord_3211442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211442).length < 2 ^ (prefixWord ++ tailWord_3211442).sum := by decide
  have hdescent : baseEnd_3211442 < baseStart_3211442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211482 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_3211482 : Nat := 118140960795 + 3211482 * 2 ^ 59
def prefixEnd_3211482 : Nat := 4983230072969 + 3 ^ 40 * 3211482 * 2
def baseEnd_3211482 : Nat := 1649033879262509295605669

theorem tailTrace_3211482 : CollatzResearch.WordTrace tailWord_3211482 prefixEnd_3211482 1649033879262509295605669 := by
  unfold tailWord_3211482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29283092837839166576047175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78088247567571110869459133 29283092837839166576047175)
  ·
    refine ⟨43924639256758749864070763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29283092837839166576047175 43924639256758749864070763)
    ·
      refine ⟨65886958885138124796106145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43924639256758749864070763 65886958885138124796106145)
      ·
        refine ⟨49415219163853593597079609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65886958885138124796106145 49415219163853593597079609)
        ·
          refine ⟨37061414372890195197809707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49415219163853593597079609 37061414372890195197809707)
          ·
            refine ⟨55592121559335292796714561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37061414372890195197809707 55592121559335292796714561)
            ·
              refine ⟨41694091169501469597535921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55592121559335292796714561 41694091169501469597535921)
              ·
                refine ⟨31270568377126102198151941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41694091169501469597535921 31270568377126102198151941)
                ·
                  refine ⟨5863231570711144162153489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31270568377126102198151941 5863231570711144162153489)
                  ·
                    refine ⟨4397423678033358121615117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5863231570711144162153489 4397423678033358121615117)
                    ·
                      refine ⟨1649033879262509295605669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397423678033358121615117 1649033879262509295605669)
                      ·
                        rfl

theorem cell23_3211482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_3211482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211482 prefixEnd_3211482 := by exact prefixLift 3211482
  have htrace : WordTrace (prefixWord ++ tailWord_3211482) baseStart_3211482 baseEnd_3211482 := by
    simpa [prefixWord, tailWord_3211482, baseEnd_3211482] using wordTrace_append hprefix tailTrace_3211482
  have hstable : (prefixWord ++ tailWord_3211482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211482).length < 2 ^ (prefixWord ++ tailWord_3211482).sum := by decide
  have hdescent : baseEnd_3211482 < baseStart_3211482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211506 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3211506 : Nat := 118140960795 + 3211506 * 2 ^ 59
def prefixEnd_3211506 : Nat := 4983230072969 + 3 ^ 40 * 3211506 * 2
def baseEnd_3211506 : Nat := 549682067599405733901853

theorem tailTrace_3211506 : CollatzResearch.WordTrace tailWord_3211506 prefixEnd_3211506 549682067599405733901853 := by
  unfold tailWord_3211506
  simp only [CollatzResearch.WordTrace]
  refine ⟨29283311675817429600765593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78088831135513145602041581 29283311675817429600765593)
  ·
    refine ⟨21962483756863072200574195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29283311675817429600765593 21962483756863072200574195)
    ·
      refine ⟨32943725635294608300861293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21962483756863072200574195 32943725635294608300861293)
      ·
        refine ⟨12353897113235478112822985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32943725635294608300861293 12353897113235478112822985)
        ·
          refine ⟨9265422834926608584617239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12353897113235478112822985 9265422834926608584617239)
          ·
            refine ⟨13898134252389912876925859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9265422834926608584617239 13898134252389912876925859)
            ·
              refine ⟨20847201378584869315388789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13898134252389912876925859 20847201378584869315388789)
              ·
                refine ⟨1954425129242331498317699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20847201378584869315388789 1954425129242331498317699)
                ·
                  refine ⟨2931637693863497247476549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954425129242331498317699 2931637693863497247476549)
                  ·
                    refine ⟨549682067599405733901853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2931637693863497247476549 549682067599405733901853)
                    ·
                      rfl

theorem cell23_3211506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3211506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211506 prefixEnd_3211506 := by exact prefixLift 3211506
  have htrace : WordTrace (prefixWord ++ tailWord_3211506) baseStart_3211506 baseEnd_3211506 := by
    simpa [prefixWord, tailWord_3211506, baseEnd_3211506] using wordTrace_append hprefix tailTrace_3211506
  have hstable : (prefixWord ++ tailWord_3211506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211506).length < 2 ^ (prefixWord ++ tailWord_3211506).sum := by decide
  have hdescent : baseEnd_3211506 < baseStart_3211506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211525 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_3211525 : Nat := 118140960795 + 3211525 * 2 ^ 59
def prefixEnd_3211525 : Nat := 4983230072969 + 3 ^ 40 * 3211525 * 2
def baseEnd_3211525 : Nat := 1649055958930652627367971

theorem tailTrace_3211525 : CollatzResearch.WordTrace tailWord_3211525 prefixEnd_3211525 1649055958930652627367971 := by
  unfold tailWord_3211525
  simp only [CollatzResearch.WordTrace]
  refine ⟨117133939690200884648004029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78089293126800589765336019 117133939690200884648004029)
  ·
    refine ⟨43925227383825331743001511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117133939690200884648004029 43925227383825331743001511)
    ·
      refine ⟨65887841075737997614502267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43925227383825331743001511 65887841075737997614502267)
      ·
        refine ⟨98831761613606996421753401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65887841075737997614502267 98831761613606996421753401)
        ·
          refine ⟨74123821210205247316315051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98831761613606996421753401 74123821210205247316315051)
          ·
            refine ⟨111185731815307870974472577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74123821210205247316315051 111185731815307870974472577)
            ·
              refine ⟨83389298861480903230854433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111185731815307870974472577 83389298861480903230854433)
              ·
                refine ⟨62541974146110677423140825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83389298861480903230854433 62541974146110677423140825)
                ·
                  refine ⟨46906480609583008067355619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62541974146110677423140825 46906480609583008067355619)
                  ·
                    refine ⟨70359720914374512101033429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46906480609583008067355619 70359720914374512101033429)
                    ·
                      refine ⟨1649055958930652627367971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70359720914374512101033429 1649055958930652627367971)
                      ·
                        rfl

theorem cell23_3211525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_3211525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211525 prefixEnd_3211525 := by exact prefixLift 3211525
  have htrace : WordTrace (prefixWord ++ tailWord_3211525) baseStart_3211525 baseEnd_3211525 := by
    simpa [prefixWord, tailWord_3211525, baseEnd_3211525] using wordTrace_append hprefix tailTrace_3211525
  have hstable : (prefixWord ++ tailWord_3211525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211525).length < 2 ^ (prefixWord ++ tailWord_3211525).sum := by decide
  have hdescent : baseEnd_3211525 < baseStart_3211525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211529 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 3]
def baseStart_3211529 : Nat := 118140960795 + 3211529 * 2 ^ 59
def prefixEnd_3211529 : Nat := 4983230072969 + 3 ^ 40 * 3211529 * 2
def baseEnd_3211529 : Nat := 1649058012853270611717953

theorem tailTrace_3211529 : CollatzResearch.WordTrace tailWord_3211529 prefixEnd_3211529 1649058012853270611717953 := by
  unfold tailWord_3211529
  simp only [CollatzResearch.WordTrace]
  refine ⟨117134085582186393331149641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78089390388124262220766427 117134085582186393331149641)
  ·
    refine ⟨87850564186639794998362231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117134085582186393331149641 87850564186639794998362231)
    ·
      refine ⟨131775846279959692497543347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87850564186639794998362231 131775846279959692497543347)
      ·
        refine ⟨197663769419939538746315021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131775846279959692497543347 197663769419939538746315021)
        ·
          refine ⟨74123913532477327029868133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197663769419939538746315021 74123913532477327029868133)
          ·
            refine ⟨13898233787339498818100275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74123913532477327029868133 13898233787339498818100275)
            ·
              refine ⟨20847350681009248227150413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13898233787339498818100275 20847350681009248227150413)
              ·
                refine ⟨7817756505378468085181405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20847350681009248227150413 7817756505378468085181405)
                ·
                  refine ⟨2931658689516925531943027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7817756505378468085181405 2931658689516925531943027)
                  ·
                    refine ⟨4397488034275388297914541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931658689516925531943027 4397488034275388297914541)
                    ·
                      refine ⟨1649058012853270611717953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397488034275388297914541 1649058012853270611717953)
                      ·
                        rfl

theorem cell23_3211529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_3211529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211529 prefixEnd_3211529 := by exact prefixLift 3211529
  have htrace : WordTrace (prefixWord ++ tailWord_3211529) baseStart_3211529 baseEnd_3211529 := by
    simpa [prefixWord, tailWord_3211529, baseEnd_3211529] using wordTrace_append hprefix tailTrace_3211529
  have hstable : (prefixWord ++ tailWord_3211529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211529).length < 2 ^ (prefixWord ++ tailWord_3211529).sum := by decide
  have hdescent : baseEnd_3211529 < baseStart_3211529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211619 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3211619 : Nat := 118140960795 + 3211619 * 2 ^ 59
def prefixEnd_3211619 : Nat := 4983230072969 + 3 ^ 40 * 3211619 * 2
def baseEnd_3211619 : Nat := 1649104226112175259592539

theorem tailTrace_3211619 : CollatzResearch.WordTrace tailWord_3211619 prefixEnd_3211619 1649104226112175259592539 := by
  unfold tailWord_3211619
  simp only [CollatzResearch.WordTrace]
  refine ⟨117137368151860338701925911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78091578767906892467950607 117137368151860338701925911)
  ·
    refine ⟨175706052227790508052888867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117137368151860338701925911 175706052227790508052888867)
    ·
      refine ⟨263559078341685762079333301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175706052227790508052888867 263559078341685762079333301)
      ·
        refine ⟨24708663594533040194937497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263559078341685762079333301 24708663594533040194937497)
        ·
          refine ⟨18531497695899780146203123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24708663594533040194937497 18531497695899780146203123)
          ·
            refine ⟨27797246543849670219304685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18531497695899780146203123 27797246543849670219304685)
            ·
              refine ⟨10423967453943626332239257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27797246543849670219304685 10423967453943626332239257)
              ·
                refine ⟨7817975590457719749179443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10423967453943626332239257 7817975590457719749179443)
                ·
                  refine ⟨11726963385686579623769165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817975590457719749179443 11726963385686579623769165)
                  ·
                    refine ⟨4397611269632467358913437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11726963385686579623769165 4397611269632467358913437)
                    ·
                      refine ⟨1649104226112175259592539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397611269632467358913437 1649104226112175259592539)
                      ·
                        rfl

theorem cell23_3211619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3211619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211619 prefixEnd_3211619 := by exact prefixLift 3211619
  have htrace : WordTrace (prefixWord ++ tailWord_3211619) baseStart_3211619 baseEnd_3211619 := by
    simpa [prefixWord, tailWord_3211619, baseEnd_3211619] using wordTrace_append hprefix tailTrace_3211619
  have hstable : (prefixWord ++ tailWord_3211619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211619).length < 2 ^ (prefixWord ++ tailWord_3211619).sum := by decide
  have hdescent : baseEnd_3211619 < baseStart_3211619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211623 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_3211623 : Nat := 118140960795 + 3211623 * 2 ^ 59
def prefixEnd_3211623 : Nat := 4983230072969 + 3 ^ 40 * 3211623 * 2
def baseEnd_3211623 : Nat := 1649106280034793243942521

theorem tailTrace_3211623 : CollatzResearch.WordTrace tailWord_3211623 prefixEnd_3211623 1649106280034793243942521 := by
  unfold tailWord_3211623
  simp only [CollatzResearch.WordTrace]
  refine ⟨117137514043845847385071523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78091676029230564923381015 117137514043845847385071523)
  ·
    refine ⟨175706271065768771077607285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117137514043845847385071523 175706271065768771077607285)
    ·
      refine ⟨16472462912415822288525683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175706271065768771077607285 16472462912415822288525683)
      ·
        refine ⟨24708694368623733432788525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16472462912415822288525683 24708694368623733432788525)
        ·
          refine ⟨9265760388233900037295697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24708694368623733432788525 9265760388233900037295697)
          ·
            refine ⟨6949320291175425027971773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9265760388233900037295697 6949320291175425027971773)
            ·
              refine ⟨2605995109190784385489415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6949320291175425027971773 2605995109190784385489415)
              ·
                refine ⟨3908992663786176578234123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605995109190784385489415 3908992663786176578234123)
                ·
                  refine ⟨5863488995679264867351185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908992663786176578234123 5863488995679264867351185)
                  ·
                    refine ⟨4397616746759448650513389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5863488995679264867351185 4397616746759448650513389)
                    ·
                      refine ⟨1649106280034793243942521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397616746759448650513389 1649106280034793243942521)
                      ·
                        rfl

theorem cell23_3211623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_3211623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211623 prefixEnd_3211623 := by exact prefixLift 3211623
  have htrace : WordTrace (prefixWord ++ tailWord_3211623) baseStart_3211623 baseEnd_3211623 := by
    simpa [prefixWord, tailWord_3211623, baseEnd_3211623] using wordTrace_append hprefix tailTrace_3211623
  have hstable : (prefixWord ++ tailWord_3211623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211623).length < 2 ^ (prefixWord ++ tailWord_3211623).sum := by decide
  have hdescent : baseEnd_3211623 < baseStart_3211623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211637 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_3211637 : Nat := 118140960795 + 3211637 * 2 ^ 59
def prefixEnd_3211637 : Nat := 4983230072969 + 3 ^ 40 * 3211637 * 2
def baseEnd_3211637 : Nat := 1649113468763956189167457

theorem tailTrace_3211637 : CollatzResearch.WordTrace tailWord_3211637 prefixEnd_3211637 1649113468763956189167457 := by
  unfold tailWord_3211637
  simp only [CollatzResearch.WordTrace]
  refine ⟨117138024665795127776081165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78092016443863418517387443 117138024665795127776081165)
  ·
    refine ⟨43926759249673172916030437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117138024665795127776081165 43926759249673172916030437)
    ·
      refine ⟨8236267359313719921755707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43926759249673172916030437 8236267359313719921755707)
      ·
        refine ⟨12354401038970579882633561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8236267359313719921755707 12354401038970579882633561)
        ·
          refine ⟨9265800779227934911975171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12354401038970579882633561 9265800779227934911975171)
          ·
            refine ⟨13898701168841902367962757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9265800779227934911975171 13898701168841902367962757)
            ·
              refine ⟨2606006469157856693993017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13898701168841902367962757 2606006469157856693993017)
              ·
                refine ⟨1954504851868392520494763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606006469157856693993017 1954504851868392520494763)
                ·
                  refine ⟨2931757277802588780742145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954504851868392520494763 2931757277802588780742145)
                  ·
                    refine ⟨2198817958351941585556609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2931757277802588780742145 2198817958351941585556609)
                    ·
                      refine ⟨1649113468763956189167457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198817958351941585556609 1649113468763956189167457)
                      ·
                        rfl

theorem cell23_3211637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_3211637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211637 prefixEnd_3211637 := by exact prefixLift 3211637
  have htrace : WordTrace (prefixWord ++ tailWord_3211637) baseStart_3211637 baseEnd_3211637 := by
    simpa [prefixWord, tailWord_3211637, baseEnd_3211637] using wordTrace_append hprefix tailTrace_3211637
  have hstable : (prefixWord ++ tailWord_3211637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211637).length < 2 ^ (prefixWord ++ tailWord_3211637).sum := by decide
  have hdescent : baseEnd_3211637 < baseStart_3211637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211680 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 1, 3, 2]
def baseStart_3211680 : Nat := 118140960795 + 3211680 * 2 ^ 59
def prefixEnd_3211680 : Nat := 4983230072969 + 3 ^ 40 * 3211680 * 2
def baseEnd_3211680 : Nat := 1649135548432099520929759

theorem tailTrace_3211680 : CollatzResearch.WordTrace tailWord_3211680 prefixEnd_3211680 1649135548432099520929759 := by
  unfold tailWord_3211680
  simp only [CollatzResearch.WordTrace]
  refine ⟨58569796502319673059948247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78093062003092897413264329 58569796502319673059948247)
  ·
    refine ⟨87854694753479509589922371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58569796502319673059948247 87854694753479509589922371)
    ·
      refine ⟨131782042130219264384883557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87854694753479509589922371 131782042130219264384883557)
      ·
        refine ⟨24709132899416112072165667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131782042130219264384883557 24709132899416112072165667)
        ·
          refine ⟨37063699349124168108248501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24709132899416112072165667 37063699349124168108248501)
          ·
            refine ⟨3474721813980390760148297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37063699349124168108248501 3474721813980390760148297)
            ·
              refine ⟨2606041360485293070111223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3474721813980390760148297 2606041360485293070111223)
              ·
                refine ⟨3909062040727939605166835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606041360485293070111223 3909062040727939605166835)
                ·
                  refine ⟨5863593061091909407750253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909062040727939605166835 5863593061091909407750253)
                  ·
                    refine ⟨2198847397909466027906345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5863593061091909407750253 2198847397909466027906345)
                    ·
                      refine ⟨1649135548432099520929759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198847397909466027906345 1649135548432099520929759)
                      ·
                        rfl

theorem cell23_3211680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_3211680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211680 prefixEnd_3211680 := by exact prefixLift 3211680
  have htrace : WordTrace (prefixWord ++ tailWord_3211680) baseStart_3211680 baseEnd_3211680 := by
    simpa [prefixWord, tailWord_3211680, baseEnd_3211680] using wordTrace_append hprefix tailTrace_3211680
  have hstable : (prefixWord ++ tailWord_3211680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211680).length < 2 ^ (prefixWord ++ tailWord_3211680).sum := by decide
  have hdescent : baseEnd_3211680 < baseStart_3211680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211733 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 5]
def baseStart_3211733 : Nat := 118140960795 + 3211733 * 2 ^ 59
def prefixEnd_3211733 : Nat := 4983230072969 + 3 ^ 40 * 3211733 * 2
def baseEnd_3211733 : Nat := 183240306989643090396335

theorem tailTrace_3211733 : CollatzResearch.WordTrace tailWord_3211733 prefixEnd_3211733 183240306989643090396335 := by
  unfold tailWord_3211733
  simp only [CollatzResearch.WordTrace]
  refine ⟨117141526073447336171575853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78094350715631557447717235 117141526073447336171575853)
  ·
    refine ⟨43928072277542751064340945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117141526073447336171575853 43928072277542751064340945)
    ·
      refine ⟨32946054208157063298255709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43928072277542751064340945 32946054208157063298255709)
      ·
        refine ⟨12354770328058898736845891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32946054208157063298255709 12354770328058898736845891)
        ·
          refine ⟨18532155492088348105268837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12354770328058898736845891 18532155492088348105268837)
          ·
            refine ⟨3474779154766565269737907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18532155492088348105268837 3474779154766565269737907)
            ·
              refine ⟨5212168732149847904606861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474779154766565269737907 5212168732149847904606861)
              ·
                refine ⟨1954563274556192964227573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5212168732149847904606861 1954563274556192964227573)
                ·
                  refine ⟨183240306989643090396335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954563274556192964227573 183240306989643090396335)
                  ·
                    rfl

theorem cell23_3211733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_3211733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211733 prefixEnd_3211733 := by exact prefixLift 3211733
  have htrace : WordTrace (prefixWord ++ tailWord_3211733) baseStart_3211733 baseEnd_3211733 := by
    simpa [prefixWord, tailWord_3211733, baseEnd_3211733] using wordTrace_append hprefix tailTrace_3211733
  have hstable : (prefixWord ++ tailWord_3211733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211733).length < 2 ^ (prefixWord ++ tailWord_3211733).sum := by decide
  have hdescent : baseEnd_3211733 < baseStart_3211733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211766 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3211766 : Nat := 118140960795 + 3211766 * 2 ^ 59
def prefixEnd_3211766 : Nat := 4983230072969 + 3 ^ 40 * 3211766 * 2
def baseEnd_3211766 : Nat := 1649179707768386184454363

theorem tailTrace_3211766 : CollatzResearch.WordTrace tailWord_3211766 prefixEnd_3211766 1649179707768386184454363 := by
  unfold tailWord_3211766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321420605145486425470447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78095153121551855205018101 7321420605145486425470447)
  ·
    refine ⟨10982130907718229638205671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321420605145486425470447 10982130907718229638205671)
    ·
      refine ⟨16473196361577344457308507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10982130907718229638205671 16473196361577344457308507)
      ·
        refine ⟨24709794542366016685962761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473196361577344457308507 24709794542366016685962761)
        ·
          refine ⟨18532345906774512514472071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24709794542366016685962761 18532345906774512514472071)
          ·
            refine ⟨27798518860161768771708107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18532345906774512514472071 27798518860161768771708107)
            ·
              refine ⟨41697778290242653157562161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27798518860161768771708107 41697778290242653157562161)
              ·
                refine ⟨31273333717681989868171621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41697778290242653157562161 31273333717681989868171621)
                ·
                  refine ⟨5863750072065373100282179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31273333717681989868171621 5863750072065373100282179)
                  ·
                    refine ⟨8795625108098059650423269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5863750072065373100282179 8795625108098059650423269)
                    ·
                      refine ⟨1649179707768386184454363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8795625108098059650423269 1649179707768386184454363)
                      ·
                        rfl

theorem cell23_3211766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3211766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211766 prefixEnd_3211766 := by exact prefixLift 3211766
  have htrace : WordTrace (prefixWord ++ tailWord_3211766) baseStart_3211766 baseEnd_3211766 := by
    simpa [prefixWord, tailWord_3211766, baseEnd_3211766] using wordTrace_append hprefix tailTrace_3211766
  have hstable : (prefixWord ++ tailWord_3211766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211766).length < 2 ^ (prefixWord ++ tailWord_3211766).sum := by decide
  have hdescent : baseEnd_3211766 < baseStart_3211766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211769 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3211769 : Nat := 118140960795 + 3211769 * 2 ^ 59
def prefixEnd_3211769 : Nat := 4983230072969 + 3 ^ 40 * 3211769 * 2
def baseEnd_3211769 : Nat := 1649181248210349672716849

theorem tailTrace_3211769 : CollatzResearch.WordTrace tailWord_3211769 prefixEnd_3211769 1649181248210349672716849 := by
  unfold tailWord_3211769
  simp only [CollatzResearch.WordTrace]
  refine ⟨117142839101316914319886361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78095226067544609546590907 117142839101316914319886361)
  ·
    refine ⟨87857129325987685739914771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117142839101316914319886361 87857129325987685739914771)
    ·
      refine ⟨131785693988981528609872157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87857129325987685739914771 131785693988981528609872157)
      ·
        refine ⟨49419635245868073228702059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131785693988981528609872157 49419635245868073228702059)
        ·
          refine ⟨74129452868802109843053089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49419635245868073228702059 74129452868802109843053089)
          ·
            refine ⟨55597089651601582382289817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74129452868802109843053089 55597089651601582382289817)
            ·
              refine ⟨41697817238701186786717363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55597089651601582382289817 41697817238701186786717363)
              ·
                refine ⟨62546725858051780180076045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41697817238701186786717363 62546725858051780180076045)
                ·
                  refine ⟨23455022196769417567528517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62546725858051780180076045 23455022196769417567528517)
                  ·
                    refine ⟨4397816661894265793911597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23455022196769417567528517 4397816661894265793911597)
                    ·
                      refine ⟨1649181248210349672716849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397816661894265793911597 1649181248210349672716849)
                      ·
                        rfl

theorem cell23_3211769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3211769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211769 prefixEnd_3211769 := by exact prefixLift 3211769
  have htrace : WordTrace (prefixWord ++ tailWord_3211769) baseStart_3211769 baseEnd_3211769 := by
    simpa [prefixWord, tailWord_3211769, baseEnd_3211769] using wordTrace_append hprefix tailTrace_3211769
  have hstable : (prefixWord ++ tailWord_3211769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211769).length < 2 ^ (prefixWord ++ tailWord_3211769).sum := by decide
  have hdescent : baseEnd_3211769 < baseStart_3211769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211783 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3211783 : Nat := 118140960795 + 3211783 * 2 ^ 59
def prefixEnd_3211783 : Nat := 4983230072969 + 3 ^ 40 * 3211783 * 2
def baseEnd_3211783 : Nat := 1649188436939512617941785

theorem tailTrace_3211783 : CollatzResearch.WordTrace tailWord_3211783 prefixEnd_3211783 1649188436939512617941785 := by
  unfold tailWord_3211783
  simp only [CollatzResearch.WordTrace]
  refine ⟨117143349723266194710896003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78095566482177463140597335 117143349723266194710896003)
  ·
    refine ⟨175715024584899292066344005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117143349723266194710896003 175715024584899292066344005)
    ·
      refine ⟨32946567109668617262439501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175715024584899292066344005 32946567109668617262439501)
      ·
        refine ⟨12354962666125731473414813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32946567109668617262439501 12354962666125731473414813)
        ·
          refine ⟨4633110999797149302530555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12354962666125731473414813 4633110999797149302530555)
          ·
            refine ⟨6949666499695723953795833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633110999797149302530555 6949666499695723953795833)
            ·
              refine ⟨5212249874771792965346875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949666499695723953795833 5212249874771792965346875)
              ·
                refine ⟨7818374812157689448020313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212249874771792965346875 7818374812157689448020313)
                ·
                  refine ⟨5863781109118267086015235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7818374812157689448020313 5863781109118267086015235)
                  ·
                    refine ⟨8795671663677400629022853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5863781109118267086015235 8795671663677400629022853)
                    ·
                      refine ⟨1649188436939512617941785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8795671663677400629022853 1649188436939512617941785)
                      ·
                        rfl

theorem cell23_3211783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3211783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211783 prefixEnd_3211783 := by exact prefixLift 3211783
  have htrace : WordTrace (prefixWord ++ tailWord_3211783) baseStart_3211783 baseEnd_3211783 := by
    simpa [prefixWord, tailWord_3211783, baseEnd_3211783] using wordTrace_append hprefix tailTrace_3211783
  have hstable : (prefixWord ++ tailWord_3211783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211783).length < 2 ^ (prefixWord ++ tailWord_3211783).sum := by decide
  have hdescent : baseEnd_3211783 < baseStart_3211783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211809 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3211809 : Nat := 118140960795 + 3211809 * 2 ^ 59
def prefixEnd_3211809 : Nat := 4983230072969 + 3 ^ 40 * 3211809 * 2
def baseEnd_3211809 : Nat := 1649201787436529516216665

theorem tailTrace_3211809 : CollatzResearch.WordTrace tailWord_3211809 prefixEnd_3211809 1649201787436529516216665 := by
  unfold tailWord_3211809
  simp only [CollatzResearch.WordTrace]
  refine ⟨117144298021172001151342481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78096198680781334100894987 117144298021172001151342481)
  ·
    refine ⟨87858223515879000863506861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117144298021172001151342481 87858223515879000863506861)
    ·
      refine ⟨32946833818454625323815073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87858223515879000863506861 32946833818454625323815073)
      ·
        refine ⟨24710125363840968992861305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32946833818454625323815073 24710125363840968992861305)
        ·
          refine ⟨18532594022880726744645979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24710125363840968992861305 18532594022880726744645979)
          ·
            refine ⟨27798891034321090116968969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18532594022880726744645979 27798891034321090116968969)
            ·
              refine ⟨20849168275740817587726727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27798891034321090116968969 20849168275740817587726727)
              ·
                refine ⟨31273752413611226381590091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20849168275740817587726727 31273752413611226381590091)
                ·
                  refine ⟨46910628620416839572385137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31273752413611226381590091 46910628620416839572385137)
                  ·
                    refine ⟨35182971465312629679288853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46910628620416839572385137 35182971465312629679288853)
                    ·
                      refine ⟨1649201787436529516216665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35182971465312629679288853 1649201787436529516216665)
                      ·
                        rfl

theorem cell23_3211809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3211809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211809 prefixEnd_3211809 := by exact prefixLift 3211809
  have htrace : WordTrace (prefixWord ++ tailWord_3211809) baseStart_3211809 baseEnd_3211809 := by
    simpa [prefixWord, tailWord_3211809, baseEnd_3211809] using wordTrace_append hprefix tailTrace_3211809
  have hstable : (prefixWord ++ tailWord_3211809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211809).length < 2 ^ (prefixWord ++ tailWord_3211809).sum := by decide
  have hdescent : baseEnd_3211809 < baseStart_3211809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211829 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3211829 : Nat := 118140960795 + 3211829 * 2 ^ 59
def prefixEnd_3211829 : Nat := 4983230072969 + 3 ^ 40 * 3211829 * 2
def baseEnd_3211829 : Nat := 1649212057049619437966573

theorem tailTrace_3211829 : CollatzResearch.WordTrace tailWord_3211829 prefixEnd_3211829 1649212057049619437966573 := by
  unfold tailWord_3211829
  simp only [CollatzResearch.WordTrace]
  refine ⟨117145027481099544567070541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78096684987399696378047027 117145027481099544567070541)
  ·
    refine ⟨43929385305412329212651453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117145027481099544567070541 43929385305412329212651453)
    ·
      refine ⟨16473519489529623454744295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43929385305412329212651453 16473519489529623454744295)
      ·
        refine ⟨24710279234294435182116443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473519489529623454744295 24710279234294435182116443)
        ·
          refine ⟨37065418851441652773174665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24710279234294435182116443 37065418851441652773174665)
          ·
            refine ⟨27799064138581239579880999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37065418851441652773174665 27799064138581239579880999)
            ·
              refine ⟨41698596207871859369821499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27799064138581239579880999 41698596207871859369821499)
              ·
                refine ⟨62547894311807789054732249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41698596207871859369821499 62547894311807789054732249)
                ·
                  refine ⟨46910920733855841791049187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62547894311807789054732249 46910920733855841791049187)
                  ·
                    refine ⟨70366381100783762686573781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46910920733855841791049187 70366381100783762686573781)
                    ·
                      refine ⟨1649212057049619437966573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70366381100783762686573781 1649212057049619437966573)
                      ·
                        rfl

theorem cell23_3211829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3211829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211829 prefixEnd_3211829 := by exact prefixLift 3211829
  have htrace : WordTrace (prefixWord ++ tailWord_3211829) baseStart_3211829 baseEnd_3211829 := by
    simpa [prefixWord, tailWord_3211829, baseEnd_3211829] using wordTrace_append hprefix tailTrace_3211829
  have hstable : (prefixWord ++ tailWord_3211829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211829).length < 2 ^ (prefixWord ++ tailWord_3211829).sum := by decide
  have hdescent : baseEnd_3211829 < baseStart_3211829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211833 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3211833 : Nat := 118140960795 + 3211833 * 2 ^ 59
def prefixEnd_3211833 : Nat := 4983230072969 + 3 ^ 40 * 3211833 * 2
def baseEnd_3211833 : Nat := 1649214110972237422316555

theorem tailTrace_3211833 : CollatzResearch.WordTrace tailWord_3211833 prefixEnd_3211833 1649214110972237422316555 := by
  unfold tailWord_3211833
  simp only [CollatzResearch.WordTrace]
  refine ⟨117145173373085053250216153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78096782248723368833477435 117145173373085053250216153)
  ·
    refine ⟨87858880029813789937662115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117145173373085053250216153 87858880029813789937662115)
    ·
      refine ⟨131788320044720684906493173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87858880029813789937662115 131788320044720684906493173)
      ·
        refine ⟨12355155004192564209983735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131788320044720684906493173 12355155004192564209983735)
        ·
          refine ⟨18532732506288846314975603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12355155004192564209983735 18532732506288846314975603)
          ·
            refine ⟨27799098759433269472463405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18532732506288846314975603 27799098759433269472463405)
            ·
              refine ⟨10424662034787476052173777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27799098759433269472463405 10424662034787476052173777)
              ·
                refine ⟨7818496526090607039130333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10424662034787476052173777 7818496526090607039130333)
                ·
                  refine ⟨2931936197283977639673875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7818496526090607039130333 2931936197283977639673875)
                  ·
                    refine ⟨4397904295925966459510813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931936197283977639673875 4397904295925966459510813)
                    ·
                      refine ⟨1649214110972237422316555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397904295925966459510813 1649214110972237422316555)
                      ·
                        rfl

theorem cell23_3211833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3211833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211833 prefixEnd_3211833 := by exact prefixLift 3211833
  have htrace : WordTrace (prefixWord ++ tailWord_3211833) baseStart_3211833 baseEnd_3211833 := by
    simpa [prefixWord, tailWord_3211833, baseEnd_3211833] using wordTrace_append hprefix tailTrace_3211833
  have hstable : (prefixWord ++ tailWord_3211833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211833).length < 2 ^ (prefixWord ++ tailWord_3211833).sum := by decide
  have hdescent : baseEnd_3211833 < baseStart_3211833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211836 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_3211836 : Nat := 118140960795 + 3211836 * 2 ^ 59
def prefixEnd_3211836 : Nat := 4983230072969 + 3 ^ 40 * 3211836 * 2
def baseEnd_3211836 : Nat := 549738550471400303526347

theorem tailTrace_3211836 : CollatzResearch.WordTrace tailWord_3211836 prefixEnd_3211836 549738550471400303526347 := by
  unfold tailWord_3211836
  simp only [CollatzResearch.WordTrace]
  refine ⟨58572641396037092381287681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78096855194716123175050241 58572641396037092381287681)
  ·
    refine ⟨43929481047027819285965761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58572641396037092381287681 43929481047027819285965761)
    ·
      refine ⟨32947110785270864464474321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43929481047027819285965761 32947110785270864464474321)
      ·
        refine ⟨24710333088953148348355741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32947110785270864464474321 24710333088953148348355741)
        ·
          refine ⟨9266374908357430630633403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24710333088953148348355741 9266374908357430630633403)
          ·
            refine ⟨13899562362536145945950105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266374908357430630633403 13899562362536145945950105)
            ·
              refine ⟨10424671771902109459462579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13899562362536145945950105 10424671771902109459462579)
              ·
                refine ⟨15637007657853164189193869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10424671771902109459462579 15637007657853164189193869)
                ·
                  refine ⟨5863877871694936570947701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15637007657853164189193869 5863877871694936570947701)
                  ·
                    refine ⟨549738550471400303526347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5863877871694936570947701 549738550471400303526347)
                    ·
                      rfl

theorem cell23_3211836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_3211836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211836 prefixEnd_3211836 := by exact prefixLift 3211836
  have htrace : WordTrace (prefixWord ++ tailWord_3211836) baseStart_3211836 baseEnd_3211836 := by
    simpa [prefixWord, tailWord_3211836, baseEnd_3211836] using wordTrace_append hprefix tailTrace_3211836
  have hstable : (prefixWord ++ tailWord_3211836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211836).length < 2 ^ (prefixWord ++ tailWord_3211836).sum := by decide
  have hdescent : baseEnd_3211836 < baseStart_3211836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211850 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_3211850 : Nat := 118140960795 + 3211850 * 2 ^ 59
def prefixEnd_3211850 : Nat := 4983230072969 + 3 ^ 40 * 3211850 * 2
def baseEnd_3211850 : Nat := 1649222840143363855803977

theorem tailTrace_3211850 : CollatzResearch.WordTrace tailWord_3211850 prefixEnd_3211850 1649222840143363855803977 := by
  unfold tailWord_3211850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29286448353505866288396251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78097195609348976769056669 29286448353505866288396251)
  ·
    refine ⟨43929672530258799432594377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29286448353505866288396251 43929672530258799432594377)
    ·
      refine ⟨32947254397694099574445783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43929672530258799432594377 32947254397694099574445783)
      ·
        refine ⟨49420881596541149361668675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32947254397694099574445783 49420881596541149361668675)
        ·
          refine ⟨74131322394811724042503013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49420881596541149361668675 74131322394811724042503013)
          ·
            refine ⟨13899622949027198257969315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74131322394811724042503013 13899622949027198257969315)
            ·
              refine ⟨20849434423540797386953973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13899622949027198257969315 20849434423540797386953973)
              ·
                refine ⟨1954634477206949755026935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20849434423540797386953973 1954634477206949755026935)
                ·
                  refine ⟨2931951715810424632540403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954634477206949755026935 2931951715810424632540403)
                  ·
                    refine ⟨4397927573715636948810605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931951715810424632540403 4397927573715636948810605)
                    ·
                      refine ⟨1649222840143363855803977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4397927573715636948810605 1649222840143363855803977)
                      ·
                        rfl

theorem cell23_3211850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_3211850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211850 prefixEnd_3211850 := by exact prefixLift 3211850
  have htrace : WordTrace (prefixWord ++ tailWord_3211850) baseStart_3211850 baseEnd_3211850 := by
    simpa [prefixWord, tailWord_3211850, baseEnd_3211850] using wordTrace_append hprefix tailTrace_3211850
  have hstable : (prefixWord ++ tailWord_3211850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211850).length < 2 ^ (prefixWord ++ tailWord_3211850).sum := by decide
  have hdescent : baseEnd_3211850 < baseStart_3211850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211876 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_3211876 : Nat := 118140960795 + 3211876 * 2 ^ 59
def prefixEnd_3211876 : Nat := 4983230072969 + 3 ^ 40 * 3211876 * 2
def baseEnd_3211876 : Nat := 1649236190640380754078857

theorem tailTrace_3211876 : CollatzResearch.WordTrace tailWord_3211876 prefixEnd_3211876 1649236190640380754078857 := by
  unfold tailWord_3211876
  simp only [CollatzResearch.WordTrace]
  refine ⟨58573370855964635797015741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78097827807952847729354321 58573370855964635797015741)
  ·
    refine ⟨21965014070986738423880903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58573370855964635797015741 21965014070986738423880903)
    ·
      refine ⟨32947521106480107635821355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21965014070986738423880903 32947521106480107635821355)
      ·
        refine ⟨49421281659720161453732033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32947521106480107635821355 49421281659720161453732033)
        ·
          refine ⟨37065961244790121090299025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49421281659720161453732033 37065961244790121090299025)
          ·
            refine ⟨27799470933592590817724269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37065961244790121090299025 27799470933592590817724269)
            ·
              refine ⟨10424801600097221556646601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27799470933592590817724269 10424801600097221556646601)
              ·
                refine ⟨7818601200072916167484951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10424801600097221556646601 7818601200072916167484951)
                ·
                  refine ⟨11727901800109374251227427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7818601200072916167484951 11727901800109374251227427)
                  ·
                    refine ⟨17591852700164061376841141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11727901800109374251227427 17591852700164061376841141)
                    ·
                      refine ⟨1649236190640380754078857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17591852700164061376841141 1649236190640380754078857)
                      ·
                        rfl

theorem cell23_3211876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_3211876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211876 prefixEnd_3211876 := by exact prefixLift 3211876
  have htrace : WordTrace (prefixWord ++ tailWord_3211876) baseStart_3211876 baseEnd_3211876 := by
    simpa [prefixWord, tailWord_3211876, baseEnd_3211876] using wordTrace_append hprefix tailTrace_3211876
  have hstable : (prefixWord ++ tailWord_3211876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211876).length < 2 ^ (prefixWord ++ tailWord_3211876).sum := by decide
  have hdescent : baseEnd_3211876 < baseStart_3211876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211879 : List Nat := [1, 1, 5, 1, 1, 1, 1, 12]
def baseStart_3211879 : Nat := 118140960795 + 3211879 * 2 ^ 59
def prefixEnd_3211879 : Nat := 4983230072969 + 3 ^ 40 * 3211879 * 2
def baseEnd_3211879 : Nat := 61082878928975712679309

theorem tailTrace_3211879 : CollatzResearch.WordTrace tailWord_3211879 prefixEnd_3211879 61082878928975712679309 := by
  unfold tailWord_3211879
  simp only [CollatzResearch.WordTrace]
  refine ⟨117146851130918403106390691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78097900753945602070927127 117146851130918403106390691)
  ·
    refine ⟨175720276696377604659586037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117146851130918403106390691 175720276696377604659586037)
    ·
      refine ⟨16473775940285400436836191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175720276696377604659586037 16473775940285400436836191)
      ·
        refine ⟨24710663910428100655254287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473775940285400436836191 24710663910428100655254287)
        ·
          refine ⟨37065995865642150982881431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24710663910428100655254287 37065995865642150982881431)
          ·
            refine ⟨55598993798463226474322147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37065995865642150982881431 55598993798463226474322147)
            ·
              refine ⟨83398490697694839711483221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55598993798463226474322147 83398490697694839711483221)
              ·
                refine ⟨61082878928975712679309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 83398490697694839711483221 61082878928975712679309)
                ·
                  rfl

theorem cell23_3211879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 12].length) (baseStart_3211879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211879 prefixEnd_3211879 := by exact prefixLift 3211879
  have htrace : WordTrace (prefixWord ++ tailWord_3211879) baseStart_3211879 baseEnd_3211879 := by
    simpa [prefixWord, tailWord_3211879, baseEnd_3211879] using wordTrace_append hprefix tailTrace_3211879
  have hstable : (prefixWord ++ tailWord_3211879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211879).length < 2 ^ (prefixWord ++ tailWord_3211879).sum := by decide
  have hdescent : baseEnd_3211879 < baseStart_3211879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211890 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3211890 : Nat := 118140960795 + 3211890 * 2 ^ 59
def prefixEnd_3211890 : Nat := 4983230072969 + 3 ^ 40 * 3211890 * 2
def baseEnd_3211890 : Nat := 1649243379369543699303793

theorem tailTrace_3211890 : CollatzResearch.WordTrace tailWord_3211890 prefixEnd_3211890 1649243379369543699303793 := by
  unfold tailWord_3211890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29286813083469637996260281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78098168222585701323360749 29286813083469637996260281)
  ·
    refine ⟨21965109812602228497195211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29286813083469637996260281 21965109812602228497195211)
    ·
      refine ⟨32947664718903342745792817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21965109812602228497195211 32947664718903342745792817)
      ·
        refine ⟨24710748539177507059344613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32947664718903342745792817 24710748539177507059344613)
        ·
          refine ⟨4633265351095782573627115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24710748539177507059344613 4633265351095782573627115)
          ·
            refine ⟨6949898026643673860440673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633265351095782573627115 6949898026643673860440673)
            ·
              refine ⟨5212423519982755395330505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949898026643673860440673 5212423519982755395330505)
              ·
                refine ⟨3909317639987066546497879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5212423519982755395330505 3909317639987066546497879)
                ·
                  refine ⟨5863976459980599819746819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909317639987066546497879 5863976459980599819746819)
                  ·
                    refine ⟨8795964689970899729620229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5863976459980599819746819 8795964689970899729620229)
                    ·
                      refine ⟨1649243379369543699303793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8795964689970899729620229 1649243379369543699303793)
                      ·
                        rfl

theorem cell23_3211890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3211890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211890 prefixEnd_3211890 := by exact prefixLift 3211890
  have htrace : WordTrace (prefixWord ++ tailWord_3211890) baseStart_3211890 baseEnd_3211890 := by
    simpa [prefixWord, tailWord_3211890, baseEnd_3211890] using wordTrace_append hprefix tailTrace_3211890
  have hstable : (prefixWord ++ tailWord_3211890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211890).length < 2 ^ (prefixWord ++ tailWord_3211890).sum := by decide
  have hdescent : baseEnd_3211890 < baseStart_3211890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211907 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 1, 2, 2]
def baseStart_3211907 : Nat := 118140960795 + 3211907 * 2 ^ 59
def prefixEnd_3211907 : Nat := 4983230072969 + 3 ^ 40 * 3211907 * 2
def baseEnd_3211907 : Nat := 1649252108540670132791215

theorem tailTrace_3211907 : CollatzResearch.WordTrace tailWord_3211907 prefixEnd_3211907 1649252108540670132791215 := by
  unfold tailWord_3211907
  simp only [CollatzResearch.WordTrace]
  refine ⟨117147872374816963888409975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78098581583211309258939983 117147872374816963888409975)
  ·
    refine ⟨175721808562225445832614963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117147872374816963888409975 175721808562225445832614963)
    ·
      refine ⟨263582712843338168748922445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175721808562225445832614963 263582712843338168748922445)
      ·
        refine ⟨98843517316251813280845917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263582712843338168748922445 98843517316251813280845917)
        ·
          refine ⟨37066318993594429980317219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98843517316251813280845917 37066318993594429980317219)
          ·
            refine ⟨55599478490391644970475829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37066318993594429980317219 55599478490391644970475829)
            ·
              refine ⟨5212451108474216715982109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55599478490391644970475829 5212451108474216715982109)
              ·
                refine ⟨1954669165677831268493291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5212451108474216715982109 1954669165677831268493291)
                ·
                  refine ⟨2932003748516746902739937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954669165677831268493291 2932003748516746902739937)
                  ·
                    refine ⟨2199002811387560177054953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2932003748516746902739937 2199002811387560177054953)
                    ·
                      refine ⟨1649252108540670132791215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199002811387560177054953 1649252108540670132791215)
                      ·
                        rfl

theorem cell23_3211907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_3211907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211907 prefixEnd_3211907 := by exact prefixLift 3211907
  have htrace : WordTrace (prefixWord ++ tailWord_3211907) baseStart_3211907 baseEnd_3211907 := by
    simpa [prefixWord, tailWord_3211907, baseEnd_3211907] using wordTrace_append hprefix tailTrace_3211907
  have hstable : (prefixWord ++ tailWord_3211907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211907).length < 2 ^ (prefixWord ++ tailWord_3211907).sum := by decide
  have hdescent : baseEnd_3211907 < baseStart_3211907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211924 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3211924 : Nat := 118140960795 + 3211924 * 2 ^ 59
def prefixEnd_3211924 : Nat := 4983230072969 + 3 ^ 40 * 3211924 * 2
def baseEnd_3211924 : Nat := 1649260837711796566278637

theorem tailTrace_3211924 : CollatzResearch.WordTrace tailWord_3211924 prefixEnd_3211924 1649260837711796566278637 := by
  unfold tailWord_3211924
  simp only [CollatzResearch.WordTrace]
  refine ⟨58574246207877687895889413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78098994943836917194519217 58574246207877687895889413)
  ·
    refine ⟨10982671163977066480479265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58574246207877687895889413 10982671163977066480479265)
    ·
      refine ⟨8237003372982799860359449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10982671163977066480479265 8237003372982799860359449)
      ·
        refine ⟨6177752529737099895269587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8237003372982799860359449 6177752529737099895269587)
        ·
          refine ⟨9266628794605649842904381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177752529737099895269587 9266628794605649842904381)
          ·
            refine ⟨3474985797977118691089143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9266628794605649842904381 3474985797977118691089143)
            ·
              refine ⟨5212478696965678036633715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474985797977118691089143 5212478696965678036633715)
              ·
                refine ⟨7818718045448517054950573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212478696965678036633715 7818718045448517054950573)
                ·
                  refine ⟨2932019267043193895606465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7818718045448517054950573 2932019267043193895606465)
                  ·
                    refine ⟨2199014450282395421704849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2932019267043193895606465 2199014450282395421704849)
                    ·
                      refine ⟨1649260837711796566278637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199014450282395421704849 1649260837711796566278637)
                      ·
                        rfl

theorem cell23_3211924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3211924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211924 prefixEnd_3211924 := by exact prefixLift 3211924
  have htrace : WordTrace (prefixWord ++ tailWord_3211924) baseStart_3211924 baseEnd_3211924 := by
    simpa [prefixWord, tailWord_3211924, baseEnd_3211924] using wordTrace_append hprefix tailTrace_3211924
  have hstable : (prefixWord ++ tailWord_3211924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211924).length < 2 ^ (prefixWord ++ tailWord_3211924).sum := by decide
  have hdescent : baseEnd_3211924 < baseStart_3211924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211940 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_3211940 : Nat := 118140960795 + 3211940 * 2 ^ 59
def prefixEnd_3211940 : Nat := 4983230072969 + 3 ^ 40 * 3211940 * 2
def baseEnd_3211940 : Nat := 1649269053402268503678563

theorem tailTrace_3211940 : CollatzResearch.WordTrace tailWord_3211940 prefixEnd_3211940 1649269053402268503678563 := by
  unfold tailWord_3211940
  simp only [CollatzResearch.WordTrace]
  refine ⟨58574537991848705262180637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78099383989131607016240849 58574537991848705262180637)
  ·
    refine ⟨21965451746943264473317739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58574537991848705262180637 21965451746943264473317739)
    ·
      refine ⟨32948177620414896709976609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21965451746943264473317739 32948177620414896709976609)
      ·
        refine ⟨24711133215311172532482457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32948177620414896709976609 24711133215311172532482457)
        ·
          refine ⟨18533349911483379399361843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24711133215311172532482457 18533349911483379399361843)
          ·
            refine ⟨27800024867225069099042765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18533349911483379399361843 27800024867225069099042765)
            ·
              refine ⟨10425009325209400912141037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27800024867225069099042765 10425009325209400912141037)
              ·
                refine ⟨3909378496953525342052889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10425009325209400912141037 3909378496953525342052889)
                ·
                  refine ⟨2932033872715144006539667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3909378496953525342052889 2932033872715144006539667)
                  ·
                    refine ⟨4398050809072716009809501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2932033872715144006539667 4398050809072716009809501)
                    ·
                      refine ⟨1649269053402268503678563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4398050809072716009809501 1649269053402268503678563)
                      ·
                        rfl

theorem cell23_3211940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_3211940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211940 prefixEnd_3211940 := by exact prefixLift 3211940
  have htrace : WordTrace (prefixWord ++ tailWord_3211940) baseStart_3211940 baseEnd_3211940 := by
    simpa [prefixWord, tailWord_3211940, baseEnd_3211940] using wordTrace_append hprefix tailTrace_3211940
  have hstable : (prefixWord ++ tailWord_3211940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211940).length < 2 ^ (prefixWord ++ tailWord_3211940).sum := by decide
  have hdescent : baseEnd_3211940 < baseStart_3211940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211967 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 1, 3, 2]
def baseStart_3211967 : Nat := 118140960795 + 3211967 * 2 ^ 59
def prefixEnd_3211967 : Nat := 4983230072969 + 3 ^ 40 * 3211967 * 2
def baseEnd_3211967 : Nat := 1649282917379939898040939

theorem tailTrace_3211967 : CollatzResearch.WordTrace tailWord_3211967 prefixEnd_3211967 1649282917379939898040939 := by
  unfold tailWord_3211967
  simp only [CollatzResearch.WordTrace]
  refine ⟨117150060754599594135594155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78100040503066396090396103 117150060754599594135594155)
  ·
    refine ⟨175725091131899391203391233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117150060754599594135594155 175725091131899391203391233)
    ·
      refine ⟨131793818348924543402543425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175725091131899391203391233 131793818348924543402543425)
      ·
        refine ⟨98845363761693407551907569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131793818348924543402543425 98845363761693407551907569)
        ·
          refine ⟨74134022821270055663930677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98845363761693407551907569 74134022821270055663930677)
          ·
            refine ⟨6950064639494067718493501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74134022821270055663930677 6950064639494067718493501)
            ·
              refine ⟨2606274239810275394435063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6950064639494067718493501 2606274239810275394435063)
              ·
                refine ⟨3909411359715413091652595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606274239810275394435063 3909411359715413091652595)
                ·
                  refine ⟨5864117039573119637478893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909411359715413091652595 5864117039573119637478893)
                  ·
                    refine ⟨2199043889839919864054585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5864117039573119637478893 2199043889839919864054585)
                    ·
                      refine ⟨1649282917379939898040939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199043889839919864054585 1649282917379939898040939)
                      ·
                        rfl

theorem cell23_3211967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_3211967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211967 prefixEnd_3211967 := by exact prefixLift 3211967
  have htrace : WordTrace (prefixWord ++ tailWord_3211967) baseStart_3211967 baseEnd_3211967 := by
    simpa [prefixWord, tailWord_3211967, baseEnd_3211967] using wordTrace_append hprefix tailTrace_3211967
  have hstable : (prefixWord ++ tailWord_3211967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211967).length < 2 ^ (prefixWord ++ tailWord_3211967).sum := by decide
  have hdescent : baseEnd_3211967 < baseStart_3211967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212003 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 7]
def baseStart_3212003 : Nat := 118140960795 + 3212003 * 2 ^ 59
def prefixEnd_3212003 : Nat := 4983230072969 + 3 ^ 40 * 3212003 * 2
def baseEnd_3212003 : Nat := 183255711409277973021197

theorem tailTrace_3212003 : CollatzResearch.WordTrace tailWord_3212003 prefixEnd_3212003 183255711409277973021197 := by
  unfold tailWord_3212003
  simp only [CollatzResearch.WordTrace]
  refine ⟨117151373782469172283904663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78100915854979448189269775 117151373782469172283904663)
  ·
    refine ⟨175727060673703758425856995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117151373782469172283904663 175727060673703758425856995)
    ·
      refine ⟨263590591010555637638785493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175727060673703758425856995 263590591010555637638785493)
      ·
        refine ⟨6177904476809897757159035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 263590591010555637638785493 6177904476809897757159035)
        ·
          refine ⟨9266856715214846635738553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177904476809897757159035 9266856715214846635738553)
          ·
            refine ⟨6950142536411134976803915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9266856715214846635738553 6950142536411134976803915)
            ·
              refine ⟨10425213804616702465205873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950142536411134976803915 10425213804616702465205873)
              ·
                refine ⟨7818910353462526848904405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10425213804616702465205873 7818910353462526848904405)
                ·
                  refine ⟨183255711409277973021197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7818910353462526848904405 183255711409277973021197)
                  ·
                    rfl

theorem cell23_3212003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 7].length) (baseStart_3212003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212003 prefixEnd_3212003 := by exact prefixLift 3212003
  have htrace : WordTrace (prefixWord ++ tailWord_3212003) baseStart_3212003 baseEnd_3212003 := by
    simpa [prefixWord, tailWord_3212003, baseEnd_3212003] using wordTrace_append hprefix tailTrace_3212003
  have hstable : (prefixWord ++ tailWord_3212003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212003).length < 2 ^ (prefixWord ++ tailWord_3212003).sum := by decide
  have hdescent : baseEnd_3212003 < baseStart_3212003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212013 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3212013 : Nat := 118140960795 + 3212013 * 2 ^ 59
def prefixEnd_3212013 : Nat := 4983230072969 + 3 ^ 40 * 3212013 * 2
def baseEnd_3212013 : Nat := 1649306537490046718065727

theorem tailTrace_3212013 : CollatzResearch.WordTrace tailWord_3212013 prefixEnd_3212013 1649306537490046718065727 := by
  unfold tailWord_3212013
  simp only [CollatzResearch.WordTrace]
  refine ⟨117151738512432943991768693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78101159008288629327845795 117151738512432943991768693)
  ·
    refine ⟨10982975485540588499228315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117151738512432943991768693 10982975485540588499228315)
    ·
      refine ⟨16474463228310882748842473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10982975485540588499228315 16474463228310882748842473)
      ·
        refine ⟨12355847421233162061631855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16474463228310882748842473 12355847421233162061631855)
        ·
          refine ⟨18533771131849743092447783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12355847421233162061631855 18533771131849743092447783)
          ·
            refine ⟨27800656697774614638671675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18533771131849743092447783 27800656697774614638671675)
            ·
              refine ⟨41700985046661921958007513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27800656697774614638671675 41700985046661921958007513)
              ·
                refine ⟨31275738784996441468505635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41700985046661921958007513 31275738784996441468505635)
                ·
                  refine ⟨46913608177494662202758453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31275738784996441468505635 46913608177494662202758453)
                  ·
                    refine ⟨4398150766640124581508605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46913608177494662202758453 4398150766640124581508605)
                    ·
                      refine ⟨1649306537490046718065727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4398150766640124581508605 1649306537490046718065727)
                      ·
                        rfl

theorem cell23_3212013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3212013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212013 prefixEnd_3212013 := by exact prefixLift 3212013
  have htrace : WordTrace (prefixWord ++ tailWord_3212013) baseStart_3212013 baseEnd_3212013 := by
    simpa [prefixWord, tailWord_3212013, baseEnd_3212013] using wordTrace_append hprefix tailTrace_3212013
  have hstable : (prefixWord ++ tailWord_3212013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212013).length < 2 ^ (prefixWord ++ tailWord_3212013).sum := by decide
  have hdescent : baseEnd_3212013 < baseStart_3212013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212016 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_3212016 : Nat := 118140960795 + 3212016 * 2 ^ 59
def prefixEnd_3212016 : Nat := 4983230072969 + 3 ^ 40 * 3212016 * 2
def baseEnd_3212016 : Nat := 549769359310670068776071

theorem tailTrace_3212016 : CollatzResearch.WordTrace tailWord_3212016 prefixEnd_3212016 549769359310670068776071 := by
  unfold tailWord_3212016
  simp only [CollatzResearch.WordTrace]
  refine ⟨58575923965711037752063951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78101231954281383669418601 58575923965711037752063951)
  ·
    refine ⟨87863885948566556628095927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58575923965711037752063951 87863885948566556628095927)
    ·
      refine ⟨131795828922849834942143891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87863885948566556628095927 131795828922849834942143891)
      ·
        refine ⟨197693743384274752413215837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131795828922849834942143891 197693743384274752413215837)
        ·
          refine ⟨74135153769103032154955939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197693743384274752413215837 74135153769103032154955939)
          ·
            refine ⟨111202730653654548232433909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74135153769103032154955939 111202730653654548232433909)
            ·
              refine ⟨10425255998780113896790679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111202730653654548232433909 10425255998780113896790679)
              ·
                refine ⟨15637883998170170845186019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10425255998780113896790679 15637883998170170845186019)
                ·
                  refine ⟨23456825997255256267779029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15637883998170170845186019 23456825997255256267779029)
                  ·
                    refine ⟨549769359310670068776071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23456825997255256267779029 549769359310670068776071)
                    ·
                      rfl

theorem cell23_3212016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_3212016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212016 prefixEnd_3212016 := by exact prefixLift 3212016
  have htrace : WordTrace (prefixWord ++ tailWord_3212016) baseStart_3212016 baseEnd_3212016 := by
    simpa [prefixWord, tailWord_3212016, baseEnd_3212016] using wordTrace_append hprefix tailTrace_3212016
  have hstable : (prefixWord ++ tailWord_3212016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212016).length < 2 ^ (prefixWord ++ tailWord_3212016).sum := by decide
  have hdescent : baseEnd_3212016 < baseStart_3212016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212026 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_3212026 : Nat := 118140960795 + 3212026 * 2 ^ 59
def prefixEnd_3212026 : Nat := 4983230072969 + 3 ^ 40 * 3212026 * 2
def baseEnd_3212026 : Nat := 1649313212738555167203167

theorem tailTrace_3212026 : CollatzResearch.WordTrace tailWord_3212026 prefixEnd_3212026 1649313212738555167203167 := by
  unfold tailWord_3212026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29288053165346461802997983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78101475107590564807994621 29288053165346461802997983)
  ·
    refine ⟨43932079748019692704496975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29288053165346461802997983 43932079748019692704496975)
    ·
      refine ⟨65898119622029539056745463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43932079748019692704496975 65898119622029539056745463)
      ·
        refine ⟨98847179433044308585118195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65898119622029539056745463 98847179433044308585118195)
        ·
          refine ⟨148270769149566462877677293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98847179433044308585118195 148270769149566462877677293)
          ·
            refine ⟨55601538431087423579128985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148270769149566462877677293 55601538431087423579128985)
            ·
              refine ⟨41701153823315567684346739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55601538431087423579128985 41701153823315567684346739)
              ·
                refine ⟨62551730734973351526520109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41701153823315567684346739 62551730734973351526520109)
                ·
                  refine ⟨23456899025615006822445041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62551730734973351526520109 23456899025615006822445041)
                  ·
                    refine ⟨17592674269211255116833781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23456899025615006822445041 17592674269211255116833781)
                    ·
                      refine ⟨1649313212738555167203167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17592674269211255116833781 1649313212738555167203167)
                      ·
                        rfl

theorem cell23_3212026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_3212026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212026 prefixEnd_3212026 := by exact prefixLift 3212026
  have htrace : WordTrace (prefixWord ++ tailWord_3212026) baseStart_3212026 baseEnd_3212026 := by
    simpa [prefixWord, tailWord_3212026, baseEnd_3212026] using wordTrace_append hprefix tailTrace_3212026
  have hstable : (prefixWord ++ tailWord_3212026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212026).length < 2 ^ (prefixWord ++ tailWord_3212026).sum := by decide
  have hdescent : baseEnd_3212026 < baseStart_3212026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212030 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3212030 : Nat := 118140960795 + 3212030 * 2 ^ 59
def prefixEnd_3212030 : Nat := 4983230072969 + 3 ^ 40 * 3212030 * 2
def baseEnd_3212030 : Nat := 1649315266661173151553149

theorem tailTrace_3212030 : CollatzResearch.WordTrace tailWord_3212030 prefixEnd_3212030 1649315266661173151553149 := by
  unfold tailWord_3212030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14644044819171419486892193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78101572368914237263425029 14644044819171419486892193)
  ·
    refine ⟨10983033614378564615169145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14644044819171419486892193 10983033614378564615169145)
    ·
      refine ⟨8237275210783923461376859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10983033614378564615169145 8237275210783923461376859)
      ·
        refine ⟨12355912816175885192065289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8237275210783923461376859 12355912816175885192065289)
        ·
          refine ⟨9266934612131913894048967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12355912816175885192065289 9266934612131913894048967)
          ·
            refine ⟨13900401918197870841073451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266934612131913894048967 13900401918197870841073451)
            ·
              refine ⟨20850602877296806261610177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13900401918197870841073451 20850602877296806261610177)
              ·
                refine ⟨15637952157972604696207633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20850602877296806261610177 15637952157972604696207633)
                ·
                  refine ⟨11728464118479453522155725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15637952157972604696207633 11728464118479453522155725)
                  ·
                    refine ⟨4398174044429795070808397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11728464118479453522155725 4398174044429795070808397)
                    ·
                      refine ⟨1649315266661173151553149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4398174044429795070808397 1649315266661173151553149)
                      ·
                        rfl

theorem cell23_3212030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3212030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212030 prefixEnd_3212030 := by exact prefixLift 3212030
  have htrace : WordTrace (prefixWord ++ tailWord_3212030) baseStart_3212030 baseEnd_3212030 := by
    simpa [prefixWord, tailWord_3212030, baseEnd_3212030] using wordTrace_append hprefix tailTrace_3212030
  have hstable : (prefixWord ++ tailWord_3212030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212030).length < 2 ^ (prefixWord ++ tailWord_3212030).sum := by decide
  have hdescent : baseEnd_3212030 < baseStart_3212030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212076 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 10]
def baseStart_3212076 : Nat := 118140960795 + 3212076 * 2 ^ 59
def prefixEnd_3212076 : Nat := 4983230072969 + 3 ^ 40 * 3212076 * 2
def baseEnd_3212076 : Nat := 183259876307919996841993

theorem tailTrace_3212076 : CollatzResearch.WordTrace tailWord_3212076 prefixEnd_3212076 183259876307919996841993 := by
  unfold tailWord_3212076
  simp only [CollatzResearch.WordTrace]
  refine ⟨58577018155602352875656041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78102690874136470500874721 58577018155602352875656041)
  ·
    refine ⟨43932763616701764656742031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58577018155602352875656041 43932763616701764656742031)
    ·
      refine ⟨65899145425052646985113047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43932763616701764656742031 65899145425052646985113047)
      ·
        refine ⟨98848718137578970477669571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65899145425052646985113047 98848718137578970477669571)
        ·
          refine ⟨148273077206368455716504357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98848718137578970477669571 148273077206368455716504357)
          ·
            refine ⟨27801201976194085446844567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148273077206368455716504357 27801201976194085446844567)
            ·
              refine ⟨41701802964291128170266851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27801201976194085446844567 41701802964291128170266851)
              ·
                refine ⟨62552704446436692255400277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41701802964291128170266851 62552704446436692255400277)
                ·
                  refine ⟨183259876307919996841993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 62552704446436692255400277 183259876307919996841993)
                  ·
                    rfl

theorem cell23_3212076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_3212076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212076 prefixEnd_3212076 := by exact prefixLift 3212076
  have htrace : WordTrace (prefixWord ++ tailWord_3212076) baseStart_3212076 baseEnd_3212076 := by
    simpa [prefixWord, tailWord_3212076, baseEnd_3212076] using wordTrace_append hprefix tailTrace_3212076
  have hstable : (prefixWord ++ tailWord_3212076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212076).length < 2 ^ (prefixWord ++ tailWord_3212076).sum := by decide
  have hdescent : baseEnd_3212076 < baseStart_3212076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212096 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_3212096 : Nat := 118140960795 + 3212096 * 2 ^ 59
def prefixEnd_3212096 : Nat := 4983230072969 + 3 ^ 40 * 3212096 * 2
def baseEnd_3212096 : Nat := 1649349156384369893327845

theorem tailTrace_3212096 : CollatzResearch.WordTrace tailWord_3212096 prefixEnd_3212096 1649349156384369893327845 := by
  unfold tailWord_3212096
  simp only [CollatzResearch.WordTrace]
  refine ⟨58577382885566124583520071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78103177180754832778026761 58577382885566124583520071)
  ·
    refine ⟨87866074328349186875280107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58577382885566124583520071 87866074328349186875280107)
    ·
      refine ⟨131799111492523780312920161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87866074328349186875280107 131799111492523780312920161)
      ·
        refine ⟨98849333619392835234690121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131799111492523780312920161 98849333619392835234690121)
        ·
          refine ⟨74137000214544626426017591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98849333619392835234690121 74137000214544626426017591)
          ·
            refine ⟨111205500321816939639026387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74137000214544626426017591 111205500321816939639026387)
            ·
              refine ⟨166808250482725409458539581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111205500321816939639026387 166808250482725409458539581)
              ·
                refine ⟨62553093931022028546952343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166808250482725409458539581 62553093931022028546952343)
                ·
                  refine ⟨93829640896533042820428515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62553093931022028546952343 93829640896533042820428515)
                  ·
                    refine ⟨140744461344799564230642773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93829640896533042820428515 140744461344799564230642773)
                    ·
                      refine ⟨1649349156384369893327845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 140744461344799564230642773 1649349156384369893327845)
                      ·
                        rfl

theorem cell23_3212096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_3212096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212096 prefixEnd_3212096 := by exact prefixLift 3212096
  have htrace : WordTrace (prefixWord ++ tailWord_3212096) baseStart_3212096 baseEnd_3212096 := by
    simpa [prefixWord, tailWord_3212096, baseEnd_3212096] using wordTrace_append hprefix tailTrace_3212096
  have hstable : (prefixWord ++ tailWord_3212096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212096).length < 2 ^ (prefixWord ++ tailWord_3212096).sum := by decide
  have hdescent : baseEnd_3212096 < baseStart_3212096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212120 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3212120 : Nat := 118140960795 + 3212120 * 2 ^ 59
def prefixEnd_3212120 : Nat := 4983230072969 + 3 ^ 40 * 3212120 * 2
def baseEnd_3212120 : Nat := 1649361479920077799427735

theorem tailTrace_3212120 : CollatzResearch.WordTrace tailWord_3212120 prefixEnd_3212120 1649361479920077799427735 := by
  unfold tailWord_3212120
  simp only [CollatzResearch.WordTrace]
  refine ⟨58577820561522650632956907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78103760748696867510609209 58577820561522650632956907)
  ·
    refine ⟨87866730842283975949435361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58577820561522650632956907 87866730842283975949435361)
    ·
      refine ⟨65900048131712981962076521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87866730842283975949435361 65900048131712981962076521)
      ·
        refine ⟨49425036098784736471557391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65900048131712981962076521 49425036098784736471557391)
        ·
          refine ⟨74137554148177104707336087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49425036098784736471557391 74137554148177104707336087)
          ·
            refine ⟨111206331222265657061004131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74137554148177104707336087 111206331222265657061004131)
            ·
              refine ⟨166809496833398485591506197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111206331222265657061004131 166809496833398485591506197)
              ·
                refine ⟨7819195164065554012101853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166809496833398485591506197 7819195164065554012101853)
                ·
                  refine ⟨2932198186524582754538195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7819195164065554012101853 2932198186524582754538195)
                  ·
                    refine ⟨4398297279786874131807293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2932198186524582754538195 4398297279786874131807293)
                    ·
                      refine ⟨1649361479920077799427735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4398297279786874131807293 1649361479920077799427735)
                      ·
                        rfl

theorem cell23_3212120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3212120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212120 prefixEnd_3212120 := by exact prefixLift 3212120
  have htrace : WordTrace (prefixWord ++ tailWord_3212120) baseStart_3212120 baseEnd_3212120 := by
    simpa [prefixWord, tailWord_3212120, baseEnd_3212120] using wordTrace_append hprefix tailTrace_3212120
  have hstable : (prefixWord ++ tailWord_3212120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212120).length < 2 ^ (prefixWord ++ tailWord_3212120).sum := by decide
  have hdescent : baseEnd_3212120 < baseStart_3212120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212163 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5]
def baseStart_3212163 : Nat := 118140960795 + 3212163 * 2 ^ 59
def prefixEnd_3212163 : Nat := 4983230072969 + 3 ^ 40 * 3212163 * 2
def baseEnd_3212163 : Nat := 1649383559588221131190037

theorem tailTrace_3212163 : CollatzResearch.WordTrace tailWord_3212163 prefixEnd_3212163 1649383559588221131190037 := by
  unfold tailWord_3212163
  simp only [CollatzResearch.WordTrace]
  refine ⟨117157209461889519609729143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78104806307926346406486095 117157209461889519609729143)
  ·
    refine ⟨175735814192834279414593715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117157209461889519609729143 175735814192834279414593715)
    ·
      refine ⟨263603721289251419121890573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175735814192834279414593715 263603721289251419121890573)
      ·
        refine ⟨98851395483469282170708965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263603721289251419121890573 98851395483469282170708965)
        ·
          refine ⟨18534636653150490407007931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98851395483469282170708965 18534636653150490407007931)
          ·
            refine ⟨27801954979725735610511897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18534636653150490407007931 27801954979725735610511897)
            ·
              refine ⟨20851466234794301707883923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27801954979725735610511897 20851466234794301707883923)
              ·
                refine ⟨31277199352191452561825885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20851466234794301707883923 31277199352191452561825885)
                ·
                  refine ⟨11728949757071794710684707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31277199352191452561825885 11728949757071794710684707)
                  ·
                    refine ⟨17593424635607692066027061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11728949757071794710684707 17593424635607692066027061)
                    ·
                      refine ⟨1649383559588221131190037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17593424635607692066027061 1649383559588221131190037)
                      ·
                        rfl

theorem cell23_3212163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_3212163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212163 prefixEnd_3212163 := by exact prefixLift 3212163
  have htrace : WordTrace (prefixWord ++ tailWord_3212163) baseStart_3212163 baseEnd_3212163 := by
    simpa [prefixWord, tailWord_3212163, baseEnd_3212163] using wordTrace_append hprefix tailTrace_3212163
  have hstable : (prefixWord ++ tailWord_3212163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212163).length < 2 ^ (prefixWord ++ tailWord_3212163).sum := by decide
  have hdescent : baseEnd_3212163 < baseStart_3212163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212170 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3212170 : Nat := 118140960795 + 3212170 * 2 ^ 59
def prefixEnd_3212170 : Nat := 4983230072969 + 3 ^ 40 * 3212170 * 2
def baseEnd_3212170 : Nat := 549795717984267534600835

theorem tailTrace_3212170 : CollatzResearch.WordTrace tailWord_3212170 prefixEnd_3212170 549795717984267534600835 := by
  unfold tailWord_3212170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29289366193216039951308491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78104976515242773203489309 29289366193216039951308491)
  ·
    refine ⟨43934049289824059926962737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29289366193216039951308491 43934049289824059926962737)
    ·
      refine ⟨32950536967368044945222053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43934049289824059926962737 32950536967368044945222053)
      ·
        refine ⟨6178225681381508427229135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32950536967368044945222053 6178225681381508427229135)
        ·
          refine ⟨9267338522072262640843703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178225681381508427229135 9267338522072262640843703)
          ·
            refine ⟨13901007783108393961265555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9267338522072262640843703 13901007783108393961265555)
            ·
              refine ⟨20851511674662590941898333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13901007783108393961265555 20851511674662590941898333)
              ·
                refine ⟨7819316877998471603211875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20851511674662590941898333 7819316877998471603211875)
                ·
                  refine ⟨11728975316997707404817813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7819316877998471603211875 11728975316997707404817813)
                  ·
                    refine ⟨549795717984267534600835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11728975316997707404817813 549795717984267534600835)
                    ·
                      rfl

theorem cell23_3212170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3212170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212170 prefixEnd_3212170 := by exact prefixLift 3212170
  have htrace : WordTrace (prefixWord ++ tailWord_3212170) baseStart_3212170 baseEnd_3212170 := by
    simpa [prefixWord, tailWord_3212170, baseEnd_3212170] using wordTrace_append hprefix tailTrace_3212170
  have hstable : (prefixWord ++ tailWord_3212170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212170).length < 2 ^ (prefixWord ++ tailWord_3212170).sum := by decide
  have hdescent : baseEnd_3212170 < baseStart_3212170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212194 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_3212194 : Nat := 118140960795 + 3212194 * 2 ^ 59
def prefixEnd_3212194 : Nat := 4983230072969 + 3 ^ 40 * 3212194 * 2
def baseEnd_3212194 : Nat := 1649399477488510509902395

theorem tailTrace_3212194 : CollatzResearch.WordTrace tailWord_3212194 prefixEnd_3212194 1649399477488510509902395 := by
  unfold tailWord_3212194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29289585031194302976026909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78105560083184807936071757 29289585031194302976026909)
  ·
    refine ⟨10983594386697863616010091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29289585031194302976026909 10983594386697863616010091)
    ·
      refine ⟨16475391580046795424015137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10983594386697863616010091 16475391580046795424015137)
      ·
        refine ⟨12356543685035096568011353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16475391580046795424015137 12356543685035096568011353)
        ·
          refine ⟨9267407763776322426008515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12356543685035096568011353 9267407763776322426008515)
          ·
            refine ⟨13901111645664483639012773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9267407763776322426008515 13901111645664483639012773)
            ·
              refine ⟨2606458433562090682314895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13901111645664483639012773 2606458433562090682314895)
              ·
                refine ⟨3909687650343136023472343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606458433562090682314895 3909687650343136023472343)
                ·
                  refine ⟨5864531475514704035208515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909687650343136023472343 5864531475514704035208515)
                  ·
                    refine ⟨8796797213272056052812773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5864531475514704035208515 8796797213272056052812773)
                    ·
                      refine ⟨1649399477488510509902395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8796797213272056052812773 1649399477488510509902395)
                      ·
                        rfl

theorem cell23_3212194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_3212194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212194 prefixEnd_3212194 := by exact prefixLift 3212194
  have htrace : WordTrace (prefixWord ++ tailWord_3212194) baseStart_3212194 baseEnd_3212194 := by
    simpa [prefixWord, tailWord_3212194, baseEnd_3212194] using wordTrace_append hprefix tailTrace_3212194
  have hstable : (prefixWord ++ tailWord_3212194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212194).length < 2 ^ (prefixWord ++ tailWord_3212194).sum := by decide
  have hdescent : baseEnd_3212194 < baseStart_3212194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212245 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3212245 : Nat := 118140960795 + 3212245 * 2 ^ 59
def prefixEnd_3212245 : Nat := 4983230072969 + 3 ^ 40 * 3212245 * 2
def baseEnd_3212245 : Nat := 1649425665001889810364661

theorem tailTrace_3212245 : CollatzResearch.WordTrace tailWord_3212245 prefixEnd_3212245 1649425665001889810364661 := by
  unfold tailWord_3212245
  simp only [CollatzResearch.WordTrace]
  refine ⟨117160200247592447614214189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78106800165061631742809459 117160200247592447614214189)
  ·
    refine ⟨43935075092847167855330321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117160200247592447614214189 43935075092847167855330321)
    ·
      refine ⟨32951306319635375891497741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43935075092847167855330321 32951306319635375891497741)
      ·
        refine ⟨12356739869863265959311653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32951306319635375891497741 12356739869863265959311653)
        ·
          refine ⟨2316888725599362367370935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12356739869863265959311653 2316888725599362367370935)
          ·
            refine ⟨3475333088399043551056403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316888725599362367370935 3475333088399043551056403)
            ·
              refine ⟨5212999632598565326584605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475333088399043551056403 5212999632598565326584605)
              ·
                refine ⟨1954874862224461997469227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5212999632598565326584605 1954874862224461997469227)
                ·
                  refine ⟨2932312293336692996203841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954874862224461997469227 2932312293336692996203841)
                  ·
                    refine ⟨2199234220002519747152881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2932312293336692996203841 2199234220002519747152881)
                    ·
                      refine ⟨1649425665001889810364661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199234220002519747152881 1649425665001889810364661)
                      ·
                        rfl

theorem cell23_3212245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3212245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212245 prefixEnd_3212245 := by exact prefixLift 3212245
  have htrace : WordTrace (prefixWord ++ tailWord_3212245) baseStart_3212245 baseEnd_3212245 := by
    simpa [prefixWord, tailWord_3212245, baseEnd_3212245] using wordTrace_append hprefix tailTrace_3212245
  have hstable : (prefixWord ++ tailWord_3212245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212245).length < 2 ^ (prefixWord ++ tailWord_3212245).sum := by decide
  have hdescent : baseEnd_3212245 < baseStart_3212245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212278 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_3212278 : Nat := 118140960795 + 3212278 * 2 ^ 59
def prefixEnd_3212278 : Nat := 4983230072969 + 3 ^ 40 * 3212278 * 2
def baseEnd_3212278 : Nat := 1649442609863488181252009

theorem tailTrace_3212278 : CollatzResearch.WordTrace tailWord_3212278 prefixEnd_3212278 1649442609863488181252009 := by
  unfold tailWord_3212278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322587741029555890635343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78107602570981929500110325 7322587741029555890635343)
  ·
    refine ⟨10983881611544333835953015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7322587741029555890635343 10983881611544333835953015)
    ·
      refine ⟨16475822417316500753929523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10983881611544333835953015 16475822417316500753929523)
      ·
        refine ⟨24713733625974751130894285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16475822417316500753929523 24713733625974751130894285)
        ·
          refine ⟨9267650109740531674085357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24713733625974751130894285 9267650109740531674085357)
          ·
            refine ⟨3475368791152699377782009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9267650109740531674085357 3475368791152699377782009)
            ·
              refine ⟨2606526593364524533336507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475368791152699377782009 2606526593364524533336507)
              ·
                refine ⟨3909789890046786800004761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606526593364524533336507 3909789890046786800004761)
                ·
                  refine ⟨2932342417535090100003571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3909789890046786800004761 2932342417535090100003571)
                  ·
                    refine ⟨4398513626302635150005357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2932342417535090100003571 4398513626302635150005357)
                    ·
                      refine ⟨1649442609863488181252009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4398513626302635150005357 1649442609863488181252009)
                      ·
                        rfl

theorem cell23_3212278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_3212278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212278 prefixEnd_3212278 := by exact prefixLift 3212278
  have htrace : WordTrace (prefixWord ++ tailWord_3212278) baseStart_3212278 baseEnd_3212278 := by
    simpa [prefixWord, tailWord_3212278, baseEnd_3212278] using wordTrace_append hprefix tailTrace_3212278
  have hstable : (prefixWord ++ tailWord_3212278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212278).length < 2 ^ (prefixWord ++ tailWord_3212278).sum := by decide
  have hdescent : baseEnd_3212278 < baseStart_3212278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212324 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 5]
def baseStart_3212324 : Nat := 118140960795 + 3212324 * 2 ^ 59
def prefixEnd_3212324 : Nat := 4983230072969 + 3 ^ 40 * 3212324 * 2
def baseEnd_3212324 : Nat := 183274025552621666808533

theorem tailTrace_3212324 : CollatzResearch.WordTrace tailWord_3212324 prefixEnd_3212324 183274025552621666808533 := by
  unfold tailWord_3212324
  simp only [CollatzResearch.WordTrace]
  refine ⟨58581540807153122053170013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78108721076204162737560017 58581540807153122053170013)
  ·
    refine ⟨21968077802682420769938755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58581540807153122053170013 21968077802682420769938755)
    ·
      refine ⟨32952116704023631154908133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21968077802682420769938755 32952116704023631154908133)
      ·
        refine ⟨6178521882004430841545275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32952116704023631154908133 6178521882004430841545275)
        ·
          refine ⟨9267782823006646262317913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178521882004430841545275 9267782823006646262317913)
          ·
            refine ⟨6950837117254984696738435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9267782823006646262317913 6950837117254984696738435)
            ·
              refine ⟨10426255675882477045107653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950837117254984696738435 10426255675882477045107653)
              ·
                refine ⟨1954922939227964445957685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10426255675882477045107653 1954922939227964445957685)
                ·
                  refine ⟨183274025552621666808533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954922939227964445957685 183274025552621666808533)
                  ·
                    rfl

theorem cell23_3212324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_3212324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212324 prefixEnd_3212324 := by exact prefixLift 3212324
  have htrace : WordTrace (prefixWord ++ tailWord_3212324) baseStart_3212324 baseEnd_3212324 := by
    simpa [prefixWord, tailWord_3212324, baseEnd_3212324] using wordTrace_append hprefix tailTrace_3212324
  have hstable : (prefixWord ++ tailWord_3212324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212324).length < 2 ^ (prefixWord ++ tailWord_3212324).sum := by decide
  have hdescent : baseEnd_3212324 < baseStart_3212324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212357 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_3212357 : Nat := 118140960795 + 3212357 * 2 ^ 59
def prefixEnd_3212357 : Nat := 4983230072969 + 3 ^ 40 * 3212357 * 2
def baseEnd_3212357 : Nat := 1649483174835193372164145

theorem tailTrace_3212357 : CollatzResearch.WordTrace tailWord_3212357 prefixEnd_3212357 1649483174835193372164145 := by
  unfold tailWord_3212357
  simp only [CollatzResearch.WordTrace]
  refine ⟨117164285223186690742291325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78109523482124460494860883 117164285223186690742291325)
  ·
    refine ⟨43936606958695009028359247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117164285223186690742291325 43936606958695009028359247)
    ·
      refine ⟨65904910438042513542538871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43936606958695009028359247 65904910438042513542538871)
      ·
        refine ⟨98857365657063770313808307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65904910438042513542538871 98857365657063770313808307)
        ·
          refine ⟨148286048485595655470712461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98857365657063770313808307 148286048485595655470712461)
          ·
            refine ⟨55607268182098370801517173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148286048485595655470712461 55607268182098370801517173)
            ·
              refine ⟨5213181392071722262642235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55607268182098370801517173 5213181392071722262642235)
              ·
                refine ⟨7819772088107583393963353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213181392071722262642235 7819772088107583393963353)
                ·
                  refine ⟨5864829066080687545472515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7819772088107583393963353 5864829066080687545472515)
                  ·
                    refine ⟨8797243599121031318208773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5864829066080687545472515 8797243599121031318208773)
                    ·
                      refine ⟨1649483174835193372164145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8797243599121031318208773 1649483174835193372164145)
                      ·
                        rfl

theorem cell23_3212357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_3212357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212357 prefixEnd_3212357 := by exact prefixLift 3212357
  have htrace : WordTrace (prefixWord ++ tailWord_3212357) baseStart_3212357 baseEnd_3212357 := by
    simpa [prefixWord, tailWord_3212357, baseEnd_3212357] using wordTrace_append hprefix tailTrace_3212357
  have hstable : (prefixWord ++ tailWord_3212357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212357).length < 2 ^ (prefixWord ++ tailWord_3212357).sum := by decide
  have hdescent : baseEnd_3212357 < baseStart_3212357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212384 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 1, 4]
def baseStart_3212384 : Nat := 118140960795 + 3212384 * 2 ^ 59
def prefixEnd_3212384 : Nat := 4983230072969 + 3 ^ 40 * 3212384 * 2
def baseEnd_3212384 : Nat := 549832346270954922175507

theorem tailTrace_3212384 : CollatzResearch.WordTrace tailWord_3212384 prefixEnd_3212384 549832346270954922175507 := by
  unfold tailWord_3212384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58582634997044437176762103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78110179996059249569016137 58582634997044437176762103)
  ·
    refine ⟨87873952495566655765143155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58582634997044437176762103 87873952495566655765143155)
    ·
      refine ⟨131810928743349983647714733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87873952495566655765143155 131810928743349983647714733)
      ·
        refine ⟨49429098278756243867893025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131810928743349983647714733 49429098278756243867893025)
        ·
          refine ⟨37071823709067182900919769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49429098278756243867893025 37071823709067182900919769)
          ·
            refine ⟨27803867781800387175689827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37071823709067182900919769 27803867781800387175689827)
            ·
              refine ⟨41705801672700580763534741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27803867781800387175689827 41705801672700580763534741)
              ·
                refine ⟨1954959453407839723290691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41705801672700580763534741 1954959453407839723290691)
                ·
                  refine ⟨2932439180111759584936037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954959453407839723290691 2932439180111759584936037)
                  ·
                    refine ⟨549832346270954922175507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2932439180111759584936037 549832346270954922175507)
                    ·
                      rfl

theorem cell23_3212384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 4].length) (baseStart_3212384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212384 prefixEnd_3212384 := by exact prefixLift 3212384
  have htrace : WordTrace (prefixWord ++ tailWord_3212384) baseStart_3212384 baseEnd_3212384 := by
    simpa [prefixWord, tailWord_3212384, baseEnd_3212384] using wordTrace_append hprefix tailTrace_3212384
  have hstable : (prefixWord ++ tailWord_3212384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212384).length < 2 ^ (prefixWord ++ tailWord_3212384).sum := by decide
  have hdescent : baseEnd_3212384 < baseStart_3212384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212400 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_3212400 : Nat := 118140960795 + 3212400 * 2 ^ 59
def prefixEnd_3212400 : Nat := 4983230072969 + 3 ^ 40 * 3212400 * 2
def baseEnd_3212400 : Nat := 1649505254503336703926447

theorem tailTrace_3212400 : CollatzResearch.WordTrace tailWord_3212400 prefixEnd_3212400 1649505254503336703926447 := by
  unfold tailWord_3212400
  simp only [CollatzResearch.WordTrace]
  refine ⟨58582926781015454543053327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78110569041353939390737769 58582926781015454543053327)
  ·
    refine ⟨87874390171523181814579991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58582926781015454543053327 87874390171523181814579991)
    ·
      refine ⟨131811585257284772721869987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87874390171523181814579991 131811585257284772721869987)
      ·
        refine ⟨197717377885927159082804981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131811585257284772721869987 197717377885927159082804981)
        ·
          refine ⟨18536004176805671164012967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197717377885927159082804981 18536004176805671164012967)
          ·
            refine ⟨27804006265208506746019451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18536004176805671164012967 27804006265208506746019451)
            ·
              refine ⟨41706009397812760119029177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27804006265208506746019451 41706009397812760119029177)
              ·
                refine ⟨31279507048359570089271883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41706009397812760119029177 31279507048359570089271883)
                ·
                  refine ⟨46919260572539355133907825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31279507048359570089271883 46919260572539355133907825)
                  ·
                    refine ⟨35189445429404516350430869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46919260572539355133907825 35189445429404516350430869)
                    ·
                      refine ⟨1649505254503336703926447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35189445429404516350430869 1649505254503336703926447)
                      ·
                        rfl

theorem cell23_3212400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_3212400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212400 prefixEnd_3212400 := by exact prefixLift 3212400
  have htrace : WordTrace (prefixWord ++ tailWord_3212400) baseStart_3212400 baseEnd_3212400 := by
    simpa [prefixWord, tailWord_3212400, baseEnd_3212400] using wordTrace_append hprefix tailTrace_3212400
  have hstable : (prefixWord ++ tailWord_3212400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212400).length < 2 ^ (prefixWord ++ tailWord_3212400).sum := by decide
  have hdescent : baseEnd_3212400 < baseStart_3212400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212477 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3212477 : Nat := 118140960795 + 3212477 * 2 ^ 59
def prefixEnd_3212477 : Nat := 4983230072969 + 3 ^ 40 * 3212477 * 2
def baseEnd_3212477 : Nat := 1649544792513732902663593

theorem tailTrace_3212477 : CollatzResearch.WordTrace tailWord_3212477 prefixEnd_3212477 1649544792513732902663593 := by
  unfold tailWord_3212477
  simp only [CollatzResearch.WordTrace]
  refine ⟨117168661982751951236659685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78112441321834634157773123 117168661982751951236659685)
  ·
    refine ⟨21969124121765990856873691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117168661982751951236659685 21969124121765990856873691)
    ·
      refine ⟨32953686182648986285310537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21969124121765990856873691 32953686182648986285310537)
      ·
        refine ⟨24715264636986739713982903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32953686182648986285310537 24715264636986739713982903)
        ·
          refine ⟨37072896955480109570974355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24715264636986739713982903 37072896955480109570974355)
          ·
            refine ⟨55609345433220164356461533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37072896955480109570974355 55609345433220164356461533)
            ·
              refine ⟨20853504537457561633673075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55609345433220164356461533 20853504537457561633673075)
              ·
                refine ⟨31280256806186342450509613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20853504537457561633673075 31280256806186342450509613)
                ·
                  refine ⟨11730096302319878418941105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31280256806186342450509613 11730096302319878418941105)
                  ·
                    refine ⟨8797572226739908814205829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11730096302319878418941105 8797572226739908814205829)
                    ·
                      refine ⟨1649544792513732902663593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8797572226739908814205829 1649544792513732902663593)
                      ·
                        rfl

theorem cell23_3212477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3212477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212477 prefixEnd_3212477 := by exact prefixLift 3212477
  have htrace : WordTrace (prefixWord ++ tailWord_3212477) baseStart_3212477 baseEnd_3212477 := by
    simpa [prefixWord, tailWord_3212477, baseEnd_3212477] using wordTrace_append hprefix tailTrace_3212477
  have hstable : (prefixWord ++ tailWord_3212477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212477).length < 2 ^ (prefixWord ++ tailWord_3212477).sum := by decide
  have hdescent : baseEnd_3212477 < baseStart_3212477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212486 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3212486 : Nat := 118140960795 + 3212486 * 2 ^ 59
def prefixEnd_3212486 : Nat := 4983230072969 + 3 ^ 40 * 3212486 * 2
def baseEnd_3212486 : Nat := 549849804613207789150351

theorem tailTrace_3212486 : CollatzResearch.WordTrace tailWord_3212486 prefixEnd_3212486 549849804613207789150351 := by
  unfold tailWord_3212486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661530944991229555429291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78112660159812897182491541 3661530944991229555429291)
  ·
    refine ⟨5492296417486844333143937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661530944991229555429291 5492296417486844333143937)
    ·
      refine ⟨4119222313115133249857953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5492296417486844333143937 4119222313115133249857953)
      ·
        refine ⟨3089416734836349937393465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4119222313115133249857953 3089416734836349937393465)
        ·
          refine ⟨2317062551127262453045099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3089416734836349937393465 2317062551127262453045099)
          ·
            refine ⟨3475593826690893679567649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317062551127262453045099 3475593826690893679567649)
            ·
              refine ⟨2606695370018170259675737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475593826690893679567649 2606695370018170259675737)
              ·
                refine ⟨1955021527513627694756803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606695370018170259675737 1955021527513627694756803)
                ·
                  refine ⟨2932532291270441542135205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955021527513627694756803 2932532291270441542135205)
                  ·
                    refine ⟨549849804613207789150351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2932532291270441542135205 549849804613207789150351)
                    ·
                      rfl

theorem cell23_3212486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3212486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212486 prefixEnd_3212486 := by exact prefixLift 3212486
  have htrace : WordTrace (prefixWord ++ tailWord_3212486) baseStart_3212486 baseEnd_3212486 := by
    simpa [prefixWord, tailWord_3212486, baseEnd_3212486] using wordTrace_append hprefix tailTrace_3212486
  have hstable : (prefixWord ++ tailWord_3212486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212486).length < 2 ^ (prefixWord ++ tailWord_3212486).sum := by decide
  have hdescent : baseEnd_3212486 < baseStart_3212486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212497 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_3212497 : Nat := 118140960795 + 3212497 * 2 ^ 59
def prefixEnd_3212497 : Nat := 4983230072969 + 3 ^ 40 * 3212497 * 2
def baseEnd_3212497 : Nat := 1649555062126822824413501

theorem tailTrace_3212497 : CollatzResearch.WordTrace tailWord_3212497 prefixEnd_3212497 1649555062126822824413501 := by
  unfold tailWord_3212497
  simp only [CollatzResearch.WordTrace]
  refine ⟨117169391442679494652387745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78112927628452996434925163 117169391442679494652387745)
  ·
    refine ⟨87877043582009620989290809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117169391442679494652387745 87877043582009620989290809)
    ·
      refine ⟨65907782686507215741968107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87877043582009620989290809 65907782686507215741968107)
      ·
        refine ⟨98861674029760823612952161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65907782686507215741968107 98861674029760823612952161)
        ·
          refine ⟨74146255522320617709714121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98861674029760823612952161 74146255522320617709714121)
          ·
            refine ⟨55609691641740463282285591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74146255522320617709714121 55609691641740463282285591)
            ·
              refine ⟨83414537462610694923428387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55609691641740463282285591 83414537462610694923428387)
              ·
                refine ⟨125121806193916042385142581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83414537462610694923428387 125121806193916042385142581)
                ·
                  refine ⟨11730169330679628973607117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125121806193916042385142581 11730169330679628973607117)
                  ·
                    refine ⟨4398813499004860865102669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11730169330679628973607117 4398813499004860865102669)
                    ·
                      refine ⟨1649555062126822824413501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4398813499004860865102669 1649555062126822824413501)
                      ·
                        rfl

theorem cell23_3212497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_3212497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212497 prefixEnd_3212497 := by exact prefixLift 3212497
  have htrace : WordTrace (prefixWord ++ tailWord_3212497) baseStart_3212497 baseEnd_3212497 := by
    simpa [prefixWord, tailWord_3212497, baseEnd_3212497] using wordTrace_append hprefix tailTrace_3212497
  have hstable : (prefixWord ++ tailWord_3212497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212497).length < 2 ^ (prefixWord ++ tailWord_3212497).sum := by decide
  have hdescent : baseEnd_3212497 < baseStart_3212497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212504 : List Nat := [2, 1, 2, 2, 5, 2, 1, 8]
def baseStart_3212504 : Nat := 118140960795 + 3212504 * 2 ^ 59
def prefixEnd_3212504 : Nat := 4983230072969 + 3 ^ 40 * 3212504 * 2
def baseEnd_3212504 : Nat := 61094765055237196186147

theorem tailTrace_3212504 : CollatzResearch.WordTrace tailWord_3212504 prefixEnd_3212504 61094765055237196186147 := by
  unfold tailWord_3212504
  simp only [CollatzResearch.WordTrace]
  refine ⟨58584823376827067423946283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78113097835769423231928377 58584823376827067423946283)
  ·
    refine ⟨87877235065240601135919425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58584823376827067423946283 87877235065240601135919425)
    ·
      refine ⟨65907926298930450851939569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87877235065240601135919425 65907926298930450851939569)
      ·
        refine ⟨49430944724197838138954677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65907926298930450851939569 49430944724197838138954677)
        ·
          refine ⟨4634151067893547325527001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49430944724197838138954677 4634151067893547325527001)
          ·
            refine ⟨3475613300920160494145251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4634151067893547325527001 3475613300920160494145251)
            ·
              refine ⟨5213419951380240741217877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475613300920160494145251 5213419951380240741217877)
              ·
                refine ⟨61094765055237196186147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5213419951380240741217877 61094765055237196186147)
                ·
                  rfl

theorem cell23_3212504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 8].length) (baseStart_3212504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212504 prefixEnd_3212504 := by exact prefixLift 3212504
  have htrace : WordTrace (prefixWord ++ tailWord_3212504) baseStart_3212504 baseEnd_3212504 := by
    simpa [prefixWord, tailWord_3212504, baseEnd_3212504] using wordTrace_append hprefix tailTrace_3212504
  have hstable : (prefixWord ++ tailWord_3212504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212504).length < 2 ^ (prefixWord ++ tailWord_3212504).sum := by decide
  have hdescent : baseEnd_3212504 < baseStart_3212504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212547 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 2, 6]
def baseStart_3212547 : Nat := 118140960795 + 3212547 * 2 ^ 59
def prefixEnd_3212547 : Nat := 4983230072969 + 3 ^ 40 * 3212547 * 2
def baseEnd_3212547 : Nat := 549860245386515876262757

theorem tailTrace_3212547 : CollatzResearch.WordTrace tailWord_3212547 prefixEnd_3212547 549860245386515876262757 := by
  unfold tailWord_3212547
  simp only [CollatzResearch.WordTrace]
  refine ⟨117171215092498353191707895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78114143394998902127805263 117171215092498353191707895)
  ·
    refine ⟨175756822638747529787561843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117171215092498353191707895 175756822638747529787561843)
    ·
      refine ⟨263635233958121294681342765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175756822638747529787561843 263635233958121294681342765)
      ·
        refine ⟨98863212734295485505503537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263635233958121294681342765 98863212734295485505503537)
        ·
          refine ⟨74147409550721614129127653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98863212734295485505503537 74147409550721614129127653)
          ·
            refine ⟨13902639290760302649211435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74147409550721614129127653 13902639290760302649211435)
            ·
              refine ⟨20853958936140453973817153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902639290760302649211435 20853958936140453973817153)
              ·
                refine ⟨15640469202105340480362865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20853958936140453973817153 15640469202105340480362865)
                ·
                  refine ⟨11730351901579005360272149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15640469202105340480362865 11730351901579005360272149)
                  ·
                    refine ⟨549860245386515876262757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11730351901579005360272149 549860245386515876262757)
                    ·
                      rfl

theorem cell23_3212547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 6].length) (baseStart_3212547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212547 prefixEnd_3212547 := by exact prefixLift 3212547
  have htrace : WordTrace (prefixWord ++ tailWord_3212547) baseStart_3212547 baseEnd_3212547 := by
    simpa [prefixWord, tailWord_3212547, baseEnd_3212547] using wordTrace_append hprefix tailTrace_3212547
  have hstable : (prefixWord ++ tailWord_3212547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212547).length < 2 ^ (prefixWord ++ tailWord_3212547).sum := by decide
  have hdescent : baseEnd_3212547 < baseStart_3212547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212548 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3212548 : Nat := 118140960795 + 3212548 * 2 ^ 59
def prefixEnd_3212548 : Nat := 4983230072969 + 3 ^ 40 * 3212548 * 2
def baseEnd_3212548 : Nat := 1649581249640202124875767

theorem tailTrace_3212548 : CollatzResearch.WordTrace tailWord_3212548 prefixEnd_3212548 1649581249640202124875767 := by
  unfold tailWord_3212548
  simp only [CollatzResearch.WordTrace]
  refine ⟨58585625782747365181247149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78114167710329820241662865 58585625782747365181247149)
  ·
    refine ⟨21969609668530261942967681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58585625782747365181247149 21969609668530261942967681)
    ·
      refine ⟨16477207251397696457225761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21969609668530261942967681 16477207251397696457225761)
      ·
        refine ⟨12357905438548272342919321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16477207251397696457225761 12357905438548272342919321)
        ·
          refine ⟨9268429078911204257189491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12357905438548272342919321 9268429078911204257189491)
          ·
            refine ⟨13902643618366806385784237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268429078911204257189491 13902643618366806385784237)
            ·
              refine ⟨5213491356887552394669089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13902643618366806385784237 5213491356887552394669089)
              ·
                refine ⟨3910118517665664296001817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213491356887552394669089 3910118517665664296001817)
                ·
                  refine ⟨2932588888249248222001363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3910118517665664296001817 2932588888249248222001363)
                  ·
                    refine ⟨4398883332373872333002045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2932588888249248222001363 4398883332373872333002045)
                    ·
                      refine ⟨1649581249640202124875767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4398883332373872333002045 1649581249640202124875767)
                      ·
                        rfl

theorem cell23_3212548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3212548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212548 prefixEnd_3212548 := by exact prefixLift 3212548
  have htrace : WordTrace (prefixWord ++ tailWord_3212548) baseStart_3212548 baseEnd_3212548 := by
    simpa [prefixWord, tailWord_3212548, baseEnd_3212548] using wordTrace_append hprefix tailTrace_3212548
  have hstable : (prefixWord ++ tailWord_3212548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212548).length < 2 ^ (prefixWord ++ tailWord_3212548).sum := by decide
  have hdescent : baseEnd_3212548 < baseStart_3212548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212617 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_3212617 : Nat := 118140960795 + 3212617 * 2 ^ 59
def prefixEnd_3212617 : Nat := 4983230072969 + 3 ^ 40 * 3212617 * 2
def baseEnd_3212617 : Nat := 1649616679805362354912949

theorem tailTrace_3212617 : CollatzResearch.WordTrace tailWord_3212617 prefixEnd_3212617 1649616679805362354912949 := by
  unfold tailWord_3212617
  simp only [CollatzResearch.WordTrace]
  refine ⟨117173768202244755146756105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78115845468163170097837403 117173768202244755146756105)
  ·
    refine ⟨87880326151683566360067079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117173768202244755146756105 87880326151683566360067079)
    ·
      refine ⟨131820489227525349540100619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87880326151683566360067079 131820489227525349540100619)
      ·
        refine ⟨197730733841288024310150929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131820489227525349540100619 197730733841288024310150929)
        ·
          refine ⟨148298050380966018232613197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197730733841288024310150929 148298050380966018232613197)
          ·
            refine ⟨55611768892862256837229949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148298050380966018232613197 55611768892862256837229949)
            ·
              refine ⟨20854413334823346313961231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55611768892862256837229949 20854413334823346313961231)
              ·
                refine ⟨31281620002235019470941847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20854413334823346313961231 31281620002235019470941847)
                ·
                  refine ⟨46922430003352529206412771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31281620002235019470941847 46922430003352529206412771)
                  ·
                    refine ⟨70383645005028793809619157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46922430003352529206412771 70383645005028793809619157)
                    ·
                      refine ⟨1649616679805362354912949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70383645005028793809619157 1649616679805362354912949)
                      ·
                        rfl

theorem cell23_3212617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_3212617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212617 prefixEnd_3212617 := by exact prefixLift 3212617
  have htrace : WordTrace (prefixWord ++ tailWord_3212617) baseStart_3212617 baseEnd_3212617 := by
    simpa [prefixWord, tailWord_3212617, baseEnd_3212617] using wordTrace_append hprefix tailTrace_3212617
  have hstable : (prefixWord ++ tailWord_3212617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212617).length < 2 ^ (prefixWord ++ tailWord_3212617).sum := by decide
  have hdescent : baseEnd_3212617 < baseStart_3212617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212684 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 6]
def baseStart_3212684 : Nat := 118140960795 + 3212684 * 2 ^ 59
def prefixEnd_3212684 : Nat := 4983230072969 + 3 ^ 40 * 3212684 * 2
def baseEnd_3212684 : Nat := 183294564778801510308349

theorem tailTrace_3212684 : CollatzResearch.WordTrace tailWord_3212684 prefixEnd_3212684 183294564778801510308349 := by
  unfold tailWord_3212684
  simp only [CollatzResearch.WordTrace]
  refine ⟨58588105946501012794722553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78117474595334683726296737 58588105946501012794722553)
  ·
    refine ⟨43941079459875759596041915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58588105946501012794722553 43941079459875759596041915)
    ·
      refine ⟨65911619189813639394062873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43941079459875759596041915 65911619189813639394062873)
      ·
        refine ⟨49433714392360229545547155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65911619189813639394062873 49433714392360229545547155)
        ·
          refine ⟨74150571588540344318320733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49433714392360229545547155 74150571588540344318320733)
          ·
            refine ⟨27806464345702629119370275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74150571588540344318320733 27806464345702629119370275)
            ·
              refine ⟨41709696518553943679055413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27806464345702629119370275 41709696518553943679055413)
              ·
                refine ⟨3910284048614432219911445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41709696518553943679055413 3910284048614432219911445)
                ·
                  refine ⟨183294564778801510308349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3910284048614432219911445 183294564778801510308349)
                  ·
                    rfl

theorem cell23_3212684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_3212684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212684 prefixEnd_3212684 := by exact prefixLift 3212684
  have htrace : WordTrace (prefixWord ++ tailWord_3212684) baseStart_3212684 baseEnd_3212684 := by
    simpa [prefixWord, tailWord_3212684, baseEnd_3212684] using wordTrace_append hprefix tailTrace_3212684
  have hstable : (prefixWord ++ tailWord_3212684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212684).length < 2 ^ (prefixWord ++ tailWord_3212684).sum := by decide
  have hdescent : baseEnd_3212684 < baseStart_3212684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212748 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_3212748 : Nat := 118140960795 + 3212748 * 2 ^ 59
def prefixEnd_3212748 : Nat := 4983230072969 + 3 ^ 40 * 3212748 * 2
def baseEnd_3212748 : Nat := 549894648590367114124949

theorem tailTrace_3212748 : CollatzResearch.WordTrace tailWord_3212748 prefixEnd_3212748 549894648590367114124949 := by
  unfold tailWord_3212748
  simp only [CollatzResearch.WordTrace]
  refine ⟨58589273082385082259887449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78119030776513443013183265 58589273082385082259887449)
  ·
    refine ⟨43941954811788811694915587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58589273082385082259887449 43941954811788811694915587)
    ·
      refine ⟨65912932217683217542373381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43941954811788811694915587 65912932217683217542373381)
      ·
        refine ⟨12358674790815603289195009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65912932217683217542373381 12358674790815603289195009)
        ·
          refine ⟨9269006093111702466896257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12358674790815603289195009 9269006093111702466896257)
          ·
            refine ⟨6951754569833776850172193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269006093111702466896257 6951754569833776850172193)
            ·
              refine ⟨5213815927375332637629145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6951754569833776850172193 5213815927375332637629145)
              ·
                refine ⟨3910361945531499478221859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213815927375332637629145 3910361945531499478221859)
                ·
                  refine ⟨5865542918297249217332789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910361945531499478221859 5865542918297249217332789)
                  ·
                    refine ⟨549894648590367114124949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5865542918297249217332789 549894648590367114124949)
                    ·
                      rfl

theorem cell23_3212748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_3212748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212748 prefixEnd_3212748 := by exact prefixLift 3212748
  have htrace : WordTrace (prefixWord ++ tailWord_3212748) baseStart_3212748 baseEnd_3212748 := by
    simpa [prefixWord, tailWord_3212748, baseEnd_3212748] using wordTrace_append hprefix tailTrace_3212748
  have hstable : (prefixWord ++ tailWord_3212748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212748).length < 2 ^ (prefixWord ++ tailWord_3212748).sum := by decide
  have hdescent : baseEnd_3212748 < baseStart_3212748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212751 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 4]
def baseStart_3212751 : Nat := 118140960795 + 3212751 * 2 ^ 59
def prefixEnd_3212751 : Nat := 4983230072969 + 3 ^ 40 * 3212751 * 2
def baseEnd_3212751 : Nat := 1649685486213064830637333

theorem tailTrace_3212751 : CollatzResearch.WordTrace tailWord_3212751 prefixEnd_3212751 1649685486213064830637333 := by
  unfold tailWord_3212751
  simp only [CollatzResearch.WordTrace]
  refine ⟨117178655583759296032134107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78119103722506197354756071 117178655583759296032134107)
  ·
    refine ⟨175767983375638944048201161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117178655583759296032134107 175767983375638944048201161)
    ·
      refine ⟨131825987531729208036150871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175767983375638944048201161 131825987531729208036150871)
      ·
        refine ⟨197738981297593812054226307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131825987531729208036150871 197738981297593812054226307)
        ·
          refine ⟨296608471946390718081339461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197738981297593812054226307 296608471946390718081339461)
          ·
            refine ⟨55614088489948259640251149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296608471946390718081339461 55614088489948259640251149)
            ·
              refine ⟨20855283183730597365094181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55614088489948259640251149 20855283183730597365094181)
              ·
                refine ⟨3910365596949487005955159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20855283183730597365094181 3910365596949487005955159)
                ·
                  refine ⟨5865548395424230508932739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910365596949487005955159 5865548395424230508932739)
                  ·
                    refine ⟨8798322593136345763399109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865548395424230508932739 8798322593136345763399109)
                    ·
                      refine ⟨1649685486213064830637333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8798322593136345763399109 1649685486213064830637333)
                      ·
                        rfl

theorem cell23_3212751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_3212751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212751 prefixEnd_3212751 := by exact prefixLift 3212751
  have htrace : WordTrace (prefixWord ++ tailWord_3212751) baseStart_3212751 baseEnd_3212751 := by
    simpa [prefixWord, tailWord_3212751, baseEnd_3212751] using wordTrace_append hprefix tailTrace_3212751
  have hstable : (prefixWord ++ tailWord_3212751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212751).length < 2 ^ (prefixWord ++ tailWord_3212751).sum := by decide
  have hdescent : baseEnd_3212751 < baseStart_3212751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212761 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 4, 4]
def baseStart_3212761 : Nat := 118140960795 + 3212761 * 2 ^ 59
def prefixEnd_3212761 : Nat := 4983230072969 + 3 ^ 40 * 3212761 * 2
def baseEnd_3212761 : Nat := 549896873673203263837429

theorem tailTrace_3212761 : CollatzResearch.WordTrace tailWord_3212761 prefixEnd_3212761 549896873673203263837429 := by
  unfold tailWord_3212761
  simp only [CollatzResearch.WordTrace]
  refine ⟨117179020313723067739998137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78119346875815378493332091 117179020313723067739998137)
  ·
    refine ⟨87884265235292300804998603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117179020313723067739998137 87884265235292300804998603)
    ·
      refine ⟨131826397852938451207497905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87884265235292300804998603 131826397852938451207497905)
      ·
        refine ⟨98869798389703838405623429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131826397852938451207497905 98869798389703838405623429)
        ·
          refine ⟨18538087198069469701054393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98869798389703838405623429 18538087198069469701054393)
          ·
            refine ⟨13903565398552102275790795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18538087198069469701054393 13903565398552102275790795)
            ·
              refine ⟨20855348097828153413686193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13903565398552102275790795 20855348097828153413686193)
              ·
                refine ⟨15641511073371115060264645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20855348097828153413686193 15641511073371115060264645)
                ·
                  refine ⟨2932783326257084073799621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15641511073371115060264645 2932783326257084073799621)
                  ·
                    refine ⟨549896873673203263837429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2932783326257084073799621 549896873673203263837429)
                    ·
                      rfl

theorem cell23_3212761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_3212761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212761 prefixEnd_3212761 := by exact prefixLift 3212761
  have htrace : WordTrace (prefixWord ++ tailWord_3212761) baseStart_3212761 baseEnd_3212761 := by
    simpa [prefixWord, tailWord_3212761, baseEnd_3212761] using wordTrace_append hprefix tailTrace_3212761
  have hstable : (prefixWord ++ tailWord_3212761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212761).length < 2 ^ (prefixWord ++ tailWord_3212761).sum := by decide
  have hdescent : baseEnd_3212761 < baseStart_3212761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212762 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3]
def baseStart_3212762 : Nat := 118140960795 + 3212762 * 2 ^ 59
def prefixEnd_3212762 : Nat := 4983230072969 + 3 ^ 40 * 3212762 * 2
def baseEnd_3212762 : Nat := 1649691134500264287599783

theorem tailTrace_3212762 : CollatzResearch.WordTrace tailWord_3212762 prefixEnd_3212762 1649691134500264287599783 := by
  unfold tailWord_3212762
  simp only [CollatzResearch.WordTrace]
  refine ⟨29294764196679861227696135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78119371191146296607189693 29294764196679861227696135)
  ·
    refine ⟨43942146295019791841544203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29294764196679861227696135 43942146295019791841544203)
    ·
      refine ⟨65913219442529687762316305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43942146295019791841544203 65913219442529687762316305)
      ·
        refine ⟨49434914581897265821737229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65913219442529687762316305 49434914581897265821737229)
        ·
          refine ⟨18538092968211474683151461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49434914581897265821737229 18538092968211474683151461)
          ·
            refine ⟨3475892431539651503090899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18538092968211474683151461 3475892431539651503090899)
            ·
              refine ⟨5213838647309477254636349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475892431539651503090899 5213838647309477254636349)
              ·
                refine ⟨1955189492741053970488631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5213838647309477254636349 1955189492741053970488631)
                ·
                  refine ⟨2932784239111580955732947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955189492741053970488631 2932784239111580955732947)
                  ·
                    refine ⟨4399176358667371433599421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2932784239111580955732947 4399176358667371433599421)
                    ·
                      refine ⟨1649691134500264287599783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4399176358667371433599421 1649691134500264287599783)
                      ·
                        rfl

theorem cell23_3212762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_3212762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212762 prefixEnd_3212762 := by exact prefixLift 3212762
  have htrace : WordTrace (prefixWord ++ tailWord_3212762) baseStart_3212762 baseEnd_3212762 := by
    simpa [prefixWord, tailWord_3212762, baseEnd_3212762] using wordTrace_append hprefix tailTrace_3212762
  have hstable : (prefixWord ++ tailWord_3212762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212762).length < 2 ^ (prefixWord ++ tailWord_3212762).sum := by decide
  have hdescent : baseEnd_3212762 < baseStart_3212762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212771 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3212771 : Nat := 118140960795 + 3212771 * 2 ^ 59
def prefixEnd_3212771 : Nat := 4983230072969 + 3 ^ 40 * 3212771 * 2
def baseEnd_3212771 : Nat := 1649695755826154752387241

theorem tailTrace_3212771 : CollatzResearch.WordTrace tailWord_3212771 prefixEnd_3212771 1649695755826154752387241 := by
  unfold tailWord_3212771
  simp only [CollatzResearch.WordTrace]
  refine ⟨117179385043686839447862167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78119590029124559631908111 117179385043686839447862167)
  ·
    refine ⟨175769077565530259171793251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117179385043686839447862167 175769077565530259171793251)
    ·
      refine ⟨263653616348295388757689877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175769077565530259171793251 263653616348295388757689877)
      ·
        refine ⟨12358763266326346348016713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 263653616348295388757689877 12358763266326346348016713)
        ·
          refine ⟨9269072449744759761012535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12358763266326346348016713 9269072449744759761012535)
          ·
            refine ⟨13903608674617139641518803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269072449744759761012535 13903608674617139641518803)
            ·
              refine ⟨20855413011925709462278205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13903608674617139641518803 20855413011925709462278205)
              ·
                refine ⟨7820779879472141048354327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20855413011925709462278205 7820779879472141048354327)
                ·
                  refine ⟨11731169819208211572531491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7820779879472141048354327 11731169819208211572531491)
                  ·
                    refine ⟨17596754728812317358797237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11731169819208211572531491 17596754728812317358797237)
                    ·
                      refine ⟨1649695755826154752387241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17596754728812317358797237 1649695755826154752387241)
                      ·
                        rfl

theorem cell23_3212771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3212771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212771 prefixEnd_3212771 := by exact prefixLift 3212771
  have htrace : WordTrace (prefixWord ++ tailWord_3212771) baseStart_3212771 baseEnd_3212771 := by
    simpa [prefixWord, tailWord_3212771, baseEnd_3212771] using wordTrace_append hprefix tailTrace_3212771
  have hstable : (prefixWord ++ tailWord_3212771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212771).length < 2 ^ (prefixWord ++ tailWord_3212771).sum := by decide
  have hdescent : baseEnd_3212771 < baseStart_3212771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212785 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 3, 2, 2]
def baseStart_3212785 : Nat := 118140960795 + 3212785 * 2 ^ 59
def prefixEnd_3212785 : Nat := 4983230072969 + 3 ^ 40 * 3212785 * 2
def baseEnd_3212785 : Nat := 1649702944555317697612177

theorem tailTrace_3212785 : CollatzResearch.WordTrace tailWord_3212785 prefixEnd_3212785 1649702944555317697612177 := by
  unfold tailWord_3212785
  simp only [CollatzResearch.WordTrace]
  refine ⟨117179895665636119838871809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78119930443757413225914539 117179895665636119838871809)
  ·
    refine ⟨87884921749227089879153857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117179895665636119838871809 87884921749227089879153857)
    ·
      refine ⟨65913691311920317409365393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87884921749227089879153857 65913691311920317409365393)
      ·
        refine ⟨49435268483940238057024045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65913691311920317409365393 49435268483940238057024045)
        ·
          refine ⟨18538225681477589271384017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49435268483940238057024045 18538225681477589271384017)
          ·
            refine ⟨13903669261108191953538013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18538225681477589271384017 13903669261108191953538013)
            ·
              refine ⟨5213875972915571982576755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13903669261108191953538013 5213875972915571982576755)
              ·
                refine ⟨7820813959373357973865133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213875972915571982576755 7820813959373357973865133)
                ·
                  refine ⟨2932805234765009240199425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7820813959373357973865133 2932805234765009240199425)
                  ·
                    refine ⟨2199603926073756930149569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2932805234765009240199425 2199603926073756930149569)
                    ·
                      refine ⟨1649702944555317697612177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199603926073756930149569 1649702944555317697612177)
                      ·
                        rfl

theorem cell23_3212785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_3212785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212785 prefixEnd_3212785 := by exact prefixLift 3212785
  have htrace : WordTrace (prefixWord ++ tailWord_3212785) baseStart_3212785 baseEnd_3212785 := by
    simpa [prefixWord, tailWord_3212785, baseEnd_3212785] using wordTrace_append hprefix tailTrace_3212785
  have hstable : (prefixWord ++ tailWord_3212785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212785).length < 2 ^ (prefixWord ++ tailWord_3212785).sum := by decide
  have hdescent : baseEnd_3212785 < baseStart_3212785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212794 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_3212794 : Nat := 118140960795 + 3212794 * 2 ^ 59
def prefixEnd_3212794 : Nat := 4983230072969 + 3 ^ 40 * 3212794 * 2
def baseEnd_3212794 : Nat := 1649707565881208162399635

theorem tailTrace_3212794 : CollatzResearch.WordTrace tailWord_3212794 prefixEnd_3212794 1649707565881208162399635 := by
  unfold tailWord_3212794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295055980650878593987359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78120149281735676250632957 29295055980650878593987359)
  ·
    refine ⟨43942583970976317890981039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29295055980650878593987359 43942583970976317890981039)
    ·
      refine ⟨65913875956464476836471559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43942583970976317890981039 65913875956464476836471559)
      ·
        refine ⟨98870813934696715254707339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65913875956464476836471559 98870813934696715254707339)
        ·
          refine ⟨148306220902045072882061009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98870813934696715254707339 148306220902045072882061009)
          ·
            refine ⟨111229665676533804661545757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148306220902045072882061009 111229665676533804661545757)
            ·
              refine ⟨41711124628700176748079659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111229665676533804661545757 41711124628700176748079659)
              ·
                refine ⟨62566686943050265122119489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41711124628700176748079659 62566686943050265122119489)
                ·
                  refine ⟨46925015207287698841589617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62566686943050265122119489 46925015207287698841589617)
                  ·
                    refine ⟨35193761405465774131192213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46925015207287698841589617 35193761405465774131192213)
                    ·
                      refine ⟨1649707565881208162399635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35193761405465774131192213 1649707565881208162399635)
                      ·
                        rfl

theorem cell23_3212794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_3212794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212794 prefixEnd_3212794 := by exact prefixLift 3212794
  have htrace : WordTrace (prefixWord ++ tailWord_3212794) baseStart_3212794 baseEnd_3212794 := by
    simpa [prefixWord, tailWord_3212794, baseEnd_3212794] using wordTrace_append hprefix tailTrace_3212794
  have hstable : (prefixWord ++ tailWord_3212794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212794).length < 2 ^ (prefixWord ++ tailWord_3212794).sum := by decide
  have hdescent : baseEnd_3212794 < baseStart_3212794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212802 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3212802 : Nat := 118140960795 + 3212802 * 2 ^ 59
def prefixEnd_3212802 : Nat := 4983230072969 + 3 ^ 40 * 3212802 * 2
def baseEnd_3212802 : Nat := 1649711673726444131099599

theorem tailTrace_3212802 : CollatzResearch.WordTrace tailWord_3212802 prefixEnd_3212802 1649711673726444131099599 := by
  unfold tailWord_3212802
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295128926643632935560165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78120343804383021161493773 29295128926643632935560165)
  ·
    refine ⟨5492836673745681175417531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29295128926643632935560165 5492836673745681175417531)
    ·
      refine ⟨8239255010618521763126297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492836673745681175417531 8239255010618521763126297)
      ·
        refine ⟨6179441257963891322344723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8239255010618521763126297 6179441257963891322344723)
        ·
          refine ⟨9269161886945836983517085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179441257963891322344723 9269161886945836983517085)
          ·
            refine ⟨3475935707604688868818907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9269161886945836983517085 3475935707604688868818907)
            ·
              refine ⟨5213903561407033303228361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475935707604688868818907 5213903561407033303228361)
              ·
                refine ⟨3910427671055274977421271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213903561407033303228361 3910427671055274977421271)
                ·
                  refine ⟨5865641506582912466131907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910427671055274977421271 5865641506582912466131907)
                  ·
                    refine ⟨8798462259874368699197861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865641506582912466131907 8798462259874368699197861)
                    ·
                      refine ⟨1649711673726444131099599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8798462259874368699197861 1649711673726444131099599)
                      ·
                        rfl

theorem cell23_3212802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3212802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212802 prefixEnd_3212802 := by exact prefixLift 3212802
  have htrace : WordTrace (prefixWord ++ tailWord_3212802) baseStart_3212802 baseEnd_3212802 := by
    simpa [prefixWord, tailWord_3212802, baseEnd_3212802] using wordTrace_append hprefix tailTrace_3212802
  have hstable : (prefixWord ++ tailWord_3212802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212802).length < 2 ^ (prefixWord ++ tailWord_3212802).sum := by decide
  have hdescent : baseEnd_3212802 < baseStart_3212802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212806 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3212806 : Nat := 118140960795 + 3212806 * 2 ^ 59
def prefixEnd_3212806 : Nat := 4983230072969 + 3 ^ 40 * 3212806 * 2
def baseEnd_3212806 : Nat := 1649713727649062115449581

theorem tailTrace_3212806 : CollatzResearch.WordTrace tailWord_3212806 prefixEnd_3212806 1649713727649062115449581 := by
  unfold tailWord_3212806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661895674955001263293321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78120441065706693616924181 3661895674955001263293321)
  ·
    refine ⟨2746421756216250947469991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3661895674955001263293321 2746421756216250947469991)
    ·
      refine ⟨4119632634324376421204987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746421756216250947469991 4119632634324376421204987)
      ·
        refine ⟨6179448951486564631807481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119632634324376421204987 6179448951486564631807481)
        ·
          refine ⟨4634586713614923473855611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6179448951486564631807481 4634586713614923473855611)
          ·
            refine ⟨6951880070422385210783417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4634586713614923473855611 6951880070422385210783417)
            ·
              refine ⟨5213910052816788908087563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6951880070422385210783417 5213910052816788908087563)
              ·
                refine ⟨7820865079225183362131345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213910052816788908087563 7820865079225183362131345)
                ·
                  refine ⟨5865648809418887521598509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7820865079225183362131345 5865648809418887521598509)
                  ·
                    refine ⟨2199618303532082820599441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5865648809418887521598509 2199618303532082820599441)
                    ·
                      refine ⟨1649713727649062115449581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199618303532082820599441 1649713727649062115449581)
                      ·
                        rfl

theorem cell23_3212806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3212806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212806 prefixEnd_3212806 := by exact prefixLift 3212806
  have htrace : WordTrace (prefixWord ++ tailWord_3212806) baseStart_3212806 baseEnd_3212806 := by
    simpa [prefixWord, tailWord_3212806, baseEnd_3212806] using wordTrace_append hprefix tailTrace_3212806
  have hstable : (prefixWord ++ tailWord_3212806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212806).length < 2 ^ (prefixWord ++ tailWord_3212806).sum := by decide
  have hdescent : baseEnd_3212806 < baseStart_3212806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212830 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3212830 : Nat := 118140960795 + 3212830 * 2 ^ 59
def prefixEnd_3212830 : Nat := 4983230072969 + 3 ^ 40 * 3212830 * 2
def baseEnd_3212830 : Nat := 1649726051184770021549471

theorem tailTrace_3212830 : CollatzResearch.WordTrace tailWord_3212830 prefixEnd_3212830 1649726051184770021549471 := by
  unfold tailWord_3212830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647692118809136565532493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78121024633648728349506629 14647692118809136565532493)
  ·
    refine ⟨5492884544553426212074685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14647692118809136565532493 5492884544553426212074685)
    ·
      refine ⟨2059831704207534829528007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5492884544553426212074685 2059831704207534829528007)
      ·
        refine ⟨3089747556311302244292011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059831704207534829528007 3089747556311302244292011)
        ·
          refine ⟨4634621334466953366438017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089747556311302244292011 4634621334466953366438017)
          ·
            refine ⟨3475966000850215024828513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4634621334466953366438017 3475966000850215024828513)
            ·
              refine ⟨2606974500637661268621385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475966000850215024828513 2606974500637661268621385)
              ·
                refine ⟨1955230875478245951466039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606974500637661268621385 1955230875478245951466039)
                ·
                  refine ⟨2932846313217368927199059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955230875478245951466039 2932846313217368927199059)
                  ·
                    refine ⟨4399269469826053390798589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2932846313217368927199059 4399269469826053390798589)
                    ·
                      refine ⟨1649726051184770021549471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4399269469826053390798589 1649726051184770021549471)
                      ·
                        rfl

theorem cell23_3212830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3212830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212830 prefixEnd_3212830 := by exact prefixLift 3212830
  have htrace : WordTrace (prefixWord ++ tailWord_3212830) baseStart_3212830 baseEnd_3212830 := by
    simpa [prefixWord, tailWord_3212830, baseEnd_3212830] using wordTrace_append hprefix tailTrace_3212830
  have hstable : (prefixWord ++ tailWord_3212830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212830).length < 2 ^ (prefixWord ++ tailWord_3212830).sum := by decide
  have hdescent : baseEnd_3212830 < baseStart_3212830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212851 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 2, 6]
def baseStart_3212851 : Nat := 118140960795 + 3212851 * 2 ^ 59
def prefixEnd_3212851 : Nat := 4983230072969 + 3 ^ 40 * 3212851 * 2
def baseEnd_3212851 : Nat := 549912278092838146462291

theorem tailTrace_3212851 : CollatzResearch.WordTrace tailWord_3212851 prefixEnd_3212851 549912278092838146462291 := by
  unfold tailWord_3212851
  simp only [CollatzResearch.WordTrace]
  refine ⟨117182302883397013110774407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78121535255598008740516271 117182302883397013110774407)
  ·
    refine ⟨175773454325095519666161611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117182302883397013110774407 175773454325095519666161611)
    ·
      refine ⟨263660181487643279499242417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175773454325095519666161611 263660181487643279499242417)
      ·
        refine ⟨197745136115732459624431813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263660181487643279499242417 197745136115732459624431813)
        ·
          refine ⟨37077213021699836179580965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197745136115732459624431813 37077213021699836179580965)
          ·
            refine ⟨6951977441568719283671431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37077213021699836179580965 6951977441568719283671431)
            ·
              refine ⟨10427966162353078925507147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6951977441568719283671431 10427966162353078925507147)
              ·
                refine ⟨15641949243529618388260721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10427966162353078925507147 15641949243529618388260721)
                ·
                  refine ⟨11731461932647213791195541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15641949243529618388260721 11731461932647213791195541)
                  ·
                    refine ⟨549912278092838146462291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11731461932647213791195541 549912278092838146462291)
                    ·
                      rfl

theorem cell23_3212851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 6].length) (baseStart_3212851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212851 prefixEnd_3212851 := by exact prefixLift 3212851
  have htrace : WordTrace (prefixWord ++ tailWord_3212851) baseStart_3212851 baseEnd_3212851 := by
    simpa [prefixWord, tailWord_3212851, baseEnd_3212851] using wordTrace_append hprefix tailTrace_3212851
  have hstable : (prefixWord ++ tailWord_3212851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212851).length < 2 ^ (prefixWord ++ tailWord_3212851).sum := by decide
  have hdescent : baseEnd_3212851 < baseStart_3212851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212892 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_3212892 : Nat := 118140960795 + 3212892 * 2 ^ 59
def prefixEnd_3212892 : Nat := 4983230072969 + 3 ^ 40 * 3212892 * 2
def baseEnd_3212892 : Nat := 1649757886985348778974185

theorem tailTrace_3212892 : CollatzResearch.WordTrace tailWord_3212892 prefixEnd_3212892 1649757886985348778974185 := by
  unfold tailWord_3212892
  simp only [CollatzResearch.WordTrace]
  refine ⟨58591899138124238556508465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78122532184165651408677953 58591899138124238556508465)
  ·
    refine ⟨43943924353593178917381349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58591899138124238556508465 43943924353593178917381349)
    ·
      refine ⟨8239485816298721047009003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43943924353593178917381349 8239485816298721047009003)
      ·
        refine ⟨12359228724448081570513505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239485816298721047009003 12359228724448081570513505)
        ·
          refine ⟨9269421543336061177885129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12359228724448081570513505 9269421543336061177885129)
          ·
            refine ⟨6952066157502045883413847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269421543336061177885129 6952066157502045883413847)
            ·
              refine ⟨10428099236253068825120771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952066157502045883413847 10428099236253068825120771)
              ·
                refine ⟨15642148854379603237681157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10428099236253068825120771 15642148854379603237681157)
                ·
                  refine ⟨2932902910196175607065217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15642148854379603237681157 2932902910196175607065217)
                  ·
                    refine ⟨2199677182647131705298913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2932902910196175607065217 2199677182647131705298913)
                    ·
                      refine ⟨1649757886985348778974185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199677182647131705298913 1649757886985348778974185)
                      ·
                        rfl

theorem cell23_3212892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_3212892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212892 prefixEnd_3212892 := by exact prefixLift 3212892
  have htrace : WordTrace (prefixWord ++ tailWord_3212892) baseStart_3212892 baseEnd_3212892 := by
    simpa [prefixWord, tailWord_3212892, baseEnd_3212892] using wordTrace_append hprefix tailTrace_3212892
  have hstable : (prefixWord ++ tailWord_3212892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212892).length < 2 ^ (prefixWord ++ tailWord_3212892).sum := by decide
  have hdescent : baseEnd_3212892 < baseStart_3212892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212909 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3212909 : Nat := 118140960795 + 3212909 * 2 ^ 59
def prefixEnd_3212909 : Nat := 4983230072969 + 3 ^ 40 * 3212909 * 2
def baseEnd_3212909 : Nat := 1649766616156475212461607

theorem tailTrace_3212909 : CollatzResearch.WordTrace tailWord_3212909 prefixEnd_3212909 1649766616156475212461607 := by
  unfold tailWord_3212909
  simp only [CollatzResearch.WordTrace]
  refine ⟨117184418317186889016385781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78122945544791259344257187 117184418317186889016385781)
  ·
    refine ⟨10986039217236270845286167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117184418317186889016385781 10986039217236270845286167)
    ·
      refine ⟨16479058825854406267929251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10986039217236270845286167 16479058825854406267929251)
      ·
        refine ⟨24718588238781609401893877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16479058825854406267929251 24718588238781609401893877)
        ·
          refine ⟨2317367647385775881427551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24718588238781609401893877 2317367647385775881427551)
          ·
            refine ⟨3476051471078663822141327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317367647385775881427551 3476051471078663822141327)
            ·
              refine ⟨5214077206617995733211991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476051471078663822141327 5214077206617995733211991)
              ·
                refine ⟨7821115809926993599817987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5214077206617995733211991 7821115809926993599817987)
                ·
                  refine ⟨11731673714890490399726981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7821115809926993599817987 11731673714890490399726981)
                  ·
                    refine ⟨2199688821541966949948809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11731673714890490399726981 2199688821541966949948809)
                    ·
                      refine ⟨1649766616156475212461607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199688821541966949948809 1649766616156475212461607)
                      ·
                        rfl

theorem cell23_3212909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3212909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212909 prefixEnd_3212909 := by exact prefixLift 3212909
  have htrace : WordTrace (prefixWord ++ tailWord_3212909) baseStart_3212909 baseEnd_3212909 := by
    simpa [prefixWord, tailWord_3212909, baseEnd_3212909] using wordTrace_append hprefix tailTrace_3212909
  have hstable : (prefixWord ++ tailWord_3212909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212909).length < 2 ^ (prefixWord ++ tailWord_3212909).sum := by decide
  have hdescent : baseEnd_3212909 < baseStart_3212909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212932 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 5]
def baseStart_3212932 : Nat := 118140960795 + 3212932 * 2 ^ 59
def prefixEnd_3212932 : Nat := 4983230072969 + 3 ^ 40 * 3212932 * 2
def baseEnd_3212932 : Nat := 183308714023503180274889

theorem tailTrace_3212932 : CollatzResearch.WordTrace tailWord_3212932 prefixEnd_3212932 183308714023503180274889 := by
  unfold tailWord_3212932
  simp only [CollatzResearch.WordTrace]
  refine ⟨58592628598051781972236525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78123504797402375962982033 58592628598051781972236525)
  ·
    refine ⟨21972235724269418239588697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58592628598051781972236525 21972235724269418239588697)
    ·
      refine ⟨16479176793202063679691523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21972235724269418239588697 16479176793202063679691523)
      ·
        refine ⟨24718765189803095519537285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16479176793202063679691523 24718765189803095519537285)
        ·
          refine ⟨4634768473088080409913241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24718765189803095519537285 4634768473088080409913241)
          ·
            refine ⟨3476076354816060307434931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4634768473088080409913241 3476076354816060307434931)
            ·
              refine ⟨5214114532224090461152397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476076354816060307434931 5214114532224090461152397)
              ·
                refine ⟨1955292949584033922932149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5214114532224090461152397 1955292949584033922932149)
                ·
                  refine ⟨183308714023503180274889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955292949584033922932149 183308714023503180274889)
                  ·
                    rfl

theorem cell23_3212932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_3212932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212932 prefixEnd_3212932 := by exact prefixLift 3212932
  have htrace : WordTrace (prefixWord ++ tailWord_3212932) baseStart_3212932 baseEnd_3212932 := by
    simpa [prefixWord, tailWord_3212932, baseEnd_3212932] using wordTrace_append hprefix tailTrace_3212932
  have hstable : (prefixWord ++ tailWord_3212932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212932).length < 2 ^ (prefixWord ++ tailWord_3212932).sum := by decide
  have hdescent : baseEnd_3212932 < baseStart_3212932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212982 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3212982 : Nat := 118140960795 + 3212982 * 2 ^ 59
def prefixEnd_3212982 : Nat := 4983230072969 + 3 ^ 40 * 3212982 * 2
def baseEnd_3212982 : Nat := 1649804100244253426848771

theorem tailTrace_3212982 : CollatzResearch.WordTrace tailWord_3212982 prefixEnd_3212982 1649804100244253426848771 := by
  unfold tailWord_3212982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324192552870151405237075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78124720563948281655862133 7324192552870151405237075)
  ·
    refine ⟨10986288829305227107855613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7324192552870151405237075 10986288829305227107855613)
    ·
      refine ⟨4119858310989460165445855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10986288829305227107855613 4119858310989460165445855)
      ·
        refine ⟨6179787466484190248168783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119858310989460165445855 6179787466484190248168783)
        ·
          refine ⟨9269681199726285372253175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179787466484190248168783 9269681199726285372253175)
          ·
            refine ⟨13904521799589428058379763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269681199726285372253175 13904521799589428058379763)
            ·
              refine ⟨20856782699384142087569645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904521799589428058379763 20856782699384142087569645)
              ·
                refine ⟨7821293512269053282838617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20856782699384142087569645 7821293512269053282838617)
                ·
                  refine ⟨5865970134201789962128963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7821293512269053282838617 5865970134201789962128963)
                  ·
                    refine ⟨8798955201302684943193445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865970134201789962128963 8798955201302684943193445)
                    ·
                      refine ⟨1649804100244253426848771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8798955201302684943193445 1649804100244253426848771)
                      ·
                        rfl

theorem cell23_3212982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3212982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3212982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3212982 prefixEnd_3212982 := by exact prefixLift 3212982
  have htrace : WordTrace (prefixWord ++ tailWord_3212982) baseStart_3212982 baseEnd_3212982 := by
    simpa [prefixWord, tailWord_3212982, baseEnd_3212982] using wordTrace_append hprefix tailTrace_3212982
  have hstable : (prefixWord ++ tailWord_3212982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212982).length < 2 ^ (prefixWord ++ tailWord_3212982).sum := by decide
  have hdescent : baseEnd_3212982 < baseStart_3212982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213009 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 1, 4]
def baseStart_3213009 : Nat := 118140960795 + 3213009 * 2 ^ 59
def prefixEnd_3213009 : Nat := 4983230072969 + 3 ^ 40 * 3213009 * 2
def baseEnd_3213009 : Nat := 549939321407308273737049

theorem tailTrace_3213009 : CollatzResearch.WordTrace tailWord_3213009 prefixEnd_3213009 549939321407308273737049 := by
  unfold tailWord_3213009
  simp only [CollatzResearch.WordTrace]
  refine ⟨117188065616824606095026081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78125377077883070730017387 117188065616824606095026081)
  ·
    refine ⟨87891049212618454571269561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117188065616824606095026081 87891049212618454571269561)
    ·
      refine ⟨65918286909463840928452171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87891049212618454571269561 65918286909463840928452171)
      ·
        refine ⟨98877430364195761392678257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65918286909463840928452171 98877430364195761392678257)
        ·
          refine ⟨74158072773146821044508693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98877430364195761392678257 74158072773146821044508693)
          ·
            refine ⟨3476159661241257236461345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74158072773146821044508693 3476159661241257236461345)
            ·
              refine ⟨2607119745930942927346009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476159661241257236461345 2607119745930942927346009)
              ·
                refine ⟨1955339809448207195509507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607119745930942927346009 1955339809448207195509507)
                ·
                  refine ⟨2933009714172310793264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955339809448207195509507 2933009714172310793264261)
                  ·
                    refine ⟨549939321407308273737049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2933009714172310793264261 549939321407308273737049)
                    ·
                      rfl

theorem cell23_3213009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_3213009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213009 prefixEnd_3213009 := by exact prefixLift 3213009
  have htrace : WordTrace (prefixWord ++ tailWord_3213009) baseStart_3213009 baseEnd_3213009 := by
    simpa [prefixWord, tailWord_3213009, baseEnd_3213009] using wordTrace_append hprefix tailTrace_3213009
  have hstable : (prefixWord ++ tailWord_3213009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213009).length < 2 ^ (prefixWord ++ tailWord_3213009).sum := by decide
  have hdescent : baseEnd_3213009 < baseStart_3213009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213015 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_3213015 : Nat := 118140960795 + 3213015 * 2 ^ 59
def prefixEnd_3213015 : Nat := 4983230072969 + 3 ^ 40 * 3213015 * 2
def baseEnd_3213015 : Nat := 1649821045105851797736119

theorem tailTrace_3213015 : CollatzResearch.WordTrace tailWord_3213015 prefixEnd_3213015 1649821045105851797736119 := by
  unfold tailWord_3213015
  simp only [CollatzResearch.WordTrace]
  refine ⟨117188284454802869119744499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78125522969868579413162999 117188284454802869119744499)
  ·
    refine ⟨175782426682204303679616749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117188284454802869119744499 175782426682204303679616749)
    ·
      refine ⟨65918410005826613879856281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175782426682204303679616749 65918410005826613879856281)
      ·
        refine ⟨49438807504369960409892211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65918410005826613879856281 49438807504369960409892211)
        ·
          refine ⟨74158211256554940614838317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49438807504369960409892211 74158211256554940614838317)
          ·
            refine ⟨27809329221208102730564369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74158211256554940614838317 27809329221208102730564369)
            ·
              refine ⟨20856996915906077047923277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27809329221208102730564369 20856996915906077047923277)
              ·
                refine ⟨7821373843464778892971229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20856996915906077047923277 7821373843464778892971229)
                ·
                  refine ⟨2933015191299292084864211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7821373843464778892971229 2933015191299292084864211)
                  ·
                    refine ⟨4399522786948938127296317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2933015191299292084864211 4399522786948938127296317)
                    ·
                      refine ⟨1649821045105851797736119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4399522786948938127296317 1649821045105851797736119)
                      ·
                        rfl

theorem cell23_3213015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_3213015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213015 prefixEnd_3213015 := by exact prefixLift 3213015
  have htrace : WordTrace (prefixWord ++ tailWord_3213015) baseStart_3213015 baseEnd_3213015 := by
    simpa [prefixWord, tailWord_3213015, baseEnd_3213015] using wordTrace_append hprefix tailTrace_3213015
  have hstable : (prefixWord ++ tailWord_3213015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213015).length < 2 ^ (prefixWord ++ tailWord_3213015).sum := by decide
  have hdescent : baseEnd_3213015 < baseStart_3213015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213018 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_3213018 : Nat := 118140960795 + 3213018 * 2 ^ 59
def prefixEnd_3213018 : Nat := 4983230072969 + 3 ^ 40 * 3213018 * 2
def baseEnd_3213018 : Nat := 549940861849271761999535

theorem tailTrace_3213018 : CollatzResearch.WordTrace tailWord_3213018 prefixEnd_3213018 549940861849271761999535 := by
  unfold tailWord_3213018
  simp only [CollatzResearch.WordTrace]
  refine ⟨29297098468448000158025927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78125595915861333754735805 29297098468448000158025927)
  ·
    refine ⟨43945647702672000237038891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29297098468448000158025927 43945647702672000237038891)
    ·
      refine ⟨65918471554008000355558337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43945647702672000237038891 65918471554008000355558337)
      ·
        refine ⟨49438853665506000266668753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65918471554008000355558337 49438853665506000266668753)
        ·
          refine ⟨37079140249129500200001565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49438853665506000266668753 37079140249129500200001565)
          ·
            refine ⟨13904677593423562575000587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37079140249129500200001565 13904677593423562575000587)
            ·
              refine ⟨20857016390135343862500881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904677593423562575000587 20857016390135343862500881)
              ·
                refine ⟨15642762292601507896875661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20857016390135343862500881 15642762292601507896875661)
                ·
                  refine ⟨5866035859725565461328373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15642762292601507896875661 5866035859725565461328373)
                  ·
                    refine ⟨549940861849271761999535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5866035859725565461328373 549940861849271761999535)
                    ·
                      rfl

theorem cell23_3213018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_3213018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213018 prefixEnd_3213018 := by exact prefixLift 3213018
  have htrace : WordTrace (prefixWord ++ tailWord_3213018) baseStart_3213018 baseEnd_3213018 := by
    simpa [prefixWord, tailWord_3213018, baseEnd_3213018] using wordTrace_append hprefix tailTrace_3213018
  have hstable : (prefixWord ++ tailWord_3213018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213018).length < 2 ^ (prefixWord ++ tailWord_3213018).sum := by decide
  have hdescent : baseEnd_3213018 < baseStart_3213018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213032 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3213032 : Nat := 118140960795 + 3213032 * 2 ^ 59
def prefixEnd_3213032 : Nat := 4983230072969 + 3 ^ 40 * 3213032 * 2
def baseEnd_3213032 : Nat := 1649829774276978231223541

theorem tailTrace_3213032 : CollatzResearch.WordTrace tailWord_3213032 prefixEnd_3213032 1649829774276978231223541 := by
  unfold tailWord_3213032
  simp only [CollatzResearch.WordTrace]
  refine ⟨58594452247870640511556675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78125936330494187348742233 58594452247870640511556675)
  ·
    refine ⟨87891678371805960767335013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58594452247870640511556675 87891678371805960767335013)
    ·
      refine ⟨16479689694713617643875315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87891678371805960767335013 16479689694713617643875315)
      ·
        refine ⟨24719534542070426465812973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16479689694713617643875315 24719534542070426465812973)
        ·
          refine ⟨9269825453276409924679865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24719534542070426465812973 9269825453276409924679865)
          ·
            refine ⟨6952369089957307443509899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269825453276409924679865 6952369089957307443509899)
            ·
              refine ⟨10428553634935961165264849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952369089957307443509899 10428553634935961165264849)
              ·
                refine ⟨7821415226201970873948637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10428553634935961165264849 7821415226201970873948637)
                ·
                  refine ⟨2933030709825739077730739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7821415226201970873948637 2933030709825739077730739)
                  ·
                    refine ⟨4399546064738608616596109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2933030709825739077730739 4399546064738608616596109)
                    ·
                      refine ⟨1649829774276978231223541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4399546064738608616596109 1649829774276978231223541)
                      ·
                        rfl

theorem cell23_3213032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3213032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213032 prefixEnd_3213032 := by exact prefixLift 3213032
  have htrace : WordTrace (prefixWord ++ tailWord_3213032) baseStart_3213032 baseEnd_3213032 := by
    simpa [prefixWord, tailWord_3213032, baseEnd_3213032] using wordTrace_append hprefix tailTrace_3213032
  have hstable : (prefixWord ++ tailWord_3213032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213032).length < 2 ^ (prefixWord ++ tailWord_3213032).sum := by decide
  have hdescent : baseEnd_3213032 < baseStart_3213032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213068 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3213068 : Nat := 118140960795 + 3213068 * 2 ^ 59
def prefixEnd_3213068 : Nat := 4983230072969 + 3 ^ 40 * 3213068 * 2
def baseEnd_3213068 : Nat := 1649848259580540090373375

theorem tailTrace_3213068 : CollatzResearch.WordTrace tailWord_3213068 prefixEnd_3213068 1649848259580540090373375 := by
  unfold tailWord_3213068
  simp only [CollatzResearch.WordTrace]
  refine ⟨58595108761805429585711929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78126811682407239447615905 58595108761805429585711929)
  ·
    refine ⟨43946331571354072189283947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58595108761805429585711929 43946331571354072189283947)
    ·
      refine ⟨65919497357031108283925921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43946331571354072189283947 65919497357031108283925921)
      ·
        refine ⟨49439623017773331212944441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65919497357031108283925921 49439623017773331212944441)
        ·
          refine ⟨37079717263329998409708331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49439623017773331212944441 37079717263329998409708331)
          ·
            refine ⟨55619575894994997614562497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37079717263329998409708331 55619575894994997614562497)
            ·
              refine ⟨41714681921246248210921873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55619575894994997614562497 41714681921246248210921873)
              ·
                refine ⟨31286011440934686158191405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41714681921246248210921873 31286011440934686158191405)
                ·
                  refine ⟨11732254290350507309321777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31286011440934686158191405 11732254290350507309321777)
                  ·
                    refine ⟨8799190717762880481991333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11732254290350507309321777 8799190717762880481991333)
                    ·
                      refine ⟨1649848259580540090373375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8799190717762880481991333 1649848259580540090373375)
                      ·
                        rfl

theorem cell23_3213068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3213068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213068 prefixEnd_3213068 := by exact prefixLift 3213068
  have htrace : WordTrace (prefixWord ++ tailWord_3213068) baseStart_3213068 baseEnd_3213068 := by
    simpa [prefixWord, tailWord_3213068, baseEnd_3213068] using wordTrace_append hprefix tailTrace_3213068
  have hstable : (prefixWord ++ tailWord_3213068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213068).length < 2 ^ (prefixWord ++ tailWord_3213068).sum := by decide
  have hdescent : baseEnd_3213068 < baseStart_3213068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213086 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3213086 : Nat := 118140960795 + 3213086 * 2 ^ 59
def prefixEnd_3213086 : Nat := 4983230072969 + 3 ^ 40 * 3213086 * 2
def baseEnd_3213086 : Nat := 549952500744107006649431

theorem tailTrace_3213086 : CollatzResearch.WordTrace tailWord_3213086 prefixEnd_3213086 549952500744107006649431 := by
  unfold tailWord_3213086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648859254693206030697389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78127249358363765497052741 14648859254693206030697389)
  ·
    refine ⟨5493322220509952261511521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14648859254693206030697389 5493322220509952261511521)
    ·
      refine ⟨4119991665382464196133641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5493322220509952261511521 4119991665382464196133641)
      ·
        refine ⟨3089993749036848147100231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4119991665382464196133641 3089993749036848147100231)
        ·
          refine ⟨4634990623555272220650347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089993749036848147100231 4634990623555272220650347)
          ·
            refine ⟨6952485935332908330975521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4634990623555272220650347 6952485935332908330975521)
            ·
              refine ⟨5214364451499681248231641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6952485935332908330975521 5214364451499681248231641)
              ·
                refine ⟨3910773338624760936173731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5214364451499681248231641 3910773338624760936173731)
                ·
                  refine ⟨5866160007937141404260597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910773338624760936173731 5866160007937141404260597)
                  ·
                    refine ⟨549952500744107006649431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5866160007937141404260597 549952500744107006649431)
                    ·
                      rfl

theorem cell23_3213086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3213086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213086 prefixEnd_3213086 := by exact prefixLift 3213086
  have htrace : WordTrace (prefixWord ++ tailWord_3213086) baseStart_3213086 baseEnd_3213086 := by
    simpa [prefixWord, tailWord_3213086, baseEnd_3213086] using wordTrace_append hprefix tailTrace_3213086
  have hstable : (prefixWord ++ tailWord_3213086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213086).length < 2 ^ (prefixWord ++ tailWord_3213086).sum := by decide
  have hdescent : baseEnd_3213086 < baseStart_3213086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213092 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3213092 : Nat := 118140960795 + 3213092 * 2 ^ 59
def prefixEnd_3213092 : Nat := 4983230072969 + 3 ^ 40 * 3213092 * 2
def baseEnd_3213092 : Nat := 1649860583116247996473265

theorem tailTrace_3213092 : CollatzResearch.WordTrace tailWord_3213092 prefixEnd_3213092 1649860583116247996473265 := by
  unfold tailWord_3213092
  simp only [CollatzResearch.WordTrace]
  refine ⟨58595546437761955635148765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78127395250349274180198353 58595546437761955635148765)
  ·
    refine ⟨21973329914160733363180787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58595546437761955635148765 21973329914160733363180787)
    ·
      refine ⟨32959994871241100044771181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21973329914160733363180787 32959994871241100044771181)
      ·
        refine ⟨12359998076715412516789193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32959994871241100044771181 12359998076715412516789193)
        ·
          refine ⟨9269998557536559387591895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12359998076715412516789193 9269998557536559387591895)
          ·
            refine ⟨13904997836304839081387843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269998557536559387591895 13904997836304839081387843)
            ·
              refine ⟨20857496754457258622081765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904997836304839081387843 20857496754457258622081765)
              ·
                refine ⟨3910780641460735991640331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20857496754457258622081765 3910780641460735991640331)
                ·
                  refine ⟨5866170962191103987460497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910780641460735991640331 5866170962191103987460497)
                  ·
                    refine ⟨4399628221643327990595373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5866170962191103987460497 4399628221643327990595373)
                    ·
                      refine ⟨1649860583116247996473265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4399628221643327990595373 1649860583116247996473265)
                      ·
                        rfl

theorem cell23_3213092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3213092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213092 prefixEnd_3213092 := by exact prefixLift 3213092
  have htrace : WordTrace (prefixWord ++ tailWord_3213092) baseStart_3213092 baseEnd_3213092 := by
    simpa [prefixWord, tailWord_3213092, baseEnd_3213092] using wordTrace_append hprefix tailTrace_3213092
  have hstable : (prefixWord ++ tailWord_3213092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213092).length < 2 ^ (prefixWord ++ tailWord_3213092).sum := by decide
  have hdescent : baseEnd_3213092 < baseStart_3213092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213106 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_3213106 : Nat := 118140960795 + 3213106 * 2 ^ 59
def prefixEnd_3213106 : Nat := 4983230072969 + 3 ^ 40 * 3213106 * 2
def baseEnd_3213106 : Nat := 1649867771845410941698201

theorem tailTrace_3213106 : CollatzResearch.WordTrace tailWord_3213106 prefixEnd_3213106 1649867771845410941698201 := by
  unfold tailWord_3213106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29297900874368297915326793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78127735664982127774204781 29297900874368297915326793)
  ·
    refine ⟨21973425655776223436495095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29297900874368297915326793 21973425655776223436495095)
    ·
      refine ⟨32960138483664335154742643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21973425655776223436495095 32960138483664335154742643)
      ·
        refine ⟨49440207725496502732113965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32960138483664335154742643 49440207725496502732113965)
        ·
          refine ⟨18540077897061188524542737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49440207725496502732113965 18540077897061188524542737)
          ·
            refine ⟨13905058422795891393407053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18540077897061188524542737 13905058422795891393407053)
            ·
              refine ⟨5214396908548459272527645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13905058422795891393407053 5214396908548459272527645)
              ·
                refine ⟨1955398840705672227197867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5214396908548459272527645 1955398840705672227197867)
                ·
                  refine ⟨2933098261058508340796801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955398840705672227197867 2933098261058508340796801)
                  ·
                    refine ⟨2199823695793881255597601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933098261058508340796801 2199823695793881255597601)
                    ·
                      refine ⟨1649867771845410941698201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199823695793881255597601 1649867771845410941698201)
                      ·
                        rfl

theorem cell23_3213106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_3213106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213106 prefixEnd_3213106 := by exact prefixLift 3213106
  have htrace : WordTrace (prefixWord ++ tailWord_3213106) baseStart_3213106 baseEnd_3213106 := by
    simpa [prefixWord, tailWord_3213106, baseEnd_3213106] using wordTrace_append hprefix tailTrace_3213106
  have hstable : (prefixWord ++ tailWord_3213106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213106).length < 2 ^ (prefixWord ++ tailWord_3213106).sum := by decide
  have hdescent : baseEnd_3213106 < baseStart_3213106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213165 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3213165 : Nat := 118140960795 + 3213165 * 2 ^ 59
def prefixEnd_3213165 : Nat := 4983230072969 + 3 ^ 40 * 3213165 * 2
def baseEnd_3213165 : Nat := 1649898067204026210860429

theorem tailTrace_3213165 : CollatzResearch.WordTrace tailWord_3213165 prefixEnd_3213165 1649898067204026210860429 := by
  unfold tailWord_3213165
  simp only [CollatzResearch.WordTrace]
  refine ⟨117193755404259444737704949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78129170269506296491803299 117193755404259444737704949)
  ·
    refine ⟨10986914569149322944159839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117193755404259444737704949 10986914569149322944159839)
    ·
      refine ⟨16480371853723984416239759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10986914569149322944159839 16480371853723984416239759)
      ·
        refine ⟨24720557780585976624359639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16480371853723984416239759 24720557780585976624359639)
        ·
          refine ⟨37080836670878964936539459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24720557780585976624359639 37080836670878964936539459)
          ·
            refine ⟨55621255006318447404809189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37080836670878964936539459 55621255006318447404809189)
            ·
              refine ⟨10428985313684708888401723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55621255006318447404809189 10428985313684708888401723)
              ·
                refine ⟨15643477970527063332602585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10428985313684708888401723 15643477970527063332602585)
                ·
                  refine ⟨11732608477895297499451939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15643477970527063332602585 11732608477895297499451939)
                  ·
                    refine ⟨17598912716842946249177909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11732608477895297499451939 17598912716842946249177909)
                    ·
                      refine ⟨1649898067204026210860429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17598912716842946249177909 1649898067204026210860429)
                      ·
                        rfl

theorem cell23_3213165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3213165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213165 prefixEnd_3213165 := by exact prefixLift 3213165
  have htrace : WordTrace (prefixWord ++ tailWord_3213165) baseStart_3213165 baseEnd_3213165 := by
    simpa [prefixWord, tailWord_3213165, baseEnd_3213165] using wordTrace_append hprefix tailTrace_3213165
  have hstable : (prefixWord ++ tailWord_3213165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213165).length < 2 ^ (prefixWord ++ tailWord_3213165).sum := by decide
  have hdescent : baseEnd_3213165 < baseStart_3213165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213178 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_3213178 : Nat := 118140960795 + 3213178 * 2 ^ 59
def prefixEnd_3213178 : Nat := 4983230072969 + 3 ^ 40 * 3213178 * 2
def baseEnd_3213178 : Nat := 1649904742452534659997869

theorem tailTrace_3213178 : CollatzResearch.WordTrace tailWord_3213178 prefixEnd_3213178 1649904742452534659997869 := by
  unfold tailWord_3213178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298557388303086989482047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78129486368808231971952125 29298557388303086989482047)
  ·
    refine ⟨43947836082454630484223071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29298557388303086989482047 43947836082454630484223071)
    ·
      refine ⟨65921754123681945726334607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43947836082454630484223071 65921754123681945726334607)
      ·
        refine ⟨98882631185522918589501911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65921754123681945726334607 98882631185522918589501911)
        ·
          refine ⟨148323946778284377884252867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98882631185522918589501911 148323946778284377884252867)
          ·
            refine ⟨222485920167426566826379301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148323946778284377884252867 222485920167426566826379301)
            ·
              refine ⟨41716110031392481279946119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222485920167426566826379301 41716110031392481279946119)
              ·
                refine ⟨62574165047088721919919179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41716110031392481279946119 62574165047088721919919179)
                ·
                  refine ⟨93861247570633082879878769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62574165047088721919919179 93861247570633082879878769)
                  ·
                    refine ⟨70395935677974812159909077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93861247570633082879878769 70395935677974812159909077)
                    ·
                      refine ⟨1649904742452534659997869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70395935677974812159909077 1649904742452534659997869)
                      ·
                        rfl

theorem cell23_3213178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_3213178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213178 prefixEnd_3213178 := by exact prefixLift 3213178
  have htrace : WordTrace (prefixWord ++ tailWord_3213178) baseStart_3213178 baseEnd_3213178 := by
    simpa [prefixWord, tailWord_3213178, baseEnd_3213178] using wordTrace_append hprefix tailTrace_3213178
  have hstable : (prefixWord ++ tailWord_3213178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213178).length < 2 ^ (prefixWord ++ tailWord_3213178).sum := by decide
  have hdescent : baseEnd_3213178 < baseStart_3213178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213192 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3213192 : Nat := 118140960795 + 3213192 * 2 ^ 59
def prefixEnd_3213192 : Nat := 4983230072969 + 3 ^ 40 * 3213192 * 2
def baseEnd_3213192 : Nat := 1649911931181697605222805

theorem tailTrace_3213192 : CollatzResearch.WordTrace tailWord_3213192 prefixEnd_3213192 1649911931181697605222805 := by
  unfold tailWord_3213192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58597370087580814174468915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78129826783441085565958553 58597370087580814174468915)
  ·
    refine ⟨87896055131371221261703373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58597370087580814174468915 87896055131371221261703373)
    ·
      refine ⟨32961020674264207973138765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87896055131371221261703373 32961020674264207973138765)
      ·
        refine ⟨12360382752849077989927037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32961020674264207973138765 12360382752849077989927037)
        ·
          refine ⟨4635143532318404246222639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12360382752849077989927037 4635143532318404246222639)
          ·
            refine ⟨6952715298477606369333959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635143532318404246222639 6952715298477606369333959)
            ·
              refine ⟨10429072947716409554000939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952715298477606369333959 10429072947716409554000939)
              ·
                refine ⟨15643609421574614331001409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10429072947716409554000939 15643609421574614331001409)
                ·
                  refine ⟨11732707066180960748251057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15643609421574614331001409 11732707066180960748251057)
                  ·
                    refine ⟨8799530299635720561188293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11732707066180960748251057 8799530299635720561188293)
                    ·
                      refine ⟨1649911931181697605222805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8799530299635720561188293 1649911931181697605222805)
                      ·
                        rfl

theorem cell23_3213192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3213192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213192 prefixEnd_3213192 := by exact prefixLift 3213192
  have htrace : WordTrace (prefixWord ++ tailWord_3213192) baseStart_3213192 baseEnd_3213192 := by
    simpa [prefixWord, tailWord_3213192, baseEnd_3213192] using wordTrace_append hprefix tailTrace_3213192
  have hstable : (prefixWord ++ tailWord_3213192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213192).length < 2 ^ (prefixWord ++ tailWord_3213192).sum := by decide
  have hdescent : baseEnd_3213192 < baseStart_3213192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213202 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3213202 : Nat := 118140960795 + 3213202 * 2 ^ 59
def prefixEnd_3213202 : Nat := 4983230072969 + 3 ^ 40 * 3213202 * 2
def baseEnd_3213202 : Nat := 183324118443138062899751

theorem tailTrace_3213202 : CollatzResearch.WordTrace tailWord_3213202 prefixEnd_3213202 183324118443138062899751 := by
  unfold tailWord_3213202
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298776226281350014200465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78130069936750266704534573 29298776226281350014200465)
  ·
    refine ⟨21974082169711012510650349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29298776226281350014200465 21974082169711012510650349)
    ·
      refine ⟨8240280813641629691493881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21974082169711012510650349 8240280813641629691493881)
      ·
        refine ⟨6180210610231222268620411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8240280813641629691493881 6180210610231222268620411)
        ·
          refine ⟨9270315915346833402930617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6180210610231222268620411 9270315915346833402930617)
          ·
            refine ⟨6952736936510125052197963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9270315915346833402930617 6952736936510125052197963)
            ·
              refine ⟨10429105404765187578296945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952736936510125052197963 10429105404765187578296945)
              ·
                refine ⟨7821829053573890683722709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10429105404765187578296945 7821829053573890683722709)
                ·
                  refine ⟨183324118443138062899751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7821829053573890683722709 183324118443138062899751)
                  ·
                    rfl

theorem cell23_3213202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3213202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213202 prefixEnd_3213202 := by exact prefixLift 3213202
  have htrace : WordTrace (prefixWord ++ tailWord_3213202) baseStart_3213202 baseEnd_3213202 := by
    simpa [prefixWord, tailWord_3213202, baseEnd_3213202] using wordTrace_append hprefix tailTrace_3213202
  have hstable : (prefixWord ++ tailWord_3213202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213202).length < 2 ^ (prefixWord ++ tailWord_3213202).sum := by decide
  have hdescent : baseEnd_3213202 < baseStart_3213202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213230 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3213230 : Nat := 118140960795 + 3213230 * 2 ^ 59
def prefixEnd_3213230 : Nat := 4983230072969 + 3 ^ 40 * 3213230 * 2
def baseEnd_3213230 : Nat := 1649931443446568456547631

theorem tailTrace_3213230 : CollatzResearch.WordTrace tailWord_3213230 prefixEnd_3213230 1649931443446568456547631 := by
  unfold tailWord_3213230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14649515768627995104852643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78130750766015973892547429 14649515768627995104852643)
  ·
    refine ⟨21974273652941992657278965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14649515768627995104852643 21974273652941992657278965)
    ·
      refine ⟨2060088154963311811619903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21974273652941992657278965 2060088154963311811619903)
      ·
        refine ⟨3090132232444967717429855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060088154963311811619903 3090132232444967717429855)
        ·
          refine ⟨4635198348667451576144783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090132232444967717429855 4635198348667451576144783)
          ·
            refine ⟨6952797523001177364217175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635198348667451576144783 6952797523001177364217175)
            ·
              refine ⟨10429196284501766046325763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952797523001177364217175 10429196284501766046325763)
              ·
                refine ⟨15643794426752649069488645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10429196284501766046325763 15643794426752649069488645)
                ·
                  refine ⟨2933211455016121700529121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15643794426752649069488645 2933211455016121700529121)
                  ·
                    refine ⟨2199908591262091275396841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933211455016121700529121 2199908591262091275396841)
                    ·
                      refine ⟨1649931443446568456547631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199908591262091275396841 1649931443446568456547631)
                      ·
                        rfl

theorem cell23_3213230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3213230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213230 prefixEnd_3213230 := by exact prefixLift 3213230
  have htrace : WordTrace (prefixWord ++ tailWord_3213230) baseStart_3213230 baseEnd_3213230 := by
    simpa [prefixWord, tailWord_3213230, baseEnd_3213230] using wordTrace_append hprefix tailTrace_3213230
  have hstable : (prefixWord ++ tailWord_3213230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213230).length < 2 ^ (prefixWord ++ tailWord_3213230).sum := by decide
  have hdescent : baseEnd_3213230 < baseStart_3213230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213235 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 4]
def baseStart_3213235 : Nat := 118140960795 + 3213235 * 2 ^ 59
def prefixEnd_3213235 : Nat := 4983230072969 + 3 ^ 40 * 3213235 * 2
def baseEnd_3213235 : Nat := 1649934010849840936985107

theorem tailTrace_3213235 : CollatzResearch.WordTrace tailWord_3213235 prefixEnd_3213235 1649934010849840936985107 := by
  unfold tailWord_3213235
  simp only [CollatzResearch.WordTrace]
  refine ⟨117196308514005846692753159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78130872342670564461835439 117196308514005846692753159)
  ·
    refine ⟨175794462771008770039129739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117196308514005846692753159 175794462771008770039129739)
    ·
      refine ⟨263691694156513155058694609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175794462771008770039129739 263691694156513155058694609)
      ·
        refine ⟨197768770617384866294020957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263691694156513155058694609 197768770617384866294020957)
        ·
          refine ⟨74163288981519324860257859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197768770617384866294020957 74163288981519324860257859)
          ·
            refine ⟨111244933472278987290386789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74163288981519324860257859 111244933472278987290386789)
            ·
              refine ⟨20858425026052310116947523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111244933472278987290386789 20858425026052310116947523)
              ·
                refine ⟨31287637539078465175421285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20858425026052310116947523 31287637539078465175421285)
                ·
                  refine ⟨5866432038577212220391491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31287637539078465175421285 5866432038577212220391491)
                  ·
                    refine ⟨8799648057865818330587237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5866432038577212220391491 8799648057865818330587237)
                    ·
                      refine ⟨1649934010849840936985107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8799648057865818330587237 1649934010849840936985107)
                      ·
                        rfl

theorem cell23_3213235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_3213235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213235 prefixEnd_3213235 := by exact prefixLift 3213235
  have htrace : WordTrace (prefixWord ++ tailWord_3213235) baseStart_3213235 baseEnd_3213235 := by
    simpa [prefixWord, tailWord_3213235, baseEnd_3213235] using wordTrace_append hprefix tailTrace_3213235
  have hstable : (prefixWord ++ tailWord_3213235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213235).length < 2 ^ (prefixWord ++ tailWord_3213235).sum := by decide
  have hdescent : baseEnd_3213235 < baseStart_3213235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213262 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3213262 : Nat := 118140960795 + 3213262 * 2 ^ 59
def prefixEnd_3213262 : Nat := 4983230072969 + 3 ^ 40 * 3213262 * 2
def baseEnd_3213262 : Nat := 549982624942504110449161

theorem tailTrace_3213262 : CollatzResearch.WordTrace tailWord_3213262 prefixEnd_3213262 549982624942504110449161 := by
  unfold tailWord_3213262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14649661660613503787998255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78131528856605353535990693 14649661660613503787998255)
  ·
    refine ⟨21974492490920255681997383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14649661660613503787998255 21974492490920255681997383)
    ·
      refine ⟨32961738736380383522996075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21974492490920255681997383 32961738736380383522996075)
      ·
        refine ⟨49442608104570575284494113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32961738736380383522996075 49442608104570575284494113)
        ·
          refine ⟨37081956078427931463370585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49442608104570575284494113 37081956078427931463370585)
          ·
            refine ⟨27811467058820948597527939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37081956078427931463370585 27811467058820948597527939)
            ·
              refine ⟨41717200588231422896291909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27811467058820948597527939 41717200588231422896291909)
              ·
                refine ⟨7821975110293391793054733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41717200588231422896291909 7821975110293391793054733)
                ·
                  refine ⟨2933240666360021922395525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7821975110293391793054733 2933240666360021922395525)
                  ·
                    refine ⟨549982624942504110449161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2933240666360021922395525 549982624942504110449161)
                    ·
                      rfl

theorem cell23_3213262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3213262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213262 prefixEnd_3213262 := by exact prefixLift 3213262
  have htrace : WordTrace (prefixWord ++ tailWord_3213262) baseStart_3213262 baseEnd_3213262 := by
    simpa [prefixWord, tailWord_3213262, baseEnd_3213262] using wordTrace_append hprefix tailTrace_3213262
  have hstable : (prefixWord ++ tailWord_3213262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213262).length < 2 ^ (prefixWord ++ tailWord_3213262).sum := by decide
  have hdescent : baseEnd_3213262 < baseStart_3213262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213272 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3213272 : Nat := 118140960795 + 3213272 * 2 ^ 59
def prefixEnd_3213272 : Nat := 4983230072969 + 3 ^ 40 * 3213272 * 2
def baseEnd_3213272 : Nat := 1649953009634057292222437

theorem tailTrace_3213272 : CollatzResearch.WordTrace tailWord_3213272 prefixEnd_3213272 1649953009634057292222437 := by
  unfold tailWord_3213272
  simp only [CollatzResearch.WordTrace]
  refine ⟨58598829007435901005925035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78131772009914534674566713 58598829007435901005925035)
  ·
    refine ⟨87898243511153851508887553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58598829007435901005925035 87898243511153851508887553)
    ·
      refine ⟨65923682633365388631665665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87898243511153851508887553 65923682633365388631665665)
      ·
        refine ⟨49442761975024041473749249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65923682633365388631665665 49442761975024041473749249)
        ·
          refine ⟨37082071481268031105311937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49442761975024041473749249 37082071481268031105311937)
          ·
            refine ⟨27811553610951023328983953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37082071481268031105311937 27811553610951023328983953)
            ·
              refine ⟨20858665208213267496737965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27811553610951023328983953 20858665208213267496737965)
              ·
                refine ⟨7821999453079975311276737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20858665208213267496737965 7821999453079975311276737)
                ·
                  refine ⟨5866499589809981483457553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7821999453079975311276737 5866499589809981483457553)
                  ·
                    refine ⟨4399874692357486112593165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5866499589809981483457553 4399874692357486112593165)
                    ·
                      refine ⟨1649953009634057292222437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4399874692357486112593165 1649953009634057292222437)
                      ·
                        rfl

theorem cell23_3213272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3213272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213272 prefixEnd_3213272 := by exact prefixLift 3213272
  have htrace : WordTrace (prefixWord ++ tailWord_3213272) baseStart_3213272 baseEnd_3213272 := by
    simpa [prefixWord, tailWord_3213272, baseEnd_3213272] using wordTrace_append hprefix tailTrace_3213272
  have hstable : (prefixWord ++ tailWord_3213272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213272).length < 2 ^ (prefixWord ++ tailWord_3213272).sum := by decide
  have hdescent : baseEnd_3213272 < baseStart_3213272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213312 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 1, 5, 2]
def baseStart_3213312 : Nat := 118140960795 + 3213312 * 2 ^ 59
def prefixEnd_3213312 : Nat := 4983230072969 + 3 ^ 40 * 3213312 * 2
def baseEnd_3213312 : Nat := 1649973548860237135722253

theorem tailTrace_3213312 : CollatzResearch.WordTrace tailWord_3213312 prefixEnd_3213312 1649973548860237135722253 := by
  unfold tailWord_3213312
  simp only [CollatzResearch.WordTrace]
  refine ⟨58599558467363444421653095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78132744623151259228870793 58599558467363444421653095)
  ·
    refine ⟨87899337701045166632479643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58599558467363444421653095 87899337701045166632479643)
    ·
      refine ⟨131849006551567749948719465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87899337701045166632479643 131849006551567749948719465)
      ·
        refine ⟨98886754913675812461539599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131849006551567749948719465 98886754913675812461539599)
        ·
          refine ⟨148330132370513718692309399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98886754913675812461539599 148330132370513718692309399)
          ·
            refine ⟨222495198555770578038464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148330132370513718692309399 222495198555770578038464099)
            ·
              refine ⟨333742797833655867057696149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222495198555770578038464099 333742797833655867057696149)
              ·
                refine ⟨15644193648452618768329507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333742797833655867057696149 15644193648452618768329507)
                ·
                  refine ⟨23466290472678928152494261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15644193648452618768329507 23466290472678928152494261)
                  ·
                    refine ⟨2199964731813649514296337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23466290472678928152494261 2199964731813649514296337)
                    ·
                      refine ⟨1649973548860237135722253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2199964731813649514296337 1649973548860237135722253)
                      ·
                        rfl

theorem cell23_3213312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_3213312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213312 prefixEnd_3213312 := by exact prefixLift 3213312
  have htrace : WordTrace (prefixWord ++ tailWord_3213312) baseStart_3213312 baseEnd_3213312 := by
    simpa [prefixWord, tailWord_3213312, baseEnd_3213312] using wordTrace_append hprefix tailTrace_3213312
  have hstable : (prefixWord ++ tailWord_3213312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213312).length < 2 ^ (prefixWord ++ tailWord_3213312).sum := by decide
  have hdescent : baseEnd_3213312 < baseStart_3213312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213336 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 1, 1, 3]
def baseStart_3213336 : Nat := 118140960795 + 3213336 * 2 ^ 59
def prefixEnd_3213336 : Nat := 4983230072969 + 3 ^ 40 * 3213336 * 2
def baseEnd_3213336 : Nat := 1649985872395945041822143

theorem tailTrace_3213336 : CollatzResearch.WordTrace tailWord_3213336 prefixEnd_3213336 1649985872395945041822143 := by
  unfold tailWord_3213336
  simp only [CollatzResearch.WordTrace]
  refine ⟨58599996143319970471089931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78133328191093293961453241 58599996143319970471089931)
  ·
    refine ⟨87899994214979955706634897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58599996143319970471089931 87899994214979955706634897)
    ·
      refine ⟨65924995661234966779976173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87899994214979955706634897 65924995661234966779976173)
      ·
        refine ⟨24721873372963112542491065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65924995661234966779976173 24721873372963112542491065)
        ·
          refine ⟨18541405029722334406868299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24721873372963112542491065 18541405029722334406868299)
          ·
            refine ⟨27812107544583501610302449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541405029722334406868299 27812107544583501610302449)
            ·
              refine ⟨20859080658437626207726837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27812107544583501610302449 20859080658437626207726837)
              ·
                refine ⟨1955538811728527456974391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20859080658437626207726837 1955538811728527456974391)
                ·
                  refine ⟨2933308217592791185461587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955538811728527456974391 2933308217592791185461587)
                  ·
                    refine ⟨4399962326389186778192381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2933308217592791185461587 4399962326389186778192381)
                    ·
                      refine ⟨1649985872395945041822143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4399962326389186778192381 1649985872395945041822143)
                      ·
                        rfl

theorem cell23_3213336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_3213336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213336 prefixEnd_3213336 := by exact prefixLift 3213336
  have htrace : WordTrace (prefixWord ++ tailWord_3213336) baseStart_3213336 baseEnd_3213336 := by
    simpa [prefixWord, tailWord_3213336, baseEnd_3213336] using wordTrace_append hprefix tailTrace_3213336
  have hstable : (prefixWord ++ tailWord_3213336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213336).length < 2 ^ (prefixWord ++ tailWord_3213336).sum := by decide
  have hdescent : baseEnd_3213336 < baseStart_3213336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213355 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6]
def baseStart_3213355 : Nat := 118140960795 + 3213355 * 2 ^ 59
def prefixEnd_3213355 : Nat := 4983230072969 + 3 ^ 40 * 3213355 * 2
def baseEnd_3213355 : Nat := 1649995628528380467484555

theorem tailTrace_3213355 : CollatzResearch.WordTrace tailWord_3213355 prefixEnd_3213355 1649995628528380467484555 := by
  unfold tailWord_3213355
  simp only [CollatzResearch.WordTrace]
  refine ⟨117200685273571107187121519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78133790182380738124747679 117200685273571107187121519)
  ·
    refine ⟨175801027910356660780682279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117200685273571107187121519 175801027910356660780682279)
    ·
      refine ⟨263701541865534991171023419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175801027910356660780682279 263701541865534991171023419)
      ·
        refine ⟨395552312798302486756535129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263701541865534991171023419 395552312798302486756535129)
        ·
          refine ⟨296664234598726865067401347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395552312798302486756535129 296664234598726865067401347)
          ·
            refine ⟨444996351898090297601102021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296664234598726865067401347 444996351898090297601102021)
            ·
              refine ⟨83436815980891930800206629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 444996351898090297601102021 83436815980891930800206629)
              ·
                refine ⟨15644402996417237025038743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83436815980891930800206629 15644402996417237025038743)
                ·
                  refine ⟨23466604494625855537558115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15644402996417237025038743 23466604494625855537558115)
                  ·
                    refine ⟨35199906741938783306337173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23466604494625855537558115 35199906741938783306337173)
                    ·
                      refine ⟨1649995628528380467484555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35199906741938783306337173 1649995628528380467484555)
                      ·
                        rfl

theorem cell23_3213355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_3213355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213355 prefixEnd_3213355 := by exact prefixLift 3213355
  have htrace : WordTrace (prefixWord ++ tailWord_3213355) baseStart_3213355 baseEnd_3213355 := by
    simpa [prefixWord, tailWord_3213355, baseEnd_3213355] using wordTrace_append hprefix tailTrace_3213355
  have hstable : (prefixWord ++ tailWord_3213355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213355).length < 2 ^ (prefixWord ++ tailWord_3213355).sum := by decide
  have hdescent : baseEnd_3213355 < baseStart_3213355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213369 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 1, 6]
def baseStart_3213369 : Nat := 118140960795 + 3213369 * 2 ^ 59
def prefixEnd_3213369 : Nat := 4983230072969 + 3 ^ 40 * 3213369 * 2
def baseEnd_3213369 : Nat := 550000939085847804236497

theorem tailTrace_3213369 : CollatzResearch.WordTrace tailWord_3213369 prefixEnd_3213369 550000939085847804236497 := by
  unfold tailWord_3213369
  simp only [CollatzResearch.WordTrace]
  refine ⟨117201195895520387578131161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78134130597013591718754107 117201195895520387578131161)
  ·
    refine ⟨87900896921640290683598371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117201195895520387578131161 87900896921640290683598371)
    ·
      refine ⟨131851345382460436025397557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87900896921640290683598371 131851345382460436025397557)
      ·
        refine ⟨12361063629605665877381021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131851345382460436025397557 12361063629605665877381021)
        ·
          refine ⟨4635398861102124704017883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12361063629605665877381021 4635398861102124704017883)
          ·
            refine ⟨6953098291653187056026825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635398861102124704017883 6953098291653187056026825)
            ·
              refine ⟨5214823718739890292020119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6953098291653187056026825 5214823718739890292020119)
              ·
                refine ⟨7822235578109835438030179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5214823718739890292020119 7822235578109835438030179)
                ·
                  refine ⟨11733353367164753157045269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7822235578109835438030179 11733353367164753157045269)
                  ·
                    refine ⟨550000939085847804236497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11733353367164753157045269 550000939085847804236497)
                    ·
                      rfl

theorem cell23_3213369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_3213369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213369 prefixEnd_3213369 := by exact prefixLift 3213369
  have htrace : WordTrace (prefixWord ++ tailWord_3213369) baseStart_3213369 baseEnd_3213369 := by
    simpa [prefixWord, tailWord_3213369, baseEnd_3213369] using wordTrace_append hprefix tailTrace_3213369
  have hstable : (prefixWord ++ tailWord_3213369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213369).length < 2 ^ (prefixWord ++ tailWord_3213369).sum := by decide
  have hdescent : baseEnd_3213369 < baseStart_3213369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213376 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 3, 2, 2]
def baseStart_3213376 : Nat := 118140960795 + 3213376 * 2 ^ 59
def prefixEnd_3213376 : Nat := 4983230072969 + 3 ^ 40 * 3213376 * 2
def baseEnd_3213376 : Nat := 1650006411622124885321959

theorem tailTrace_3213376 : CollatzResearch.WordTrace tailWord_3213376 prefixEnd_3213376 1650006411622124885321959 := by
  unfold tailWord_3213376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58600725603247513886817991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78134300804330018515757321 58600725603247513886817991)
  ·
    refine ⟨87901088404871270830226987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58600725603247513886817991 87901088404871270830226987)
    ·
      refine ⟨131851632607306906245340481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87901088404871270830226987 131851632607306906245340481)
      ·
        refine ⟨98888724455480179684005361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131851632607306906245340481 98888724455480179684005361)
        ·
          refine ⟨74166543341610134763004021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98888724455480179684005361 74166543341610134763004021)
          ·
            refine ⟨6953113438275950134031627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74166543341610134763004021 6953113438275950134031627)
            ·
              refine ⟨10429670157413925201047441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953113438275950134031627 10429670157413925201047441)
              ·
                refine ⟨7822252618060443900785581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10429670157413925201047441 7822252618060443900785581)
                ·
                  refine ⟨2933344731772666462794593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7822252618060443900785581 2933344731772666462794593)
                  ·
                    refine ⟨2200008548829499847095945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933344731772666462794593 2200008548829499847095945)
                    ·
                      refine ⟨1650006411622124885321959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200008548829499847095945 1650006411622124885321959)
                      ·
                        rfl

theorem cell23_3213376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_3213376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213376 prefixEnd_3213376 := by exact prefixLift 3213376
  have htrace : WordTrace (prefixWord ++ tailWord_3213376) baseStart_3213376 baseEnd_3213376 := by
    simpa [prefixWord, tailWord_3213376, baseEnd_3213376] using wordTrace_append hprefix tailTrace_3213376
  have hstable : (prefixWord ++ tailWord_3213376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213376).length < 2 ^ (prefixWord ++ tailWord_3213376).sum := by decide
  have hdescent : baseEnd_3213376 < baseStart_3213376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213389 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3213389 : Nat := 118140960795 + 3213389 * 2 ^ 59
def prefixEnd_3213389 : Nat := 4983230072969 + 3 ^ 40 * 3213389 * 2
def baseEnd_3213389 : Nat := 1650013086870633334459399

theorem tailTrace_3213389 : CollatzResearch.WordTrace tailWord_3213389 prefixEnd_3213389 1650013086870633334459399 := by
  unfold tailWord_3213389
  simp only [CollatzResearch.WordTrace]
  refine ⟨117201925355447930993859221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78134616903631953995906147 117201925355447930993859221)
  ·
    refine ⟨5493840251036621765337151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117201925355447930993859221 5493840251036621765337151)
    ·
      refine ⟨8240760376554932648005727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493840251036621765337151 8240760376554932648005727)
      ·
        refine ⟨12361140564832398972008591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240760376554932648005727 12361140564832398972008591)
        ·
          refine ⟨18541710847248598458012887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12361140564832398972008591 18541710847248598458012887)
          ·
            refine ⟨27812566270872897687019331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541710847248598458012887 27812566270872897687019331)
            ·
              refine ⟨41718849406309346530528997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27812566270872897687019331 41718849406309346530528997)
              ·
                refine ⟨7822284263683002474474187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41718849406309346530528997 7822284263683002474474187)
                ·
                  refine ⟨11733426395524503711711281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7822284263683002474474187 11733426395524503711711281)
                  ·
                    refine ⟨8800069796643377783783461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11733426395524503711711281 8800069796643377783783461)
                    ·
                      refine ⟨1650013086870633334459399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8800069796643377783783461 1650013086870633334459399)
                      ·
                        rfl

theorem cell23_3213389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3213389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213389 prefixEnd_3213389 := by exact prefixLift 3213389
  have htrace : WordTrace (prefixWord ++ tailWord_3213389) baseStart_3213389 baseEnd_3213389 := by
    simpa [prefixWord, tailWord_3213389, baseEnd_3213389] using wordTrace_append hprefix tailTrace_3213389
  have hstable : (prefixWord ++ tailWord_3213389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213389).length < 2 ^ (prefixWord ++ tailWord_3213389).sum := by decide
  have hdescent : baseEnd_3213389 < baseStart_3213389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213410 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3213410 : Nat := 118140960795 + 3213410 * 2 ^ 59
def prefixEnd_3213410 : Nat := 4983230072969 + 3 ^ 40 * 3213410 * 2
def baseEnd_3213410 : Nat := 1650023869964377752296803

theorem tailTrace_3213410 : CollatzResearch.WordTrace tailWord_3213410 prefixEnd_3213410 1650023869964377752296803 := by
  unfold tailWord_3213410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29300672822092962895093421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78135127525581234386915789 29300672822092962895093421)
  ·
    refine ⟨10987752308284861085660033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29300672822092962895093421 10987752308284861085660033)
    ·
      refine ⟨8240814231213645814245025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10987752308284861085660033 8240814231213645814245025)
      ·
        refine ⟨6180610673410234360683769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8240814231213645814245025 6180610673410234360683769)
        ·
          refine ⟨4635458005057675770512827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6180610673410234360683769 4635458005057675770512827)
          ·
            refine ⟨6953187007586513655769241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635458005057675770512827 6953187007586513655769241)
            ·
              refine ⟨5214890255689885241826931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6953187007586513655769241 5214890255689885241826931)
              ·
                refine ⟨7822335383534827862740397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5214890255689885241826931 7822335383534827862740397)
                ·
                  refine ⟨2933375768825560448527649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7822335383534827862740397 2933375768825560448527649)
                  ·
                    refine ⟨2200031826619170336395737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933375768825560448527649 2200031826619170336395737)
                    ·
                      refine ⟨1650023869964377752296803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200031826619170336395737 1650023869964377752296803)
                      ·
                        rfl

theorem cell23_3213410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3213410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213410 prefixEnd_3213410 := by exact prefixLift 3213410
  have htrace : WordTrace (prefixWord ++ tailWord_3213410) baseStart_3213410 baseEnd_3213410 := by
    simpa [prefixWord, tailWord_3213410, baseEnd_3213410] using wordTrace_append hprefix tailTrace_3213410
  have hstable : (prefixWord ++ tailWord_3213410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213410).length < 2 ^ (prefixWord ++ tailWord_3213410).sum := by decide
  have hdescent : baseEnd_3213410 < baseStart_3213410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213426 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3213426 : Nat := 118140960795 + 3213426 * 2 ^ 59
def prefixEnd_3213426 : Nat := 4983230072969 + 3 ^ 40 * 3213426 * 2
def baseEnd_3213426 : Nat := 1650032085654849689696729

theorem tailTrace_3213426 : CollatzResearch.WordTrace tailWord_3213426 prefixEnd_3213426 1650032085654849689696729 := by
  unfold tailWord_3213426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29300818714078471578239033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78135516570875924208637421 29300818714078471578239033)
  ·
    refine ⟨21975614035558853683679275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29300818714078471578239033 21975614035558853683679275)
    ·
      refine ⟨32963421053338280525518913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21975614035558853683679275 32963421053338280525518913)
      ·
        refine ⟨24722565790003710394139185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32963421053338280525518913 24722565790003710394139185)
        ·
          refine ⟨18541924342502782795604389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24722565790003710394139185 18541924342502782795604389)
          ·
            refine ⟨3476610814219271774175823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18541924342502782795604389 3476610814219271774175823)
            ·
              refine ⟨5214916221328907661263735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476610814219271774175823 5214916221328907661263735)
              ·
                refine ⟨7822374331993361491895603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5214916221328907661263735 7822374331993361491895603)
                ·
                  refine ⟨11733561497990042237843405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7822374331993361491895603 11733561497990042237843405)
                  ·
                    refine ⟨4400085561746265839191277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11733561497990042237843405 4400085561746265839191277)
                    ·
                      refine ⟨1650032085654849689696729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4400085561746265839191277 1650032085654849689696729)
                      ·
                        rfl

theorem cell23_3213426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3213426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213426 prefixEnd_3213426 := by exact prefixLift 3213426
  have htrace : WordTrace (prefixWord ++ tailWord_3213426) baseStart_3213426 baseEnd_3213426 := by
    simpa [prefixWord, tailWord_3213426, baseEnd_3213426] using wordTrace_append hprefix tailTrace_3213426
  have hstable : (prefixWord ++ tailWord_3213426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213426).length < 2 ^ (prefixWord ++ tailWord_3213426).sum := by decide
  have hdescent : baseEnd_3213426 < baseStart_3213426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213436 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_3213436 : Nat := 118140960795 + 3213436 * 2 ^ 59
def prefixEnd_3213436 : Nat := 4983230072969 + 3 ^ 40 * 3213436 * 2
def baseEnd_3213436 : Nat := 1650037220461394650571683

theorem tailTrace_3213436 : CollatzResearch.WordTrace tailWord_3213436 prefixEnd_3213436 1650037220461394650571683 := by
  unfold tailWord_3213436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58601819793138829010410081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78135759724185105347213441 58601819793138829010410081)
  ·
    refine ⟨43951364844854121757807561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58601819793138829010410081 43951364844854121757807561)
    ·
      refine ⟨32963523633640591318355671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43951364844854121757807561 32963523633640591318355671)
      ·
        refine ⟨49445285450460886977533507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32963523633640591318355671 49445285450460886977533507)
        ·
          refine ⟨74167928175691330466300261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49445285450460886977533507 74167928175691330466300261)
          ·
            refine ⟨13906486532942124462431299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74167928175691330466300261 13906486532942124462431299)
            ·
              refine ⟨20859729799413186693646949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13906486532942124462431299 20859729799413186693646949)
              ·
                refine ⟨3911199337389972505058803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20859729799413186693646949 3911199337389972505058803)
                ·
                  refine ⟨5866799006084958757588205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911199337389972505058803 5866799006084958757588205)
                  ·
                    refine ⟨2200049627281859534095577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5866799006084958757588205 2200049627281859534095577)
                    ·
                      refine ⟨1650037220461394650571683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200049627281859534095577 1650037220461394650571683)
                      ·
                        rfl

theorem cell23_3213436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_3213436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213436 prefixEnd_3213436 := by exact prefixLift 3213436
  have htrace : WordTrace (prefixWord ++ tailWord_3213436) baseStart_3213436 baseEnd_3213436 := by
    simpa [prefixWord, tailWord_3213436, baseEnd_3213436] using wordTrace_append hprefix tailTrace_3213436
  have hstable : (prefixWord ++ tailWord_3213436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213436).length < 2 ^ (prefixWord ++ tailWord_3213436).sum := by decide
  have hdescent : baseEnd_3213436 < baseStart_3213436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213449 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 3, 4, 2]
def baseStart_3213449 : Nat := 118140960795 + 3213449 * 2 ^ 59
def prefixEnd_3213449 : Nat := 4983230072969 + 3 ^ 40 * 3213449 * 2
def baseEnd_3213449 : Nat := 1650043895709903099709123

theorem tailTrace_3213449 : CollatzResearch.WordTrace tailWord_3213449 prefixEnd_3213449 1650043895709903099709123 := by
  unfold tailWord_3213449
  simp only [CollatzResearch.WordTrace]
  refine ⟨117204113735230561241043401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78136075823487040827362267 117204113735230561241043401)
  ·
    refine ⟨87903085301422920930782551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117204113735230561241043401 87903085301422920930782551)
    ·
      refine ⟨131854627952134381396173827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87903085301422920930782551 131854627952134381396173827)
      ·
        refine ⟨197781941928201572094260741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131854627952134381396173827 197781941928201572094260741)
        ·
          refine ⟨37084114111537794767673889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197781941928201572094260741 37084114111537794767673889)
          ·
            refine ⟨27813085583653346075755417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37084114111537794767673889 27813085583653346075755417)
            ·
              refine ⟨20859814187740009556816563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27813085583653346075755417 20859814187740009556816563)
              ·
                refine ⟨31289721281610014335224845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20859814187740009556816563 31289721281610014335224845)
                ·
                  refine ⟨11733645480603755375709317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31289721281610014335224845 11733645480603755375709317)
                  ·
                    refine ⟨2200058527613204132945497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11733645480603755375709317 2200058527613204132945497)
                    ·
                      refine ⟨1650043895709903099709123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200058527613204132945497 1650043895709903099709123)
                      ·
                        rfl

theorem cell23_3213449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 4, 2].length) (baseStart_3213449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213449 prefixEnd_3213449 := by exact prefixLift 3213449
  have htrace : WordTrace (prefixWord ++ tailWord_3213449) baseStart_3213449 baseEnd_3213449 := by
    simpa [prefixWord, tailWord_3213449, baseEnd_3213449] using wordTrace_append hprefix tailTrace_3213449
  have hstable : (prefixWord ++ tailWord_3213449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213449).length < 2 ^ (prefixWord ++ tailWord_3213449).sum := by decide
  have hdescent : baseEnd_3213449 < baseStart_3213449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213452 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3213452 : Nat := 118140960795 + 3213452 * 2 ^ 59
def prefixEnd_3213452 : Nat := 4983230072969 + 3 ^ 40 * 3213452 * 2
def baseEnd_3213452 : Nat := 1650045436151866587971609

theorem tailTrace_3213452 : CollatzResearch.WordTrace tailWord_3213452 prefixEnd_3213452 1650045436151866587971609 := by
  unfold tailWord_3213452
  simp only [CollatzResearch.WordTrace]
  refine ⟨58602111577109846376701305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78136148769479795168935073 58602111577109846376701305)
  ·
    refine ⟨43951583682832384782525979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58602111577109846376701305 43951583682832384782525979)
    ·
      refine ⟨65927375524248577173788969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43951583682832384782525979 65927375524248577173788969)
      ·
        refine ⟨49445531643186432880341727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65927375524248577173788969 49445531643186432880341727)
        ·
          refine ⟨74168297464779649320512591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49445531643186432880341727 74168297464779649320512591)
          ·
            refine ⟨111252446197169473980768887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74168297464779649320512591 111252446197169473980768887)
            ·
              refine ⟨166878669295754210971153331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111252446197169473980768887 166878669295754210971153331)
              ·
                refine ⟨250318003943631316456729997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166878669295754210971153331 250318003943631316456729997)
                ·
                  refine ⟨93869251478861743671273749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250318003943631316456729997 93869251478861743671273749)
                  ·
                    refine ⟨4400121163071644234590957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93869251478861743671273749 4400121163071644234590957)
                    ·
                      refine ⟨1650045436151866587971609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4400121163071644234590957 1650045436151866587971609)
                      ·
                        rfl

theorem cell23_3213452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3213452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213452 prefixEnd_3213452 := by exact prefixLift 3213452
  have htrace : WordTrace (prefixWord ++ tailWord_3213452) baseStart_3213452 baseEnd_3213452 := by
    simpa [prefixWord, tailWord_3213452, baseEnd_3213452] using wordTrace_append hprefix tailTrace_3213452
  have hstable : (prefixWord ++ tailWord_3213452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213452).length < 2 ^ (prefixWord ++ tailWord_3213452).sum := by decide
  have hdescent : baseEnd_3213452 < baseStart_3213452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213552 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_3213552 : Nat := 118140960795 + 3213552 * 2 ^ 59
def prefixEnd_3213552 : Nat := 4983230072969 + 3 ^ 40 * 3213552 * 2
def baseEnd_3213552 : Nat := 1650096784217316196721149

theorem tailTrace_3213552 : CollatzResearch.WordTrace tailWord_3213552 prefixEnd_3213552 1650096784217316196721149 := by
  unfold tailWord_3213552
  simp only [CollatzResearch.WordTrace]
  refine ⟨58603935226928704916021455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78138580302571606554695273 58603935226928704916021455)
  ·
    refine ⟨87905902840393057374032183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58603935226928704916021455 87905902840393057374032183)
    ·
      refine ⟨131858854260589586061048275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87905902840393057374032183 131858854260589586061048275)
      ·
        refine ⟨197788281390884379091572413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131858854260589586061048275 197788281390884379091572413)
        ·
          refine ⟨74170605521581642159339655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197788281390884379091572413 74170605521581642159339655)
          ·
            refine ⟨111255908282372463239009483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74170605521581642159339655 111255908282372463239009483)
            ·
              refine ⟨166883862423558694858514225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111255908282372463239009483 166883862423558694858514225)
              ·
                refine ⟨125162896817669021143885669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166883862423558694858514225 125162896817669021143885669)
                ·
                  refine ⟨23468043153312941464478563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125162896817669021143885669 23468043153312941464478563)
                  ·
                    refine ⟨35202064729969412196717845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23468043153312941464478563 35202064729969412196717845)
                    ·
                      refine ⟨1650096784217316196721149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35202064729969412196717845 1650096784217316196721149)
                      ·
                        rfl

theorem cell23_3213552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_3213552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213552 prefixEnd_3213552 := by exact prefixLift 3213552
  have htrace : WordTrace (prefixWord ++ tailWord_3213552) baseStart_3213552 baseEnd_3213552 := by
    simpa [prefixWord, tailWord_3213552, baseEnd_3213552] using wordTrace_append hprefix tailTrace_3213552
  have hstable : (prefixWord ++ tailWord_3213552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213552).length < 2 ^ (prefixWord ++ tailWord_3213552).sum := by decide
  have hdescent : baseEnd_3213552 < baseStart_3213552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213566 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3213566 : Nat := 118140960795 + 3213566 * 2 ^ 59
def prefixEnd_3213566 : Nat := 4983230072969 + 3 ^ 40 * 3213566 * 2
def baseEnd_3213566 : Nat := 550034657648826380648695

theorem tailTrace_3213566 : CollatzResearch.WordTrace tailWord_3213566 prefixEnd_3213566 550034657648826380648695 := by
  unfold tailWord_3213566
  simp only [CollatzResearch.WordTrace]
  refine ⟨14651047634475836277881569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78138920717204460148701701 14651047634475836277881569)
  ·
    refine ⟨10988285725856877208411177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14651047634475836277881569 10988285725856877208411177)
    ·
      refine ⟨8241214294392657906308383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10988285725856877208411177 8241214294392657906308383)
      ·
        refine ⟨12361821441588986859462575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8241214294392657906308383 12361821441588986859462575)
        ·
          refine ⟨18542732162383480289193863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12361821441588986859462575 18542732162383480289193863)
          ·
            refine ⟨27814098243575220433790795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18542732162383480289193863 27814098243575220433790795)
            ·
              refine ⟨41721147365362830650686193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27814098243575220433790795 41721147365362830650686193)
              ·
                refine ⟨31290860524022122988014645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41721147365362830650686193 31290860524022122988014645)
                ·
                  refine ⟨2933518174127074030126373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31290860524022122988014645 2933518174127074030126373)
                  ·
                    refine ⟨550034657648826380648695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2933518174127074030126373 550034657648826380648695)
                    ·
                      rfl

theorem cell23_3213566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3213566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213566 prefixEnd_3213566 := by exact prefixLift 3213566
  have htrace : WordTrace (prefixWord ++ tailWord_3213566) baseStart_3213566 baseEnd_3213566 := by
    simpa [prefixWord, tailWord_3213566, baseEnd_3213566] using wordTrace_append hprefix tailTrace_3213566
  have hstable : (prefixWord ++ tailWord_3213566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213566).length < 2 ^ (prefixWord ++ tailWord_3213566).sum := by decide
  have hdescent : baseEnd_3213566 < baseStart_3213566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213617 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 1, 4]
def baseStart_3213617 : Nat := 118140960795 + 3213617 * 2 ^ 59
def prefixEnd_3213617 : Nat := 4983230072969 + 3 ^ 40 * 3213617 * 2
def baseEnd_3213617 : Nat := 550043386819952814136117

theorem tailTrace_3213617 : CollatzResearch.WordTrace tailWord_3213617 prefixEnd_3213617 550043386819952814136117 := by
  unfold tailWord_3213617
  simp only [CollatzResearch.WordTrace]
  refine ⟨117210241198621925933159105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78140160799081283955439403 117210241198621925933159105)
  ·
    refine ⟨87907680898966444449869329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117210241198621925933159105 87907680898966444449869329)
    ·
      refine ⟨65930760674224833337401997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87907680898966444449869329 65930760674224833337401997)
      ·
        refine ⟨24724035252834312501525749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65930760674224833337401997 24724035252834312501525749)
        ·
          refine ⟨2317878304953216797018039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24724035252834312501525749 2317878304953216797018039)
          ·
            refine ⟨3476817457429825195527059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317878304953216797018039 3476817457429825195527059)
            ·
              refine ⟨5215226186144737793290589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476817457429825195527059 5215226186144737793290589)
              ·
                refine ⟨1955709819804276672483971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5215226186144737793290589 1955709819804276672483971)
                ·
                  refine ⟨2933564729706415008725957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955709819804276672483971 2933564729706415008725957)
                  ·
                    refine ⟨550043386819952814136117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2933564729706415008725957 550043386819952814136117)
                    ·
                      rfl

theorem cell23_3213617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_3213617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213617 prefixEnd_3213617 := by exact prefixLift 3213617
  have htrace : WordTrace (prefixWord ++ tailWord_3213617) baseStart_3213617 baseEnd_3213617 := by
    simpa [prefixWord, tailWord_3213617, baseEnd_3213617] using wordTrace_append hprefix tailTrace_3213617
  have hstable : (prefixWord ++ tailWord_3213617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213617).length < 2 ^ (prefixWord ++ tailWord_3213617).sum := by decide
  have hdescent : baseEnd_3213617 < baseStart_3213617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213626 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_3213626 : Nat := 118140960795 + 3213626 * 2 ^ 59
def prefixEnd_3213626 : Nat := 4983230072969 + 3 ^ 40 * 3213626 * 2
def baseEnd_3213626 : Nat := 550044927261916302398603

theorem tailTrace_3213626 : CollatzResearch.WordTrace tailWord_3213626 prefixEnd_3213626 550044927261916302398603 := by
  unfold tailWord_3213626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29302642363897330117559183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78140379637059546980157821 29302642363897330117559183)
  ·
    refine ⟨43953963545845995176338775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29302642363897330117559183 43953963545845995176338775)
    ·
      refine ⟨65930945318768992764508163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43953963545845995176338775 65930945318768992764508163)
      ·
        refine ⟨98896417978153489146762245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65930945318768992764508163 98896417978153489146762245)
        ·
          refine ⟨18543078370903779215017921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98896417978153489146762245 18543078370903779215017921)
          ·
            refine ⟨13907308778177834411263441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18543078370903779215017921 13907308778177834411263441)
            ·
              refine ⟨10430481583633375808447581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13907308778177834411263441 10430481583633375808447581)
              ·
                refine ⟨3911430593862515928167843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10430481583633375808447581 3911430593862515928167843)
                ·
                  refine ⟨5867145890793773892251765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911430593862515928167843 5867145890793773892251765)
                  ·
                    refine ⟨550044927261916302398603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5867145890793773892251765 550044927261916302398603)
                    ·
                      rfl

theorem cell23_3213626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_3213626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213626 prefixEnd_3213626 := by exact prefixLift 3213626
  have htrace : WordTrace (prefixWord ++ tailWord_3213626) baseStart_3213626 baseEnd_3213626 := by
    simpa [prefixWord, tailWord_3213626, baseEnd_3213626] using wordTrace_append hprefix tailTrace_3213626
  have hstable : (prefixWord ++ tailWord_3213626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213626).length < 2 ^ (prefixWord ++ tailWord_3213626).sum := by decide
  have hdescent : baseEnd_3213626 < baseStart_3213626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213646 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_3213646 : Nat := 118140960795 + 3213646 * 2 ^ 59
def prefixEnd_3213646 : Nat := 4983230072969 + 3 ^ 40 * 3213646 * 2
def baseEnd_3213646 : Nat := 1650145051398838828945717

theorem tailTrace_3213646 : CollatzResearch.WordTrace tailWord_3213646 prefixEnd_3213646 1650145051398838828945717 := by
  unfold tailWord_3213646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14651412364439607985745599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78140865943677909257309861 14651412364439607985745599)
  ·
    refine ⟨21977118546659411978618399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14651412364439607985745599 21977118546659411978618399)
    ·
      refine ⟨32965677819989117967927599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21977118546659411978618399 32965677819989117967927599)
      ·
        refine ⟨49448516729983676951891399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32965677819989117967927599 49448516729983676951891399)
        ·
          refine ⟨74172775094975515427837099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49448516729983676951891399 74172775094975515427837099)
          ·
            refine ⟨111259162642463273141755649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74172775094975515427837099 111259162642463273141755649)
            ·
              refine ⟨83444371981847454856316737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111259162642463273141755649 83444371981847454856316737)
              ·
                refine ⟨62583278986385591142237553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83444371981847454856316737 62583278986385591142237553)
                ·
                  refine ⟨46937459239789193356678165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62583278986385591142237553 46937459239789193356678165)
                  ·
                    refine ⟨2200193401865118438594289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46937459239789193356678165 2200193401865118438594289)
                    ·
                      refine ⟨1650145051398838828945717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200193401865118438594289 1650145051398838828945717)
                      ·
                        rfl

theorem cell23_3213646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_3213646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213646 prefixEnd_3213646 := by exact prefixLift 3213646
  have htrace : WordTrace (prefixWord ++ tailWord_3213646) baseStart_3213646 baseEnd_3213646 := by
    simpa [prefixWord, tailWord_3213646, baseEnd_3213646] using wordTrace_append hprefix tailTrace_3213646
  have hstable : (prefixWord ++ tailWord_3213646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213646).length < 2 ^ (prefixWord ++ tailWord_3213646).sum := by decide
  have hdescent : baseEnd_3213646 < baseStart_3213646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213663 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 3, 2, 2]
def baseStart_3213663 : Nat := 118140960795 + 3213663 * 2 ^ 59
def prefixEnd_3213663 : Nat := 4983230072969 + 3 ^ 40 * 3213663 * 2
def baseEnd_3213663 : Nat := 1650153780569965262433139

theorem tailTrace_3213663 : CollatzResearch.WordTrace tailWord_3213663 prefixEnd_3213663 1650153780569965262433139 := by
  unfold tailWord_3213663
  simp only [CollatzResearch.WordTrace]
  refine ⟨117211918956455275789333643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78141279304303517192889095 117211918956455275789333643)
  ·
    refine ⟨175817878434682913684000465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117211918956455275789333643 175817878434682913684000465)
    ·
      refine ⟨131863408826012185263000349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175817878434682913684000465 131863408826012185263000349)
      ·
        refine ⟨49448778309754569473625131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131863408826012185263000349 49448778309754569473625131)
        ·
          refine ⟨74173167464631854210437697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49448778309754569473625131 74173167464631854210437697)
          ·
            refine ⟨55629875598473890657828273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74173167464631854210437697 55629875598473890657828273)
            ·
              refine ⟨41722406698855417993371205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55629875598473890657828273 41722406698855417993371205)
              ·
                refine ⟨7822951256035390873757101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41722406698855417993371205 7822951256035390873757101)
                ·
                  refine ⟨2933606721013271577658913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7822951256035390873757101 2933606721013271577658913)
                  ·
                    refine ⟨2200205040759953683244185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933606721013271577658913 2200205040759953683244185)
                    ·
                      refine ⟨1650153780569965262433139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200205040759953683244185 1650153780569965262433139)
                      ·
                        rfl

theorem cell23_3213663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_3213663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213663 prefixEnd_3213663 := by exact prefixLift 3213663
  have htrace : WordTrace (prefixWord ++ tailWord_3213663) baseStart_3213663 baseEnd_3213663 := by
    simpa [prefixWord, tailWord_3213663, baseEnd_3213663] using wordTrace_append hprefix tailTrace_3213663
  have hstable : (prefixWord ++ tailWord_3213663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213663).length < 2 ^ (prefixWord ++ tailWord_3213663).sum := by decide
  have hdescent : baseEnd_3213663 < baseStart_3213663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213669 : List Nat := [1, 3, 1, 3, 1, 3, 2, 9]
def baseStart_3213669 : Nat := 118140960795 + 3213669 * 2 ^ 59
def prefixEnd_3213669 : Nat := 4983230072969 + 3 ^ 40 * 3213669 * 2
def baseEnd_3213669 : Nat := 61116920794588601442893

theorem tailTrace_3213669 : CollatzResearch.WordTrace tailWord_3213669 prefixEnd_3213669 61116920794588601442893 := by
  unfold tailWord_3213669
  simp only [CollatzResearch.WordTrace]
  refine ⟨117212137794433538814052061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78141425196289025876034707 117212137794433538814052061)
  ·
    refine ⟨43954551672912577055269523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117212137794433538814052061 43954551672912577055269523)
    ·
      refine ⟨65931827509368865582904285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43954551672912577055269523 65931827509368865582904285)
      ·
        refine ⟨24724435316013324593589107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65931827509368865582904285 24724435316013324593589107)
        ·
          refine ⟨37086652974019986890383661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24724435316013324593589107 37086652974019986890383661)
          ·
            refine ⟨13907494865257495083893873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37086652974019986890383661 13907494865257495083893873)
            ·
              refine ⟨10430621148943121312920405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13907494865257495083893873 10430621148943121312920405)
              ·
                refine ⟨61116920794588601442893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10430621148943121312920405 61116920794588601442893)
                ·
                  rfl

theorem cell23_3213669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 9].length) (baseStart_3213669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213669 prefixEnd_3213669 := by exact prefixLift 3213669
  have htrace : WordTrace (prefixWord ++ tailWord_3213669) baseStart_3213669 baseEnd_3213669 := by
    simpa [prefixWord, tailWord_3213669, baseEnd_3213669] using wordTrace_append hprefix tailTrace_3213669
  have hstable : (prefixWord ++ tailWord_3213669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213669).length < 2 ^ (prefixWord ++ tailWord_3213669).sum := by decide
  have hdescent : baseEnd_3213669 < baseStart_3213669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213686 : List Nat := [5, 1, 1, 4, 12]
def baseStart_3213686 : Nat := 118140960795 + 3213686 * 2 ^ 59
def prefixEnd_3213686 : Nat := 4983230072969 + 3 ^ 40 * 3213686 * 2
def baseEnd_3213686 : Nat := 2263601633230478288677

theorem tailTrace_3213686 : CollatzResearch.WordTrace tailWord_3213686 prefixEnd_3213686 2263601633230478288677 := by
  unfold tailWord_3213686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325797364710746919838807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78141838556914633811613941 7325797364710746919838807)
  ·
    refine ⟨10988696047066120379758211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7325797364710746919838807 10988696047066120379758211)
    ·
      refine ⟨16483044070599180569637317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10988696047066120379758211 16483044070599180569637317)
      ·
        refine ⟨3090570763237346356806997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16483044070599180569637317 3090570763237346356806997)
        ·
          refine ⟨2263601633230478288677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3090570763237346356806997 2263601633230478288677)
          ·
            rfl

theorem cell23_3213686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 12].length) (baseStart_3213686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213686 prefixEnd_3213686 := by exact prefixLift 3213686
  have htrace : WordTrace (prefixWord ++ tailWord_3213686) baseStart_3213686 baseEnd_3213686 := by
    simpa [prefixWord, tailWord_3213686, baseEnd_3213686] using wordTrace_append hprefix tailTrace_3213686
  have hstable : (prefixWord ++ tailWord_3213686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213686).length < 2 ^ (prefixWord ++ tailWord_3213686).sum := by decide
  have hdescent : baseEnd_3213686 < baseStart_3213686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213718 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3213718 : Nat := 118140960795 + 3213718 * 2 ^ 59
def prefixEnd_3213718 : Nat := 4983230072969 + 3 ^ 40 * 3213718 * 2
def baseEnd_3213718 : Nat := 1650182022005962547245387

theorem tailTrace_3213718 : CollatzResearch.WordTrace tailWord_3213718 prefixEnd_3213718 1650182022005962547245387 := by
  unfold tailWord_3213718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325870310703501261411613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78142616647504013455057205 7325870310703501261411613)
  ·
    refine ⟨2747201366513812973029355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7325870310703501261411613 2747201366513812973029355)
    ·
      refine ⟨4120802049770719459544033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747201366513812973029355 4120802049770719459544033)
      ·
        refine ⟨3090601537328039594658025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4120802049770719459544033 3090601537328039594658025)
        ·
          refine ⟨2317951152996029695993519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3090601537328039594658025 2317951152996029695993519)
          ·
            refine ⟨3476926729494044543990279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317951152996029695993519 3476926729494044543990279)
            ·
              refine ⟨5215390094241066815985419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476926729494044543990279 5215390094241066815985419)
              ·
                refine ⟨7823085141361600223978129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215390094241066815985419 7823085141361600223978129)
                ·
                  refine ⟨5867313856021200167983597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823085141361600223978129 5867313856021200167983597)
                  ·
                    refine ⟨2200242696007950062993849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5867313856021200167983597 2200242696007950062993849)
                    ·
                      refine ⟨1650182022005962547245387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200242696007950062993849 1650182022005962547245387)
                      ·
                        rfl

theorem cell23_3213718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3213718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213718 prefixEnd_3213718 := by exact prefixLift 3213718
  have htrace : WordTrace (prefixWord ++ tailWord_3213718) baseStart_3213718 baseEnd_3213718 := by
    simpa [prefixWord, tailWord_3213718, baseEnd_3213718] using wordTrace_append hprefix tailTrace_3213718
  have hstable : (prefixWord ++ tailWord_3213718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213718).length < 2 ^ (prefixWord ++ tailWord_3213718).sum := by decide
  have hdescent : baseEnd_3213718 < baseStart_3213718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213764 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3213764 : Nat := 118140960795 + 3213764 * 2 ^ 59
def prefixEnd_3213764 : Nat := 4983230072969 + 3 ^ 40 * 3213764 * 2
def baseEnd_3213764 : Nat := 1650205642116069367270175

theorem tailTrace_3213764 : CollatzResearch.WordTrace tailWord_3213764 prefixEnd_3213764 1650205642116069367270175 := by
  unfold tailWord_3213764
  simp only [CollatzResearch.WordTrace]
  refine ⟨58607801364544685019380173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78143735152726246692506897 58607801364544685019380173)
  ·
    refine ⟨21977925511704256882267565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58607801364544685019380173 21977925511704256882267565)
    ·
      refine ⟨8241722066889096330850337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21977925511704256882267565 8241722066889096330850337)
      ·
        refine ⟨6181291550166822248137753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8241722066889096330850337 6181291550166822248137753)
        ·
          refine ⟨4635968662625116686103315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6181291550166822248137753 4635968662625116686103315)
          ·
            refine ⟨6953952993937675029154973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635968662625116686103315 6953952993937675029154973)
            ·
              refine ⟨2607732372726628135933115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6953952993937675029154973 2607732372726628135933115)
              ·
                refine ⟨3911598559089942203899673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607732372726628135933115 3911598559089942203899673)
                ·
                  refine ⟨2933698919317456652924755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3911598559089942203899673 2933698919317456652924755)
                  ·
                    refine ⟨4400548378976184979387133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2933698919317456652924755 4400548378976184979387133)
                    ·
                      refine ⟨1650205642116069367270175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4400548378976184979387133 1650205642116069367270175)
                      ·
                        rfl

theorem cell23_3213764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3213764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213764 prefixEnd_3213764 := by exact prefixLift 3213764
  have htrace : WordTrace (prefixWord ++ tailWord_3213764) baseStart_3213764 baseEnd_3213764 := by
    simpa [prefixWord, tailWord_3213764, baseEnd_3213764] using wordTrace_append hprefix tailTrace_3213764
  have hstable : (prefixWord ++ tailWord_3213764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213764).length < 2 ^ (prefixWord ++ tailWord_3213764).sum := by decide
  have hdescent : baseEnd_3213764 < baseStart_3213764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213779 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_3213779 : Nat := 118140960795 + 3213779 * 2 ^ 59
def prefixEnd_3213779 : Nat := 4983230072969 + 3 ^ 40 * 3213779 * 2
def baseEnd_3213779 : Nat := 1650213344325886808582605

theorem tailTrace_3213779 : CollatzResearch.WordTrace tailWord_3213779 prefixEnd_3213779 1650213344325886808582605 := by
  unfold tailWord_3213779
  simp only [CollatzResearch.WordTrace]
  refine ⟨117216149824035027600556391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78144099882690018400370927 117216149824035027600556391)
  ·
    refine ⟨175824224736052541400834587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117216149824035027600556391 175824224736052541400834587)
    ·
      refine ⟨263736337104078812101251881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175824224736052541400834587 263736337104078812101251881)
      ·
        refine ⟨197802252828059109075938911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263736337104078812101251881 197802252828059109075938911)
        ·
          refine ⟨296703379242088663613908367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197802252828059109075938911 296703379242088663613908367)
          ·
            refine ⟨445055068863132995420862551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296703379242088663613908367 445055068863132995420862551)
            ·
              refine ⟨667582603294699493131293827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445055068863132995420862551 667582603294699493131293827)
              ·
                refine ⟨1001373904942049239696940741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667582603294699493131293827 1001373904942049239696940741)
                ·
                  refine ⟨187757607176634232443176389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001373904942049239696940741 187757607176634232443176389)
                  ·
                    refine ⟨35204551345618918583095573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187757607176634232443176389 35204551345618918583095573)
                    ·
                      refine ⟨1650213344325886808582605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35204551345618918583095573 1650213344325886808582605)
                      ·
                        rfl

theorem cell23_3213779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_3213779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213779 prefixEnd_3213779 := by exact prefixLift 3213779
  have htrace : WordTrace (prefixWord ++ tailWord_3213779) baseStart_3213779 baseEnd_3213779 := by
    simpa [prefixWord, tailWord_3213779, baseEnd_3213779] using wordTrace_append hprefix tailTrace_3213779
  have hstable : (prefixWord ++ tailWord_3213779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213779).length < 2 ^ (prefixWord ++ tailWord_3213779).sum := by decide
  have hdescent : baseEnd_3213779 < baseStart_3213779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213810 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_3213810 : Nat := 118140960795 + 3213810 * 2 ^ 59
def prefixEnd_3213810 : Nat := 4983230072969 + 3 ^ 40 * 3213810 * 2
def baseEnd_3213810 : Nat := 183358806914019576366107

theorem tailTrace_3213810 : CollatzResearch.WordTrace tailWord_3213810 prefixEnd_3213810 183358806914019576366107 := by
  unfold tailWord_3213810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29304320121730679973733721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78144853657948479929956589 29304320121730679973733721)
  ·
    refine ⟨21978240091298009980300291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29304320121730679973733721 21978240091298009980300291)
    ·
      refine ⟨32967360136947014970450437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21978240091298009980300291 32967360136947014970450437)
      ·
        refine ⟨6181380025677565306959457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32967360136947014970450437 6181380025677565306959457)
        ·
          refine ⟨4636035019258173980219593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6181380025677565306959457 4636035019258173980219593)
          ·
            refine ⟨3477026264443630485164695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4636035019258173980219593 3477026264443630485164695)
            ·
              refine ⟨5215539396665445727747043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477026264443630485164695 5215539396665445727747043)
              ·
                refine ⟨7823309094998168591620565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215539396665445727747043 7823309094998168591620565)
                ·
                  refine ⟨183358806914019576366107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7823309094998168591620565 183358806914019576366107)
                  ·
                    rfl

theorem cell23_3213810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_3213810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213810 prefixEnd_3213810 := by exact prefixLift 3213810
  have htrace : WordTrace (prefixWord ++ tailWord_3213810) baseStart_3213810 baseEnd_3213810 := by
    simpa [prefixWord, tailWord_3213810, baseEnd_3213810] using wordTrace_append hprefix tailTrace_3213810
  have hstable : (prefixWord ++ tailWord_3213810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213810).length < 2 ^ (prefixWord ++ tailWord_3213810).sum := by decide
  have hdescent : baseEnd_3213810 < baseStart_3213810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213816 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3213816 : Nat := 118140960795 + 3213816 * 2 ^ 59
def prefixEnd_3213816 : Nat := 4983230072969 + 3 ^ 40 * 3213816 * 2
def baseEnd_3213816 : Nat := 1650232343110103163819935

theorem tailTrace_3213816 : CollatzResearch.WordTrace tailWord_3213816 prefixEnd_3213816 1650232343110103163819935 := by
  unfold tailWord_3213816
  simp only [CollatzResearch.WordTrace]
  refine ⟨58608749662450491459826651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78144999549933988613102201 58608749662450491459826651)
  ·
    refine ⟨87913124493675737189739977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58608749662450491459826651 87913124493675737189739977)
    ·
      refine ⟨65934843370256802892304983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87913124493675737189739977 65934843370256802892304983)
      ·
        refine ⟨98902265055385204338457475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65934843370256802892304983 98902265055385204338457475)
        ·
          refine ⟨148353397583077806507686213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98902265055385204338457475 148353397583077806507686213)
          ·
            refine ⟨27816262046827088720191165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148353397583077806507686213 27816262046827088720191165)
            ·
              refine ⟨10431098267560158270071687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27816262046827088720191165 10431098267560158270071687)
              ·
                refine ⟨15646647401340237405107531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10431098267560158270071687 15646647401340237405107531)
                ·
                  refine ⟨23469971102010356107661297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15646647401340237405107531 23469971102010356107661297)
                  ·
                    refine ⟨17602478326507767080745973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23469971102010356107661297 17602478326507767080745973)
                    ·
                      refine ⟨1650232343110103163819935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17602478326507767080745973 1650232343110103163819935)
                      ·
                        rfl

theorem cell23_3213816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3213816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213816 prefixEnd_3213816 := by exact prefixLift 3213816
  have htrace : WordTrace (prefixWord ++ tailWord_3213816) baseStart_3213816 baseEnd_3213816 := by
    simpa [prefixWord, tailWord_3213816, baseEnd_3213816] using wordTrace_append hprefix tailTrace_3213816
  have hstable : (prefixWord ++ tailWord_3213816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213816).length < 2 ^ (prefixWord ++ tailWord_3213816).sum := by decide
  have hdescent : baseEnd_3213816 < baseStart_3213816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213843 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 4]
def baseStart_3213843 : Nat := 118140960795 + 3213843 * 2 ^ 59
def prefixEnd_3213843 : Nat := 4983230072969 + 3 ^ 40 * 3213843 * 2
def baseEnd_3213843 : Nat := 1650246207087774558182311

theorem tailTrace_3213843 : CollatzResearch.WordTrace tailWord_3213843 prefixEnd_3213843 1650246207087774558182311 := by
  unfold tailWord_3213843
  simp only [CollatzResearch.WordTrace]
  refine ⟨117218484095803166530886183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78145656063868777687257455 117218484095803166530886183)
  ·
    refine ⟨175827726143704749796329275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117218484095803166530886183 175827726143704749796329275)
    ·
      refine ⟨263741589215557124694493913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175827726143704749796329275 263741589215557124694493913)
      ·
        refine ⟨197806191911667843520870435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263741589215557124694493913 197806191911667843520870435)
        ·
          refine ⟨296709287867501765281305653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197806191911667843520870435 296709287867501765281305653)
          ·
            refine ⟨27816495737578290495122405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296709287867501765281305653 27816495737578290495122405)
            ·
              refine ⟨5215592950795929467835451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27816495737578290495122405 5215592950795929467835451)
              ·
                refine ⟨7823389426193894201753177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215592950795929467835451 7823389426193894201753177)
                ·
                  refine ⟨5867542069645420651314883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823389426193894201753177 5867542069645420651314883)
                  ·
                    refine ⟨8801313104468130976972325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867542069645420651314883 8801313104468130976972325)
                    ·
                      refine ⟨1650246207087774558182311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8801313104468130976972325 1650246207087774558182311)
                      ·
                        rfl

theorem cell23_3213843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_3213843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213843 prefixEnd_3213843 := by exact prefixLift 3213843
  have htrace : WordTrace (prefixWord ++ tailWord_3213843) baseStart_3213843 baseEnd_3213843 := by
    simpa [prefixWord, tailWord_3213843, baseEnd_3213843] using wordTrace_append hprefix tailTrace_3213843
  have hstable : (prefixWord ++ tailWord_3213843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213843).length < 2 ^ (prefixWord ++ tailWord_3213843).sum := by decide
  have hdescent : baseEnd_3213843 < baseStart_3213843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213894 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3213894 : Nat := 118140960795 + 3213894 * 2 ^ 59
def prefixEnd_3213894 : Nat := 4983230072969 + 3 ^ 40 * 3213894 * 2
def baseEnd_3213894 : Nat := 1650272394601153858644577

theorem tailTrace_3213894 : CollatzResearch.WordTrace tailWord_3213894 prefixEnd_3213894 1650272394601153858644577 := by
  unfold tailWord_3213894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663135756831825070031023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78146896145745601493995157 3663135756831825070031023)
  ·
    refine ⟨5494703635247737605046535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663135756831825070031023 5494703635247737605046535)
    ·
      refine ⟨8242055452871606407569803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5494703635247737605046535 8242055452871606407569803)
      ·
        refine ⟨12363083179307409611354705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8242055452871606407569803 12363083179307409611354705)
        ·
          refine ⟨9272312384480557208516029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12363083179307409611354705 9272312384480557208516029)
          ·
            refine ⟨3477117144180208953193511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9272312384480557208516029 3477117144180208953193511)
            ·
              refine ⟨5215675716270313429790267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477117144180208953193511 5215675716270313429790267)
              ·
                refine ⟨7823513574405470144685401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215675716270313429790267 7823513574405470144685401)
                ·
                  refine ⟨5867635180804102608514051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823513574405470144685401 5867635180804102608514051)
                  ·
                    refine ⟨8801452771206153912771077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867635180804102608514051 8801452771206153912771077)
                    ·
                      refine ⟨1650272394601153858644577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8801452771206153912771077 1650272394601153858644577)
                      ·
                        rfl

theorem cell23_3213894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3213894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213894 prefixEnd_3213894 := by exact prefixLift 3213894
  have htrace : WordTrace (prefixWord ++ tailWord_3213894) baseStart_3213894 baseEnd_3213894 := by
    simpa [prefixWord, tailWord_3213894, baseEnd_3213894] using wordTrace_append hprefix tailTrace_3213894
  have hstable : (prefixWord ++ tailWord_3213894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213894).length < 2 ^ (prefixWord ++ tailWord_3213894).sum := by decide
  have hdescent : baseEnd_3213894 < baseStart_3213894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213920 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 2, 3, 2]
def baseStart_3213920 : Nat := 118140960795 + 3213920 * 2 ^ 59
def prefixEnd_3213920 : Nat := 4983230072969 + 3 ^ 40 * 3213920 * 2
def baseEnd_3213920 : Nat := 1650285745098170756919457

theorem tailTrace_3213920 : CollatzResearch.WordTrace tailWord_3213920 prefixEnd_3213920 1650285745098170756919457 := by
  unfold tailWord_3213920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58610646258262104340719607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78147528344349472454292809 58610646258262104340719607)
  ·
    refine ⟨87915969387393156511079411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58610646258262104340719607 87915969387393156511079411)
    ·
      refine ⟨131873954081089734766619117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87915969387393156511079411 131873954081089734766619117)
      ·
        refine ⟨49452732780408650537482169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131873954081089734766619117 49452732780408650537482169)
        ·
          refine ⟨37089549585306487903111627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49452732780408650537482169 37089549585306487903111627)
          ·
            refine ⟨55634324377959731854667441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37089549585306487903111627 55634324377959731854667441)
            ·
              refine ⟨41725743283469798891000581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55634324377959731854667441 41725743283469798891000581)
              ·
                refine ⟨7823576865650587292062609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41725743283469798891000581 7823576865650587292062609)
                ·
                  refine ⟨5867682649237940469046957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823576865650587292062609 5867682649237940469046957)
                  ·
                    refine ⟨2200380993464227675892609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5867682649237940469046957 2200380993464227675892609)
                    ·
                      refine ⟨1650285745098170756919457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200380993464227675892609 1650285745098170756919457)
                      ·
                        rfl

theorem cell23_3213920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_3213920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213920 prefixEnd_3213920 := by exact prefixLift 3213920
  have htrace : WordTrace (prefixWord ++ tailWord_3213920) baseStart_3213920 baseEnd_3213920 := by
    simpa [prefixWord, tailWord_3213920, baseEnd_3213920] using wordTrace_append hprefix tailTrace_3213920
  have hstable : (prefixWord ++ tailWord_3213920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213920).length < 2 ^ (prefixWord ++ tailWord_3213920).sum := by decide
  have hdescent : baseEnd_3213920 < baseStart_3213920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213943 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 1, 6]
def baseStart_3213943 : Nat := 118140960795 + 3213943 * 2 ^ 59
def prefixEnd_3213943 : Nat := 4983230072969 + 3 ^ 40 * 3213943 * 2
def baseEnd_3213943 : Nat := 550099185051074722310617

theorem tailTrace_3213943 : CollatzResearch.WordTrace tailWord_3213943 prefixEnd_3213943 550099185051074722310617 := by
  unfold tailWord_3213943
  simp only [CollatzResearch.WordTrace]
  refine ⟨117222131395440883609526483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78148087596960589073017655 117222131395440883609526483)
  ·
    refine ⟨175833197093161325414289725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117222131395440883609526483 175833197093161325414289725)
    ·
      refine ⟨65937448909935497030358647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175833197093161325414289725 65937448909935497030358647)
      ·
        refine ⟨98906173364903245545537971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65937448909935497030358647 98906173364903245545537971)
        ·
          refine ⟨148359260047354868318306957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98906173364903245545537971 148359260047354868318306957)
          ·
            refine ⟨55634722517758075619365109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148359260047354868318306957 55634722517758075619365109)
            ·
              refine ⟨5215755236039819589315479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55634722517758075619365109 5215755236039819589315479)
              ·
                refine ⟨7823632854059729383973219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215755236039819589315479 7823632854059729383973219)
                ·
                  refine ⟨11735449281089594075959829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823632854059729383973219 11735449281089594075959829)
                  ·
                    refine ⟨550099185051074722310617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11735449281089594075959829 550099185051074722310617)
                    ·
                      rfl

theorem cell23_3213943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_3213943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213943 prefixEnd_3213943 := by exact prefixLift 3213943
  have htrace : WordTrace (prefixWord ++ tailWord_3213943) baseStart_3213943 baseEnd_3213943 := by
    simpa [prefixWord, tailWord_3213943, baseEnd_3213943] using wordTrace_append hprefix tailTrace_3213943
  have hstable : (prefixWord ++ tailWord_3213943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213943).length < 2 ^ (prefixWord ++ tailWord_3213943).sum := by decide
  have hdescent : baseEnd_3213943 < baseStart_3213943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213953 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3213953 : Nat := 118140960795 + 3213953 * 2 ^ 59
def prefixEnd_3213953 : Nat := 4983230072969 + 3 ^ 40 * 3213953 * 2
def baseEnd_3213953 : Nat := 1650302689959769127806805

theorem tailTrace_3213953 : CollatzResearch.WordTrace tailWord_3213953 prefixEnd_3213953 1650302689959769127806805 := by
  unfold tailWord_3213953
  simp only [CollatzResearch.WordTrace]
  refine ⟨117222496125404655317390513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78148330750269770211593675 117222496125404655317390513)
  ·
    refine ⟨87916872094053491488042885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117222496125404655317390513 87916872094053491488042885)
    ·
      refine ⟨16484413517635029654008041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87916872094053491488042885 16484413517635029654008041)
      ·
        refine ⟨12363310138226272240506031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16484413517635029654008041 12363310138226272240506031)
        ·
          refine ⟨18544965207339408360759047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12363310138226272240506031 18544965207339408360759047)
          ·
            refine ⟨27817447811009112541138571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18544965207339408360759047 27817447811009112541138571)
            ·
              refine ⟨41726171716513668811707857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27817447811009112541138571 41726171716513668811707857)
              ·
                refine ⟨31294628787385251608780893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41726171716513668811707857 31294628787385251608780893)
                ·
                  refine ⟨11735485795269469353292835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31294628787385251608780893 11735485795269469353292835)
                  ·
                    refine ⟨17603228692904204029939253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11735485795269469353292835 17603228692904204029939253)
                    ·
                      refine ⟨1650302689959769127806805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17603228692904204029939253 1650302689959769127806805)
                      ·
                        rfl

theorem cell23_3213953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3213953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213953 prefixEnd_3213953 := by exact prefixLift 3213953
  have htrace : WordTrace (prefixWord ++ tailWord_3213953) baseStart_3213953 baseEnd_3213953 := by
    simpa [prefixWord, tailWord_3213953, baseEnd_3213953] using wordTrace_append hprefix tailTrace_3213953
  have hstable : (prefixWord ++ tailWord_3213953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213953).length < 2 ^ (prefixWord ++ tailWord_3213953).sum := by decide
  have hdescent : baseEnd_3213953 < baseStart_3213953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213970 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3213970 : Nat := 118140960795 + 3213970 * 2 ^ 59
def prefixEnd_3213970 : Nat := 4983230072969 + 3 ^ 40 * 3213970 * 2
def baseEnd_3213970 : Nat := 1650311419130895561294227

theorem tailTrace_3213970 : CollatzResearch.WordTrace tailWord_3213970 prefixEnd_3213970 1650311419130895561294227 := by
  unfold tailWord_3213970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29305779041585766805189841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78148744110895378147172909 29305779041585766805189841)
  ·
    refine ⟨21979334281189325103892381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29305779041585766805189841 21979334281189325103892381)
    ·
      refine ⟨8242250355445996913959643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21979334281189325103892381 8242250355445996913959643)
      ·
        refine ⟨12363375533168995370939465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8242250355445996913959643 12363375533168995370939465)
        ·
          refine ⟨9272531649876746528204599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12363375533168995370939465 9272531649876746528204599)
          ·
            refine ⟨13908797474815119792306899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9272531649876746528204599 13908797474815119792306899)
            ·
              refine ⟨20863196212222679688460349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13908797474815119792306899 20863196212222679688460349)
              ·
                refine ⟨7823698579583504883172631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20863196212222679688460349 7823698579583504883172631)
                ·
                  refine ⟨11735547869375257324758947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823698579583504883172631 11735547869375257324758947)
                  ·
                    refine ⟨17603321804062885987138421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11735547869375257324758947 17603321804062885987138421)
                    ·
                      refine ⟨1650311419130895561294227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17603321804062885987138421 1650311419130895561294227)
                      ·
                        rfl

theorem cell23_3213970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3213970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213970 prefixEnd_3213970 := by exact prefixLift 3213970
  have htrace : WordTrace (prefixWord ++ tailWord_3213970) baseStart_3213970 baseEnd_3213970 := by
    simpa [prefixWord, tailWord_3213970, baseEnd_3213970] using wordTrace_append hprefix tailTrace_3213970
  have hstable : (prefixWord ++ tailWord_3213970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213970).length < 2 ^ (prefixWord ++ tailWord_3213970).sum := by decide
  have hdescent : baseEnd_3213970 < baseStart_3213970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213978 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3213978 : Nat := 118140960795 + 3213978 * 2 ^ 59
def prefixEnd_3213978 : Nat := 4983230072969 + 3 ^ 40 * 3213978 * 2
def baseEnd_3213978 : Nat := 1650315526976131529994191

theorem tailTrace_3213978 : CollatzResearch.WordTrace tailWord_3213978 prefixEnd_3213978 1650315526976131529994191 := by
  unfold tailWord_3213978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29305851987578521146762647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78148938633542723058033725 29305851987578521146762647)
  ·
    refine ⟨43958777981367781720143971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29305851987578521146762647 43958777981367781720143971)
    ·
      refine ⟨65938166972051672580215957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43958777981367781720143971 65938166972051672580215957)
      ·
        refine ⟨3090851576814922152197623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65938166972051672580215957 3090851576814922152197623)
        ·
          refine ⟨4636277365222383228296435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090851576814922152197623 4636277365222383228296435)
          ·
            refine ⟨6954416047833574842444653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636277365222383228296435 6954416047833574842444653)
            ·
              refine ⟨2607906017937590565916745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6954416047833574842444653 2607906017937590565916745)
              ·
                refine ⟨1955929513453192924437559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607906017937590565916745 1955929513453192924437559)
                ·
                  refine ⟨2933894270179789386656339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955929513453192924437559 2933894270179789386656339)
                  ·
                    refine ⟨4400841405269684079984509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2933894270179789386656339 4400841405269684079984509)
                    ·
                      refine ⟨1650315526976131529994191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4400841405269684079984509 1650315526976131529994191)
                      ·
                        rfl

theorem cell23_3213978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3213978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3213978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3213978 prefixEnd_3213978 := by exact prefixLift 3213978
  have htrace : WordTrace (prefixWord ++ tailWord_3213978) baseStart_3213978 baseEnd_3213978 := by
    simpa [prefixWord, tailWord_3213978, baseEnd_3213978] using wordTrace_append hprefix tailTrace_3213978
  have hstable : (prefixWord ++ tailWord_3213978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213978).length < 2 ^ (prefixWord ++ tailWord_3213978).sum := by decide
  have hdescent : baseEnd_3213978 < baseStart_3213978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214001 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3214001 : Nat := 118140960795 + 3214001 * 2 ^ 59
def prefixEnd_3214001 : Nat := 4983230072969 + 3 ^ 40 * 3214001 * 2
def baseEnd_3214001 : Nat := 1650327337031184940006585

theorem tailTrace_3214001 : CollatzResearch.WordTrace tailWord_3214001 prefixEnd_3214001 1650327337031184940006585 := by
  unfold tailWord_3214001
  simp only [CollatzResearch.WordTrace]
  refine ⟨117224246829230759515137857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78149497886153839676758571 117224246829230759515137857)
  ·
    refine ⟨87918185121923069636353393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117224246829230759515137857 87918185121923069636353393)
    ·
      refine ⟨65938638841442302227265045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87918185121923069636353393 65938638841442302227265045)
      ·
        refine ⟨3090873695692607916903049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65938638841442302227265045 3090873695692607916903049)
        ·
          refine ⟨2318155271769455937677287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3090873695692607916903049 2318155271769455937677287)
          ·
            refine ⟨3477232907654183906515931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318155271769455937677287 3477232907654183906515931)
            ·
              refine ⟨5215849361481275859773897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477232907654183906515931 5215849361481275859773897)
              ·
                refine ⟨3911887021110956894830423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5215849361481275859773897 3911887021110956894830423)
                ·
                  refine ⟨5867830531666435342245635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911887021110956894830423 5867830531666435342245635)
                  ·
                    refine ⟨8801745797499653013368453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867830531666435342245635 8801745797499653013368453)
                    ·
                      refine ⟨1650327337031184940006585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8801745797499653013368453 1650327337031184940006585)
                      ·
                        rfl

theorem cell23_3214001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3214001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214001 prefixEnd_3214001 := by exact prefixLift 3214001
  have htrace : WordTrace (prefixWord ++ tailWord_3214001) baseStart_3214001 baseEnd_3214001 := by
    simpa [prefixWord, tailWord_3214001, baseEnd_3214001] using wordTrace_append hprefix tailTrace_3214001
  have hstable : (prefixWord ++ tailWord_3214001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214001).length < 2 ^ (prefixWord ++ tailWord_3214001).sum := by decide
  have hdescent : baseEnd_3214001 < baseStart_3214001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214033 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_3214033 : Nat := 118140960795 + 3214033 * 2 ^ 59
def prefixEnd_3214033 : Nat := 4983230072969 + 3 ^ 40 * 3214033 * 2
def baseEnd_3214033 : Nat := 550114589470709604935479

theorem tailTrace_3214033 : CollatzResearch.WordTrace tailWord_3214033 prefixEnd_3214033 550114589470709604935479 := by
  unfold tailWord_3214033
  simp only [CollatzResearch.WordTrace]
  refine ⟨117225413965114828980302753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78150275976743219320201835 117225413965114828980302753)
  ·
    refine ⟨87919060473836121735227065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117225413965114828980302753 87919060473836121735227065)
    ·
      refine ⟨65939295355377091301420299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87919060473836121735227065 65939295355377091301420299)
      ·
        refine ⟨98908943033065636952130449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65939295355377091301420299 98908943033065636952130449)
        ·
          refine ⟨74181707274799227714097837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98908943033065636952130449 74181707274799227714097837)
          ·
            refine ⟨27818140228049710392786689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74181707274799227714097837 27818140228049710392786689)
            ·
              refine ⟨20863605171037282794590017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27818140228049710392786689 20863605171037282794590017)
              ·
                refine ⟨15647703878277962095942513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20863605171037282794590017 15647703878277962095942513)
                ·
                  refine ⟨11735777908708471571956885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15647703878277962095942513 11735777908708471571956885)
                  ·
                    refine ⟨550114589470709604935479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11735777908708471571956885 550114589470709604935479)
                    ·
                      rfl

theorem cell23_3214033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_3214033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214033 prefixEnd_3214033 := by exact prefixLift 3214033
  have htrace : WordTrace (prefixWord ++ tailWord_3214033) baseStart_3214033 baseEnd_3214033 := by
    simpa [prefixWord, tailWord_3214033, baseEnd_3214033] using wordTrace_append hprefix tailTrace_3214033
  have hstable : (prefixWord ++ tailWord_3214033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214033).length < 2 ^ (prefixWord ++ tailWord_3214033).sum := by decide
  have hdescent : baseEnd_3214033 < baseStart_3214033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214044 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3214044 : Nat := 118140960795 + 3214044 * 2 ^ 59
def prefixEnd_3214044 : Nat := 4983230072969 + 3 ^ 40 * 3214044 * 2
def baseEnd_3214044 : Nat := 1650349416699328271768887

theorem tailTrace_3214044 : CollatzResearch.WordTrace tailWord_3214044 prefixEnd_3214044 1650349416699328271768887 := by
  unfold tailWord_3214044
  simp only [CollatzResearch.WordTrace]
  refine ⟨58612907584037488929476593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78150543445383318572635457 58612907584037488929476593)
  ·
    refine ⟨43959680688028116697107445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58612907584037488929476593 43959680688028116697107445)
    ·
      refine ⟨4121220064502635940353823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43959680688028116697107445 4121220064502635940353823)
      ·
        refine ⟨6181830096753953910530735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121220064502635940353823 6181830096753953910530735)
        ·
          refine ⟨9272745145130930865796103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6181830096753953910530735 9272745145130930865796103)
          ·
            refine ⟨13909117717696396298694155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9272745145130930865796103 13909117717696396298694155)
            ·
              refine ⟨20863676576544594448041233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13909117717696396298694155 20863676576544594448041233)
              ·
                refine ⟨15647757432408445836030925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20863676576544594448041233 15647757432408445836030925)
                ·
                  refine ⟨5867909037153167188511597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15647757432408445836030925 5867909037153167188511597)
                  ·
                    refine ⟨2200465888932437695691849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5867909037153167188511597 2200465888932437695691849)
                    ·
                      refine ⟨1650349416699328271768887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200465888932437695691849 1650349416699328271768887)
                      ·
                        rfl

theorem cell23_3214044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3214044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214044 prefixEnd_3214044 := by exact prefixLift 3214044
  have htrace : WordTrace (prefixWord ++ tailWord_3214044) baseStart_3214044 baseEnd_3214044 := by
    simpa [prefixWord, tailWord_3214044, baseEnd_3214044] using wordTrace_append hprefix tailTrace_3214044
  have hstable : (prefixWord ++ tailWord_3214044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214044).length < 2 ^ (prefixWord ++ tailWord_3214044).sum := by decide
  have hdescent : baseEnd_3214044 < baseStart_3214044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214063 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 9]
def baseStart_3214063 : Nat := 118140960795 + 3214063 * 2 ^ 59
def prefixEnd_3214063 : Nat := 4983230072969 + 3 ^ 40 * 3214063 * 2
def baseEnd_3214063 : Nat := 183373241425751521936811

theorem tailTrace_3214063 : CollatzResearch.WordTrace tailWord_3214063 prefixEnd_3214063 183373241425751521936811 := by
  unfold tailWord_3214063
  simp only [CollatzResearch.WordTrace]
  refine ⟨117226508155006144103894843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78151005436670762735929895 117226508155006144103894843)
  ·
    refine ⟨175839762232509216155842265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117226508155006144103894843 175839762232509216155842265)
    ·
      refine ⟨131879821674381912116881699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175839762232509216155842265 131879821674381912116881699)
      ·
        refine ⟨197819732511572868175322549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131879821674381912116881699 197819732511572868175322549)
        ·
          refine ⟨18545599922959956391436489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197819732511572868175322549 18545599922959956391436489)
          ·
            refine ⟨13909199942219967293577367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18545599922959956391436489 13909199942219967293577367)
            ·
              refine ⟨20863799913329950940366051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13909199942219967293577367 20863799913329950940366051)
              ·
                refine ⟨31295699869994926410549077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20863799913329950940366051 31295699869994926410549077)
                ·
                  refine ⟨183373241425751521936811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31295699869994926410549077 183373241425751521936811)
                  ·
                    rfl

theorem cell23_3214063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 9].length) (baseStart_3214063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214063 prefixEnd_3214063 := by exact prefixLift 3214063
  have htrace : WordTrace (prefixWord ++ tailWord_3214063) baseStart_3214063 baseEnd_3214063 := by
    simpa [prefixWord, tailWord_3214063, baseEnd_3214063] using wordTrace_append hprefix tailTrace_3214063
  have hstable : (prefixWord ++ tailWord_3214063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214063).length < 2 ^ (prefixWord ++ tailWord_3214063).sum := by decide
  have hdescent : baseEnd_3214063 < baseStart_3214063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214070 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3214070 : Nat := 118140960795 + 3214070 * 2 ^ 59
def prefixEnd_3214070 : Nat := 4983230072969 + 3 ^ 40 * 3214070 * 2
def baseEnd_3214070 : Nat := 1650362767196345170043767

theorem tailTrace_3214070 : CollatzResearch.WordTrace tailWord_3214070 prefixEnd_3214070 1650362767196345170043767 := by
  unfold tailWord_3214070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7326672716623799018712479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78151175643987189532933109 7326672716623799018712479)
  ·
    refine ⟨10990009074935698528068719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7326672716623799018712479 10990009074935698528068719)
    ·
      refine ⟨16485013612403547792103079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10990009074935698528068719 16485013612403547792103079)
      ·
        refine ⟨24727520418605321688154619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16485013612403547792103079 24727520418605321688154619)
        ·
          refine ⟨37091280627907982532231929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24727520418605321688154619 37091280627907982532231929)
          ·
            refine ⟨27818460470930986899173947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37091280627907982532231929 27818460470930986899173947)
            ·
              refine ⟨41727690706396480348760921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27818460470930986899173947 41727690706396480348760921)
              ·
                refine ⟨31295768029797360261570691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41727690706396480348760921 31295768029797360261570691)
                ·
                  refine ⟨46943652044696040392356037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31295768029797360261570691 46943652044696040392356037)
                  ·
                    refine ⟨8801934758380507573566757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46943652044696040392356037 8801934758380507573566757)
                    ·
                      refine ⟨1650362767196345170043767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8801934758380507573566757 1650362767196345170043767)
                      ·
                        rfl

theorem cell23_3214070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3214070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214070 prefixEnd_3214070 := by exact prefixLift 3214070
  have htrace : WordTrace (prefixWord ++ tailWord_3214070) baseStart_3214070 baseEnd_3214070 := by
    simpa [prefixWord, tailWord_3214070, baseEnd_3214070] using wordTrace_append hprefix tailTrace_3214070
  have hstable : (prefixWord ++ tailWord_3214070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214070).length < 2 ^ (prefixWord ++ tailWord_3214070).sum := by decide
  have hdescent : baseEnd_3214070 < baseStart_3214070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214078 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_3214078 : Nat := 118140960795 + 3214078 * 2 ^ 59
def prefixEnd_3214078 : Nat := 4983230072969 + 3 ^ 40 * 3214078 * 2
def baseEnd_3214078 : Nat := 1650366875041581138743731

theorem tailTrace_3214078 : CollatzResearch.WordTrace tailWord_3214078 prefixEnd_3214078 1650366875041581138743731 := by
  unfold tailWord_3214078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653381906243975208211361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78151370166634534443793925 14653381906243975208211361)
  ·
    refine ⟨10990036429682981406158521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14653381906243975208211361 10990036429682981406158521)
    ·
      refine ⟨8242527322262236054618891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10990036429682981406158521 8242527322262236054618891)
      ·
        refine ⟨12363790983393354081928337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8242527322262236054618891 12363790983393354081928337)
        ·
          refine ⟨9272843237545015561446253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12363790983393354081928337 9272843237545015561446253)
          ·
            refine ⟨3477316214079380835542345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9272843237545015561446253 3477316214079380835542345)
            ·
              refine ⟨2607987160559535626656759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3477316214079380835542345 2607987160559535626656759)
              ·
                refine ⟨3911980740839303439985139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607987160559535626656759 3911980740839303439985139)
                ·
                  refine ⟨5867971111258955159977709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911980740839303439985139 5867971111258955159977709)
                  ·
                    refine ⟨2200489166722108184991641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5867971111258955159977709 2200489166722108184991641)
                    ·
                      refine ⟨1650366875041581138743731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200489166722108184991641 1650366875041581138743731)
                      ·
                        rfl

theorem cell23_3214078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_3214078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214078 prefixEnd_3214078 := by exact prefixLift 3214078
  have htrace : WordTrace (prefixWord ++ tailWord_3214078) baseStart_3214078 baseEnd_3214078 := by
    simpa [prefixWord, tailWord_3214078, baseEnd_3214078] using wordTrace_append hprefix tailTrace_3214078
  have hstable : (prefixWord ++ tailWord_3214078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214078).length < 2 ^ (prefixWord ++ tailWord_3214078).sum := by decide
  have hdescent : baseEnd_3214078 < baseStart_3214078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214090 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3214090 : Nat := 118140960795 + 3214090 * 2 ^ 59
def prefixEnd_3214090 : Nat := 4983230072969 + 3 ^ 40 * 3214090 * 2
def baseEnd_3214090 : Nat := 1650373036809435091793675

theorem tailTrace_3214090 : CollatzResearch.WordTrace tailWord_3214090 prefixEnd_3214090 1650373036809435091793675 := by
  unfold tailWord_3214090
  simp only [CollatzResearch.WordTrace]
  refine ⟨29306873231477081928781931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78151661950605551810085149 29306873231477081928781931)
  ·
    refine ⟨43960309847215622893172897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29306873231477081928781931 43960309847215622893172897)
    ·
      refine ⟨32970232385411717169879673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43960309847215622893172897 32970232385411717169879673)
      ·
        refine ⟨24727674289058787877409755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32970232385411717169879673 24727674289058787877409755)
        ·
          refine ⟨37091511433588181816114633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24727674289058787877409755 37091511433588181816114633)
          ·
            refine ⟨27818633575191136362085975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37091511433588181816114633 27818633575191136362085975)
            ·
              refine ⟨41727950362786704543128963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27818633575191136362085975 41727950362786704543128963)
              ·
                refine ⟨62591925544180056814693445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41727950362786704543128963 62591925544180056814693445)
                ·
                  refine ⟨11735986039533760652755021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62591925544180056814693445 11735986039533760652755021)
                  ·
                    refine ⟨4400994764825160244783133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11735986039533760652755021 4400994764825160244783133)
                    ·
                      refine ⟨1650373036809435091793675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4400994764825160244783133 1650373036809435091793675)
                      ·
                        rfl

theorem cell23_3214090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3214090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214090 prefixEnd_3214090 := by exact prefixLift 3214090
  have htrace : WordTrace (prefixWord ++ tailWord_3214090) baseStart_3214090 baseEnd_3214090 := by
    simpa [prefixWord, tailWord_3214090, baseEnd_3214090] using wordTrace_append hprefix tailTrace_3214090
  have hstable : (prefixWord ++ tailWord_3214090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214090).length < 2 ^ (prefixWord ++ tailWord_3214090).sum := by decide
  have hdescent : baseEnd_3214090 < baseStart_3214090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214130 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3214130 : Nat := 118140960795 + 3214130 * 2 ^ 59
def prefixEnd_3214130 : Nat := 4983230072969 + 3 ^ 40 * 3214130 * 2
def baseEnd_3214130 : Nat := 1650393576035614935293491

theorem tailTrace_3214130 : CollatzResearch.WordTrace tailWord_3214130 prefixEnd_3214130 1650393576035614935293491 := by
  unfold tailWord_3214130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29307237961440853636645961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78152634563842276364389229 29307237961440853636645961)
  ·
    refine ⟨21980428471080640227484471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29307237961440853636645961 21980428471080640227484471)
    ·
      refine ⟨32970642706620960341226707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21980428471080640227484471 32970642706620960341226707)
      ·
        refine ⟨49455964059931440511840061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32970642706620960341226707 49455964059931440511840061)
        ·
          refine ⟨18545986522474290191940023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49455964059931440511840061 18545986522474290191940023)
          ·
            refine ⟨27818979783711435287910035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18545986522474290191940023 27818979783711435287910035)
            ·
              refine ⟨41728469675567152931865053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27818979783711435287910035 41728469675567152931865053)
              ·
                refine ⟨15648176128337682349449395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41728469675567152931865053 15648176128337682349449395)
                ·
                  refine ⟨23472264192506523524174093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15648176128337682349449395 23472264192506523524174093)
                  ·
                    refine ⟨8802099072189946321565285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23472264192506523524174093 8802099072189946321565285)
                    ·
                      refine ⟨1650393576035614935293491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8802099072189946321565285 1650393576035614935293491)
                      ·
                        rfl

theorem cell23_3214130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3214130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214130 prefixEnd_3214130 := by exact prefixLift 3214130
  have htrace : WordTrace (prefixWord ++ tailWord_3214130) baseStart_3214130 baseEnd_3214130 := by
    simpa [prefixWord, tailWord_3214130, baseEnd_3214130] using wordTrace_append hprefix tailTrace_3214130
  have hstable : (prefixWord ++ tailWord_3214130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214130).length < 2 ^ (prefixWord ++ tailWord_3214130).sum := by decide
  have hdescent : baseEnd_3214130 < baseStart_3214130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214148 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 5]
def baseStart_3214148 : Nat := 118140960795 + 3214148 * 2 ^ 59
def prefixEnd_3214148 : Nat := 4983230072969 + 3 ^ 40 * 3214148 * 2
def baseEnd_3214148 : Nat := 183378090965266207207601

theorem tailTrace_3214148 : CollatzResearch.WordTrace tailWord_3214148 prefixEnd_3214148 183378090965266207207601 := by
  unfold tailWord_3214148
  simp only [CollatzResearch.WordTrace]
  refine ⟨58614804179849101810369549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78153072239798802413826065 58614804179849101810369549)
  ·
    refine ⟨21980551567443413178888581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58614804179849101810369549 21980551567443413178888581)
    ·
      refine ⟨4121353418895639971041609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21980551567443413178888581 4121353418895639971041609)
      ·
        refine ⟨3091015064171729978281207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4121353418895639971041609 3091015064171729978281207)
        ·
          refine ⟨4636522596257594967421811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091015064171729978281207 4636522596257594967421811)
          ·
            refine ⟨6954783894386392451132717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636522596257594967421811 6954783894386392451132717)
            ·
              refine ⟨2608043960394897169174769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6954783894386392451132717 2608043960394897169174769)
              ·
                refine ⟨1956032970296172876881077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608043960394897169174769 1956032970296172876881077)
                ·
                  refine ⟨183378090965266207207601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956032970296172876881077 183378090965266207207601)
                  ·
                    rfl

theorem cell23_3214148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_3214148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214148 prefixEnd_3214148 := by exact prefixLift 3214148
  have htrace : WordTrace (prefixWord ++ tailWord_3214148) baseStart_3214148 baseEnd_3214148 := by
    simpa [prefixWord, tailWord_3214148, baseEnd_3214148] using wordTrace_append hprefix tailTrace_3214148
  have hstable : (prefixWord ++ tailWord_3214148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214148).length < 2 ^ (prefixWord ++ tailWord_3214148).sum := by decide
  have hdescent : baseEnd_3214148 < baseStart_3214148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214184 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3214184 : Nat := 118140960795 + 3214184 * 2 ^ 59
def prefixEnd_3214184 : Nat := 4983230072969 + 3 ^ 40 * 3214184 * 2
def baseEnd_3214184 : Nat := 1650421303990957724018243

theorem tailTrace_3214184 : CollatzResearch.WordTrace tailWord_3214184 prefixEnd_3214184 1650421303990957724018243 := by
  unfold tailWord_3214184
  simp only [CollatzResearch.WordTrace]
  refine ⟨58615460693783890884524803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78153947591711854512699737 58615460693783890884524803)
  ·
    refine ⟨87923191040675836326787205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58615460693783890884524803 87923191040675836326787205)
    ·
      refine ⟨16485598320126719311272601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87923191040675836326787205 16485598320126719311272601)
      ·
        refine ⟨12364198740095039483454451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16485598320126719311272601 12364198740095039483454451)
        ·
          refine ⟨18546298110142559225181677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12364198740095039483454451 18546298110142559225181677)
          ·
            refine ⟨6954861791303459709443129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18546298110142559225181677 6954861791303459709443129)
            ·
              refine ⟨5216146343477594782082347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954861791303459709443129 5216146343477594782082347)
              ·
                refine ⟨7824219515216392173123521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216146343477594782082347 7824219515216392173123521)
                ·
                  refine ⟨5868164636412294129842641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7824219515216392173123521 5868164636412294129842641)
                  ·
                    refine ⟨4401123477309220597381981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868164636412294129842641 4401123477309220597381981)
                    ·
                      refine ⟨1650421303990957724018243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4401123477309220597381981 1650421303990957724018243)
                      ·
                        rfl

theorem cell23_3214184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3214184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214184 prefixEnd_3214184 := by exact prefixLift 3214184
  have htrace : WordTrace (prefixWord ++ tailWord_3214184) baseStart_3214184 baseEnd_3214184 := by
    simpa [prefixWord, tailWord_3214184, baseEnd_3214184] using wordTrace_append hprefix tailTrace_3214184
  have hstable : (prefixWord ++ tailWord_3214184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214184).length < 2 ^ (prefixWord ++ tailWord_3214184).sum := by decide
  have hdescent : baseEnd_3214184 < baseStart_3214184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214237 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3214237 : Nat := 118140960795 + 3214237 * 2 ^ 59
def prefixEnd_3214237 : Nat := 4983230072969 + 3 ^ 40 * 3214237 * 2
def baseEnd_3214237 : Nat := 1650448518465646016655499

theorem tailTrace_3214237 : CollatzResearch.WordTrace tailWord_3214237 prefixEnd_3214237 1650448518465646016655499 := by
  unfold tailWord_3214237
  simp only [CollatzResearch.WordTrace]
  refine ⟨117232854456375771820728965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78155236304250514547152643 117232854456375771820728965)
  ·
    refine ⟨21981160210570457216386681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117232854456375771820728965 21981160210570457216386681)
    ·
      refine ⟨16485870157927842912290011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21981160210570457216386681 16485870157927842912290011)
      ·
        refine ⟨24728805236891764368435017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16485870157927842912290011 24728805236891764368435017)
        ·
          refine ⟨18546603927668823276326263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24728805236891764368435017 18546603927668823276326263)
          ·
            refine ⟨27819905891503234914489395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18546603927668823276326263 27819905891503234914489395)
            ·
              refine ⟨41729858837254852371734093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27819905891503234914489395 41729858837254852371734093)
              ·
                refine ⟨15648697063970569639400285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41729858837254852371734093 15648697063970569639400285)
                ·
                  refine ⟨5868261398988963614775107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15648697063970569639400285 5868261398988963614775107)
                  ·
                    refine ⟨8802392098483445422162661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868261398988963614775107 8802392098483445422162661)
                    ·
                      refine ⟨1650448518465646016655499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8802392098483445422162661 1650448518465646016655499)
                      ·
                        rfl

theorem cell23_3214237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3214237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214237 prefixEnd_3214237 := by exact prefixLift 3214237
  have htrace : WordTrace (prefixWord ++ tailWord_3214237) baseStart_3214237 baseEnd_3214237 := by
    simpa [prefixWord, tailWord_3214237, baseEnd_3214237] using wordTrace_append hprefix tailTrace_3214237
  have hstable : (prefixWord ++ tailWord_3214237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214237).length < 2 ^ (prefixWord ++ tailWord_3214237).sum := by decide
  have hdescent : baseEnd_3214237 < baseStart_3214237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214241 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3214241 : Nat := 118140960795 + 3214241 * 2 ^ 59
def prefixEnd_3214241 : Nat := 4983230072969 + 3 ^ 40 * 3214241 * 2
def baseEnd_3214241 : Nat := 1650450572388264001005481

theorem tailTrace_3214241 : CollatzResearch.WordTrace tailWord_3214241 prefixEnd_3214241 1650450572388264001005481 := by
  unfold tailWord_3214241
  simp only [CollatzResearch.WordTrace]
  refine ⟨117233000348361280503874577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78155333565574187002583051 117233000348361280503874577)
  ·
    refine ⟨87924750261270960377905933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117233000348361280503874577 87924750261270960377905933)
    ·
      refine ⟨32971781347976610141714725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87924750261270960377905933 32971781347976610141714725)
      ·
        refine ⟨6182209002745614401571511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32971781347976610141714725 6182209002745614401571511)
        ·
          refine ⟨9273313504118421602357267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182209002745614401571511 9273313504118421602357267)
          ·
            refine ⟨13909970256177632403535901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9273313504118421602357267 13909970256177632403535901)
            ·
              refine ⟨5216238846066612151325963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13909970256177632403535901 5216238846066612151325963)
              ·
                refine ⟨7824358269099918226988945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216238846066612151325963 7824358269099918226988945)
                ·
                  refine ⟨5868268701824938670241709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7824358269099918226988945 5868268701824938670241709)
                  ·
                    refine ⟨2200600763184352001340641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5868268701824938670241709 2200600763184352001340641)
                    ·
                      refine ⟨1650450572388264001005481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200600763184352001340641 1650450572388264001005481)
                      ·
                        rfl

theorem cell23_3214241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3214241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214241 prefixEnd_3214241 := by exact prefixLift 3214241
  have htrace : WordTrace (prefixWord ++ tailWord_3214241) baseStart_3214241 baseEnd_3214241 := by
    simpa [prefixWord, tailWord_3214241, baseEnd_3214241] using wordTrace_append hprefix tailTrace_3214241
  have hstable : (prefixWord ++ tailWord_3214241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214241).length < 2 ^ (prefixWord ++ tailWord_3214241).sum := by decide
  have hdescent : baseEnd_3214241 < baseStart_3214241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214264 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 2, 4]
def baseStart_3214264 : Nat := 118140960795 + 3214264 * 2 ^ 59
def prefixEnd_3214264 : Nat := 4983230072969 + 3 ^ 40 * 3214264 * 2
def baseEnd_3214264 : Nat := 550154127481105803672625

theorem tailTrace_3214264 : CollatzResearch.WordTrace tailWord_3214264 prefixEnd_3214264 550154127481105803672625 := by
  unfold tailWord_3214264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58616919613638977715980923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78155892818185303621307897 58616919613638977715980923)
  ·
    refine ⟨87925379420458466573971385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58616919613638977715980923 87925379420458466573971385)
    ·
      refine ⟨65944034565343849930478539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87925379420458466573971385 65944034565343849930478539)
      ·
        refine ⟨98916051848015774895717809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65944034565343849930478539 98916051848015774895717809)
        ·
          refine ⟨74187038886011831171788357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98916051848015774895717809 74187038886011831171788357)
          ·
            refine ⟨13910069791127218344710317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74187038886011831171788357 13910069791127218344710317)
            ·
              refine ⟨5216276171672706879266369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13910069791127218344710317 5216276171672706879266369)
              ·
                refine ⟨3912207128754530159449777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216276171672706879266369 3912207128754530159449777)
                ·
                  refine ⟨2934155346565897619587333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912207128754530159449777 2934155346565897619587333)
                  ·
                    refine ⟨550154127481105803672625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934155346565897619587333 550154127481105803672625)
                    ·
                      rfl

theorem cell23_3214264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_3214264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214264 prefixEnd_3214264 := by exact prefixLift 3214264
  have htrace : WordTrace (prefixWord ++ tailWord_3214264) baseStart_3214264 baseEnd_3214264 := by
    simpa [prefixWord, tailWord_3214264, baseEnd_3214264] using wordTrace_append hprefix tailTrace_3214264
  have hstable : (prefixWord ++ tailWord_3214264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214264).length < 2 ^ (prefixWord ++ tailWord_3214264).sum := by decide
  have hdescent : baseEnd_3214264 < baseStart_3214264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214285 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3214285 : Nat := 118140960795 + 3214285 * 2 ^ 59
def prefixEnd_3214285 : Nat := 4983230072969 + 3 ^ 40 * 3214285 * 2
def baseEnd_3214285 : Nat := 550157721845687276285093

theorem tailTrace_3214285 : CollatzResearch.WordTrace tailWord_3214285 prefixEnd_3214285 550157721845687276285093 := by
  unfold tailWord_3214285
  simp only [CollatzResearch.WordTrace]
  refine ⟨117234605160201876018476309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78156403440134584012317539 117234605160201876018476309)
  ·
    refine ⟨5495372116884462938366077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117234605160201876018476309 5495372116884462938366077)
    ·
      refine ⟨2060764543831673601887279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5495372116884462938366077 2060764543831673601887279)
      ·
        refine ⟨3091146815747510402830919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060764543831673601887279 3091146815747510402830919)
        ·
          refine ⟨4636720223621265604246379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091146815747510402830919 4636720223621265604246379)
          ·
            refine ⟨6955080335431898406369569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636720223621265604246379 6955080335431898406369569)
            ·
              refine ⟨5216310251573923804777177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955080335431898406369569 5216310251573923804777177)
              ·
                refine ⟨3912232688680442853582883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216310251573923804777177 3912232688680442853582883)
                ·
                  refine ⟨5868349033020664280374325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912232688680442853582883 5868349033020664280374325)
                  ·
                    refine ⟨550157721845687276285093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5868349033020664280374325 550157721845687276285093)
                    ·
                      rfl

theorem cell23_3214285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3214285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214285 prefixEnd_3214285 := by exact prefixLift 3214285
  have htrace : WordTrace (prefixWord ++ tailWord_3214285) baseStart_3214285 baseEnd_3214285 := by
    simpa [prefixWord, tailWord_3214285, baseEnd_3214285] using wordTrace_append hprefix tailTrace_3214285
  have hstable : (prefixWord ++ tailWord_3214285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214285).length < 2 ^ (prefixWord ++ tailWord_3214285).sum := by decide
  have hdescent : baseEnd_3214285 < baseStart_3214285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214294 : List Nat := [5, 2, 1, 1, 2, 2, 1, 9]
def baseStart_3214294 : Nat := 118140960795 + 3214294 * 2 ^ 59
def prefixEnd_3214294 : Nat := 4983230072969 + 3 ^ 40 * 3214294 * 2
def baseEnd_3214294 : Nat := 61128806920850084949731

theorem tailTrace_3214294 : CollatzResearch.WordTrace tailWord_3214294 prefixEnd_3214294 61128806920850084949731 := by
  unfold tailWord_3214294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327183338573079409722121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78156622278112847037035957 7327183338573079409722121)
  ·
    refine ⟨5495387503929809557291591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7327183338573079409722121 5495387503929809557291591)
    ·
      refine ⟨8243081255894714335937387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495387503929809557291591 8243081255894714335937387)
      ·
        refine ⟨12364621883842071503906081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8243081255894714335937387 12364621883842071503906081)
        ·
          refine ⟨9273466412881553627929561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12364621883842071503906081 9273466412881553627929561)
          ·
            refine ⟨6955099809661165220947171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9273466412881553627929561 6955099809661165220947171)
            ·
              refine ⟨10432649714491747831420757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955099809661165220947171 10432649714491747831420757)
              ·
                refine ⟨61128806920850084949731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10432649714491747831420757 61128806920850084949731)
                ·
                  rfl

theorem cell23_3214294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_3214294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214294 prefixEnd_3214294 := by exact prefixLift 3214294
  have htrace : WordTrace (prefixWord ++ tailWord_3214294) baseStart_3214294 baseEnd_3214294 := by
    simpa [prefixWord, tailWord_3214294, baseEnd_3214294] using wordTrace_append hprefix tailTrace_3214294
  have hstable : (prefixWord ++ tailWord_3214294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214294).length < 2 ^ (prefixWord ++ tailWord_3214294).sum := by decide
  have hdescent : baseEnd_3214294 < baseStart_3214294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214322 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3214322 : Nat := 118140960795 + 3214322 * 2 ^ 59
def prefixEnd_3214322 : Nat := 4983230072969 + 3 ^ 40 * 3214322 * 2
def baseEnd_3214322 : Nat := 1650492164321278184092609

theorem tailTrace_3214322 : CollatzResearch.WordTrace tailWord_3214322 prefixEnd_3214322 1650492164321278184092609 := by
  unfold tailWord_3214322
  simp only [CollatzResearch.WordTrace]
  refine ⟨29308988665266957834393305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78157303107378554225048813 29308988665266957834393305)
  ·
    refine ⟨21981741498950218375794979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29308988665266957834393305 21981741498950218375794979)
    ·
      refine ⟨32972612248425327563692469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21981741498950218375794979 32972612248425327563692469)
      ·
        refine ⟨3091182398289874459096169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32972612248425327563692469 3091182398289874459096169)
        ·
          refine ⟨2318386798717405844322127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091182398289874459096169 2318386798717405844322127)
          ·
            refine ⟨3477580198076108766483191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318386798717405844322127 3477580198076108766483191)
            ·
              refine ⟨5216370297114163149724787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477580198076108766483191 5216370297114163149724787)
              ·
                refine ⟨7824555445671244724587181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216370297114163149724787 7824555445671244724587181)
                ·
                  refine ⟨2934208292126716771720193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7824555445671244724587181 2934208292126716771720193)
                  ·
                    refine ⟨2200656219095037578790145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934208292126716771720193 2200656219095037578790145)
                    ·
                      refine ⟨1650492164321278184092609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200656219095037578790145 1650492164321278184092609)
                      ·
                        rfl

theorem cell23_3214322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3214322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214322 prefixEnd_3214322 := by exact prefixLift 3214322
  have htrace : WordTrace (prefixWord ++ tailWord_3214322) baseStart_3214322 baseEnd_3214322 := by
    simpa [prefixWord, tailWord_3214322, baseEnd_3214322] using wordTrace_append hprefix tailTrace_3214322
  have hstable : (prefixWord ++ tailWord_3214322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214322).length < 2 ^ (prefixWord ++ tailWord_3214322).sum := by decide
  have hdescent : baseEnd_3214322 < baseStart_3214322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214347 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5]
def baseStart_3214347 : Nat := 118140960795 + 3214347 * 2 ^ 59
def prefixEnd_3214347 : Nat := 4983230072969 + 3 ^ 40 * 3214347 * 2
def baseEnd_3214347 : Nat := 1650505001337640586279993

theorem tailTrace_3214347 : CollatzResearch.WordTrace tailWord_3214347 prefixEnd_3214347 1650505001337640586279993 := by
  unfold tailWord_3214347
  simp only [CollatzResearch.WordTrace]
  refine ⟨117236866485977260607233295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78157910990651507071488863 117236866485977260607233295)
  ·
    refine ⟨175855299728965890910849943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117236866485977260607233295 175855299728965890910849943)
    ·
      refine ⟨263782949593448836366274915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175855299728965890910849943 263782949593448836366274915)
      ·
        refine ⟨395674424390173254549412373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263782949593448836366274915 395674424390173254549412373)
        ·
          refine ⟨18547238643289371307003705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 395674424390173254549412373 18547238643289371307003705)
          ·
            refine ⟨13910428982467028480252779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18547238643289371307003705 13910428982467028480252779)
            ·
              refine ⟨20865643473700542720379169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13910428982467028480252779 20865643473700542720379169)
              ·
                refine ⟨15649232605275407040284377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20865643473700542720379169 15649232605275407040284377)
                ·
                  refine ⟨11736924453956555280213283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15649232605275407040284377 11736924453956555280213283)
                  ·
                    refine ⟨17605386680934832920319925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11736924453956555280213283 17605386680934832920319925)
                    ·
                      refine ⟨1650505001337640586279993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17605386680934832920319925 1650505001337640586279993)
                      ·
                        rfl

theorem cell23_3214347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_3214347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214347 prefixEnd_3214347 := by exact prefixLift 3214347
  have htrace : WordTrace (prefixWord ++ tailWord_3214347) baseStart_3214347 baseEnd_3214347 := by
    simpa [prefixWord, tailWord_3214347, baseEnd_3214347] using wordTrace_append hprefix tailTrace_3214347
  have hstable : (prefixWord ++ tailWord_3214347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214347).length < 2 ^ (prefixWord ++ tailWord_3214347).sum := by decide
  have hdescent : baseEnd_3214347 < baseStart_3214347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214348 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 1, 3, 2]
def baseStart_3214348 : Nat := 118140960795 + 3214348 * 2 ^ 59
def prefixEnd_3214348 : Nat := 4983230072969 + 3 ^ 40 * 3214348 * 2
def baseEnd_3214348 : Nat := 1650505514818295082367489

theorem tailTrace_3214348 : CollatzResearch.WordTrace tailWord_3214348 prefixEnd_3214348 1650505514818295082367489 := by
  unfold tailWord_3214348
  simp only [CollatzResearch.WordTrace]
  refine ⟨58618451479486818889009849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78157935305982425185346465 58618451479486818889009849)
  ·
    refine ⟨43963838609615114166757387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58618451479486818889009849 43963838609615114166757387)
    ·
      refine ⟨65945757914422671250136081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43963838609615114166757387 65945757914422671250136081)
      ·
        refine ⟨49459318435817003437602061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65945757914422671250136081 49459318435817003437602061)
        ·
          refine ⟨18547244413431376289100773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49459318435817003437602061 18547244413431376289100773)
          ·
            refine ⟨3477608327518383054206395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18547244413431376289100773 3477608327518383054206395)
            ·
              refine ⟨5216412491277574581309593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477608327518383054206395 5216412491277574581309593)
              ·
                refine ⟨3912309368458180935982195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216412491277574581309593 3912309368458180935982195)
                ·
                  refine ⟨5868464052687271403973293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912309368458180935982195 5868464052687271403973293)
                  ·
                    refine ⟨2200674019757726776489985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5868464052687271403973293 2200674019757726776489985)
                    ·
                      refine ⟨1650505514818295082367489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200674019757726776489985 1650505514818295082367489)
                      ·
                        rfl

theorem cell23_3214348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_3214348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214348 prefixEnd_3214348 := by exact prefixLift 3214348
  have htrace : WordTrace (prefixWord ++ tailWord_3214348) baseStart_3214348 baseEnd_3214348 := by
    simpa [prefixWord, tailWord_3214348, baseEnd_3214348] using wordTrace_append hprefix tailTrace_3214348
  have hstable : (prefixWord ++ tailWord_3214348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214348).length < 2 ^ (prefixWord ++ tailWord_3214348).sum := by decide
  have hdescent : baseEnd_3214348 < baseStart_3214348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214365 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_3214365 : Nat := 118140960795 + 3214365 * 2 ^ 59
def prefixEnd_3214365 : Nat := 4983230072969 + 3 ^ 40 * 3214365 * 2
def baseEnd_3214365 : Nat := 1650514243989421515854911

theorem tailTrace_3214365 : CollatzResearch.WordTrace tailWord_3214365 prefixEnd_3214365 1650514243989421515854911 := by
  unfold tailWord_3214365
  simp only [CollatzResearch.WordTrace]
  refine ⟨117237522999912049681388549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78158348666608033120925699 117237522999912049681388549)
  ·
    refine ⟨21982035562483509315260353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117237522999912049681388549 21982035562483509315260353)
    ·
      refine ⟨16486526671862631986445265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21982035562483509315260353 16486526671862631986445265)
      ·
        refine ⟨12364895003896973989833949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16486526671862631986445265 12364895003896973989833949)
        ·
          refine ⟨4636835626461365246187731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12364895003896973989833949 4636835626461365246187731)
          ·
            refine ⟨6955253439692047869281597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636835626461365246187731 6955253439692047869281597)
            ·
              refine ⟨2608220039884517950980599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6955253439692047869281597 2608220039884517950980599)
              ·
                refine ⟨3912330059826776926470899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608220039884517950980599 3912330059826776926470899)
                ·
                  refine ⟨5868495089740165389706349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912330059826776926470899 5868495089740165389706349)
                  ·
                    refine ⟨2200685658652562021139881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5868495089740165389706349 2200685658652562021139881)
                    ·
                      refine ⟨1650514243989421515854911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200685658652562021139881 1650514243989421515854911)
                      ·
                        rfl

theorem cell23_3214365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_3214365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214365 prefixEnd_3214365 := by exact prefixLift 3214365
  have htrace : WordTrace (prefixWord ++ tailWord_3214365) baseStart_3214365 baseEnd_3214365 := by
    simpa [prefixWord, tailWord_3214365, baseEnd_3214365] using wordTrace_append hprefix tailTrace_3214365
  have hstable : (prefixWord ++ tailWord_3214365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214365).length < 2 ^ (prefixWord ++ tailWord_3214365).sum := by decide
  have hdescent : baseEnd_3214365 < baseStart_3214365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214384 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 5]
def baseStart_3214384 : Nat := 118140960795 + 3214384 * 2 ^ 59
def prefixEnd_3214384 : Nat := 4983230072969 + 3 ^ 40 * 3214384 * 2
def baseEnd_3214384 : Nat := 183391555569095215724147

theorem tailTrace_3214384 : CollatzResearch.WordTrace tailWord_3214384 prefixEnd_3214384 183391555569095215724147 := by
  unfold tailWord_3214384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58619107993421607963165103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78158810657895477284220137 58619107993421607963165103)
  ·
    refine ⟨87928661990132411944747655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58619107993421607963165103 87928661990132411944747655)
    ·
      refine ⟨131892992985198617917121483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87928661990132411944747655 131892992985198617917121483)
      ·
        refine ⟨197839489477797926875682225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131892992985198617917121483 197839489477797926875682225)
        ·
          refine ⟨148379617108348445156761669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197839489477797926875682225 148379617108348445156761669)
          ·
            refine ⟨27821178207815333466892813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148379617108348445156761669 27821178207815333466892813)
            ·
              refine ⟨10432941827930750050084805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27821178207815333466892813 10432941827930750050084805)
              ·
                refine ⟨1956176592737015634390901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10432941827930750050084805 1956176592737015634390901)
                ·
                  refine ⟨183391555569095215724147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956176592737015634390901 183391555569095215724147)
                  ·
                    rfl

theorem cell23_3214384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 5].length) (baseStart_3214384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214384 prefixEnd_3214384 := by exact prefixLift 3214384
  have htrace : WordTrace (prefixWord ++ tailWord_3214384) baseStart_3214384 baseEnd_3214384 := by
    simpa [prefixWord, tailWord_3214384, baseEnd_3214384] using wordTrace_append hprefix tailTrace_3214384
  have hstable : (prefixWord ++ tailWord_3214384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214384).length < 2 ^ (prefixWord ++ tailWord_3214384).sum := by decide
  have hdescent : baseEnd_3214384 < baseStart_3214384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214429 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3214429 : Nat := 118140960795 + 3214429 * 2 ^ 59
def prefixEnd_3214429 : Nat := 4983230072969 + 3 ^ 40 * 3214429 * 2
def baseEnd_3214429 : Nat := 1650547106751309265454617

theorem tailTrace_3214429 : CollatzResearch.WordTrace tailWord_3214429 prefixEnd_3214429 1650547106751309265454617 := by
  unfold tailWord_3214429
  simp only [CollatzResearch.WordTrace]
  refine ⟨117239857271680188611718341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78159904847786792407812227 117239857271680188611718341)
  ·
    refine ⟨21982473238440035364697189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117239857271680188611718341 21982473238440035364697189)
    ·
      refine ⟨4121713732207506630880723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21982473238440035364697189 4121713732207506630880723)
      ·
        refine ⟨6182570598311259946321085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121713732207506630880723 6182570598311259946321085)
        ·
          refine ⟨2318463974366722479870407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6182570598311259946321085 2318463974366722479870407)
          ·
            refine ⟨3477695961550083719805611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318463974366722479870407 3477695961550083719805611)
            ·
              refine ⟨5216543942325125579708417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477695961550083719805611 5216543942325125579708417)
              ·
                refine ⟨3912407956743844184781313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216543942325125579708417 3912407956743844184781313)
                ·
                  refine ⟨2934305967557883138585985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912407956743844184781313 2934305967557883138585985)
                  ·
                    refine ⟨2200729475668412353939489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934305967557883138585985 2200729475668412353939489)
                    ·
                      refine ⟨1650547106751309265454617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200729475668412353939489 1650547106751309265454617)
                      ·
                        rfl

theorem cell23_3214429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3214429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214429 prefixEnd_3214429 := by exact prefixLift 3214429
  have htrace : WordTrace (prefixWord ++ tailWord_3214429) baseStart_3214429 baseEnd_3214429 := by
    simpa [prefixWord, tailWord_3214429, baseEnd_3214429] using wordTrace_append hprefix tailTrace_3214429
  have hstable : (prefixWord ++ tailWord_3214429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214429).length < 2 ^ (prefixWord ++ tailWord_3214429).sum := by decide
  have hdescent : baseEnd_3214429 < baseStart_3214429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214447 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_3214447 : Nat := 118140960795 + 3214447 * 2 ^ 59
def prefixEnd_3214447 : Nat := 4983230072969 + 3 ^ 40 * 3214447 * 2
def baseEnd_3214447 : Nat := 1650556349403090195029533

theorem tailTrace_3214447 : CollatzResearch.WordTrace tailWord_3214447 prefixEnd_3214447 1650556349403090195029533 := by
  unfold tailWord_3214447
  simp only [CollatzResearch.WordTrace]
  refine ⟨117240513785614977685873595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78160342523743318457249063 117240513785614977685873595)
  ·
    refine ⟨175860770678422466528810393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117240513785614977685873595 175860770678422466528810393)
    ·
      refine ⟨131895578008816849896607795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175860770678422466528810393 131895578008816849896607795)
      ·
        refine ⟨197843367013225274844911693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131895578008816849896607795 197843367013225274844911693)
        ·
          refine ⟨74191262629959478066841885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197843367013225274844911693 74191262629959478066841885)
          ·
            refine ⟨27821723486234804275065707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74191262629959478066841885 27821723486234804275065707)
            ·
              refine ⟨41732585229352206412598561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27821723486234804275065707 41732585229352206412598561)
              ·
                refine ⟨31299438922014154809448921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41732585229352206412598561 31299438922014154809448921)
                ·
                  refine ⟨23474579191510616107086691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31299438922014154809448921 23474579191510616107086691)
                  ·
                    refine ⟨35211868787265924160630037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23474579191510616107086691 35211868787265924160630037)
                    ·
                      refine ⟨1650556349403090195029533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35211868787265924160630037 1650556349403090195029533)
                      ·
                        rfl

theorem cell23_3214447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_3214447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214447 prefixEnd_3214447 := by exact prefixLift 3214447
  have htrace : WordTrace (prefixWord ++ tailWord_3214447) baseStart_3214447 baseEnd_3214447 := by
    simpa [prefixWord, tailWord_3214447, baseEnd_3214447] using wordTrace_append hprefix tailTrace_3214447
  have hstable : (prefixWord ++ tailWord_3214447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214447).length < 2 ^ (prefixWord ++ tailWord_3214447).sum := by decide
  have hdescent : baseEnd_3214447 < baseStart_3214447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214495 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 3, 4]
def baseStart_3214495 : Nat := 118140960795 + 3214495 * 2 ^ 59
def prefixEnd_3214495 : Nat := 4983230072969 + 3 ^ 40 * 3214495 * 2
def baseEnd_3214495 : Nat := 550193665491502002409771

theorem tailTrace_3214495 : CollatzResearch.WordTrace tailWord_3214495 prefixEnd_3214495 550193665491502002409771 := by
  unfold tailWord_3214495
  simp only [CollatzResearch.WordTrace]
  refine ⟨117242264489441081883620939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78161509659627387922413959 117242264489441081883620939)
  ·
    refine ⟨175863396734161622825431409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117242264489441081883620939 175863396734161622825431409)
    ·
      refine ⟨131897547550621217119073557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175863396734161622825431409 131897547550621217119073557)
      ·
        refine ⟨6182697541435369552456573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131897547550621217119073557 6182697541435369552456573)
        ·
          refine ⟨2318511578038263582171215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6182697541435369552456573 2318511578038263582171215)
          ·
            refine ⟨3477767367057395373256823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318511578038263582171215 3477767367057395373256823)
            ·
              refine ⟨5216651050586093059885235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477767367057395373256823 5216651050586093059885235)
              ·
                refine ⟨7824976575879139589827853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216651050586093059885235 7824976575879139589827853)
                ·
                  refine ⟨2934366215954677346185445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7824976575879139589827853 2934366215954677346185445)
                  ·
                    refine ⟨550193665491502002409771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934366215954677346185445 550193665491502002409771)
                    ·
                      rfl

theorem cell23_3214495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 4].length) (baseStart_3214495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214495 prefixEnd_3214495 := by exact prefixLift 3214495
  have htrace : WordTrace (prefixWord ++ tailWord_3214495) baseStart_3214495 baseEnd_3214495 := by
    simpa [prefixWord, tailWord_3214495, baseEnd_3214495] using wordTrace_append hprefix tailTrace_3214495
  have hstable : (prefixWord ++ tailWord_3214495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214495).length < 2 ^ (prefixWord ++ tailWord_3214495).sum := by decide
  have hdescent : baseEnd_3214495 < baseStart_3214495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214521 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 1, 5]
def baseStart_3214521 : Nat := 118140960795 + 3214521 * 2 ^ 59
def prefixEnd_3214521 : Nat := 4983230072969 + 3 ^ 40 * 3214521 * 2
def baseEnd_3214521 : Nat := 550198115657174301834731

theorem tailTrace_3214521 : CollatzResearch.WordTrace tailWord_3214521 prefixEnd_3214521 550198115657174301834731 := by
  unfold tailWord_3214521
  simp only [CollatzResearch.WordTrace]
  refine ⟨117243212787346888324067417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78162141858231258882711611 117243212787346888324067417)
  ·
    refine ⟨87932409590510166243050563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117243212787346888324067417 87932409590510166243050563)
    ·
      refine ⟨131898614385765249364575845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87932409590510166243050563 131898614385765249364575845)
      ·
        refine ⟨24730990197330984255857971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131898614385765249364575845 24730990197330984255857971)
        ·
          refine ⟨37096485295996476383786957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24730990197330984255857971 37096485295996476383786957)
          ·
            refine ⟨13911181985998678643920109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37096485295996476383786957 13911181985998678643920109)
            ·
              refine ⟨5216693244749504491470041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13911181985998678643920109 5216693244749504491470041)
              ·
                refine ⟨3912519933562128368602531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216693244749504491470041 3912519933562128368602531)
                ·
                  refine ⟨5868779900343192552903797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912519933562128368602531 5868779900343192552903797)
                  ·
                    refine ⟨550198115657174301834731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5868779900343192552903797 550198115657174301834731)
                    ·
                      rfl

theorem cell23_3214521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_3214521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214521 prefixEnd_3214521 := by exact prefixLift 3214521
  have htrace : WordTrace (prefixWord ++ tailWord_3214521) baseStart_3214521 baseEnd_3214521 := by
    simpa [prefixWord, tailWord_3214521, baseEnd_3214521] using wordTrace_append hprefix tailTrace_3214521
  have hstable : (prefixWord ++ tailWord_3214521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214521).length < 2 ^ (prefixWord ++ tailWord_3214521).sum := by decide
  have hdescent : baseEnd_3214521 < baseStart_3214521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214538 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_3214538 : Nat := 118140960795 + 3214538 * 2 ^ 59
def prefixEnd_3214538 : Nat := 4983230072969 + 3 ^ 40 * 3214538 * 2
def baseEnd_3214538 : Nat := 550201025380883112997205

theorem tailTrace_3214538 : CollatzResearch.WordTrace tailWord_3214538 prefixEnd_3214538 550201025380883112997205 := by
  unfold tailWord_3214538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310958207071325056859067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78162555218856866818290845 29310958207071325056859067)
  ·
    refine ⟨43966437310606987585288601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29310958207071325056859067 43966437310606987585288601)
    ·
      refine ⟨32974827982955240688966451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43966437310606987585288601 32974827982955240688966451)
      ·
        refine ⟨49462241974432861033449677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32974827982955240688966451 49462241974432861033449677)
        ·
          refine ⟨18548340740412322887543629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49462241974432861033449677 18548340740412322887543629)
          ·
            refine ⟨6955627777654621082828861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18548340740412322887543629 6955627777654621082828861)
            ·
              refine ⟨2608360416620482906060823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6955627777654621082828861 2608360416620482906060823)
              ·
                refine ⟨3912540624930724359091235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608360416620482906060823 3912540624930724359091235)
                ·
                  refine ⟨5868810937396086538636853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912540624930724359091235 5868810937396086538636853)
                  ·
                    refine ⟨550201025380883112997205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5868810937396086538636853 550201025380883112997205)
                    ·
                      rfl

theorem cell23_3214538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_3214538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214538 prefixEnd_3214538 := by exact prefixLift 3214538
  have htrace : WordTrace (prefixWord ++ tailWord_3214538) baseStart_3214538 baseEnd_3214538 := by
    simpa [prefixWord, tailWord_3214538, baseEnd_3214538] using wordTrace_append hprefix tailTrace_3214538
  have hstable : (prefixWord ++ tailWord_3214538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214538).length < 2 ^ (prefixWord ++ tailWord_3214538).sum := by decide
  have hdescent : baseEnd_3214538 < baseStart_3214538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214551 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 2, 4]
def baseStart_3214551 : Nat := 118140960795 + 3214551 * 2 ^ 59
def prefixEnd_3214551 : Nat := 4983230072969 + 3 ^ 40 * 3214551 * 2
def baseEnd_3214551 : Nat := 550203250463719262709685

theorem tailTrace_3214551 : CollatzResearch.WordTrace tailWord_3214551 prefixEnd_3214551 550203250463719262709685 := by
  unfold tailWord_3214551
  simp only [CollatzResearch.WordTrace]
  refine ⟨117244306977238203447659507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78162871318158802298439671 117244306977238203447659507)
  ·
    refine ⟨175866460465857305171489261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117244306977238203447659507 175866460465857305171489261)
    ·
      refine ⟨65949922674696489439308473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175866460465857305171489261 65949922674696489439308473)
      ·
        refine ⟨49462442006022367079481355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65949922674696489439308473 49462442006022367079481355)
        ·
          refine ⟨74193663009033550619222033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49462442006022367079481355 74193663009033550619222033)
          ·
            refine ⟨55645247256775162964416525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74193663009033550619222033 55645247256775162964416525)
            ·
              refine ⟨20866967721290686111656197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55645247256775162964416525 20866967721290686111656197)
              ·
                refine ⟨3912556447742003645935537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20866967721290686111656197 3912556447742003645935537)
                ·
                  refine ⟨2934417335806502734451653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912556447742003645935537 2934417335806502734451653)
                  ·
                    refine ⟨550203250463719262709685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934417335806502734451653 550203250463719262709685)
                    ·
                      rfl

theorem cell23_3214551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_3214551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214551 prefixEnd_3214551 := by exact prefixLift 3214551
  have htrace : WordTrace (prefixWord ++ tailWord_3214551) baseStart_3214551 baseEnd_3214551 := by
    simpa [prefixWord, tailWord_3214551, baseEnd_3214551] using wordTrace_append hprefix tailTrace_3214551
  have hstable : (prefixWord ++ tailWord_3214551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214551).length < 2 ^ (prefixWord ++ tailWord_3214551).sum := by decide
  have hdescent : baseEnd_3214551 < baseStart_3214551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214554 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3214554 : Nat := 118140960795 + 3214554 * 2 ^ 59
def prefixEnd_3214554 : Nat := 4983230072969 + 3 ^ 40 * 3214554 * 2
def baseEnd_3214554 : Nat := 1650611291833121276391541

theorem tailTrace_3214554 : CollatzResearch.WordTrace tailWord_3214554 prefixEnd_3214554 1650611291833121276391541 := by
  unfold tailWord_3214554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29311104099056833740004679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78162944264151556640012477 29311104099056833740004679)
  ·
    refine ⟨43966656148585250610007019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29311104099056833740004679 43966656148585250610007019)
    ·
      refine ⟨65949984222877875915010529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43966656148585250610007019 65949984222877875915010529)
      ·
        refine ⟨49462488167158406936257897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65949984222877875915010529 49462488167158406936257897)
        ·
          refine ⟨37096866125368805202193423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49462488167158406936257897 37096866125368805202193423)
          ·
            refine ⟨55645299188053207803290135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37096866125368805202193423 55645299188053207803290135)
            ·
              refine ⟨83467948782079811704935203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55645299188053207803290135 83467948782079811704935203)
              ·
                refine ⟨125201923173119717557402805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83467948782079811704935203 125201923173119717557402805)
                ·
                  refine ⟨11737680297479973521006513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125201923173119717557402805 11737680297479973521006513)
                  ·
                    refine ⟨8803260223109980140754885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11737680297479973521006513 8803260223109980140754885)
                    ·
                      refine ⟨1650611291833121276391541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8803260223109980140754885 1650611291833121276391541)
                      ·
                        rfl

theorem cell23_3214554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3214554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214554 prefixEnd_3214554 := by exact prefixLift 3214554
  have htrace : WordTrace (prefixWord ++ tailWord_3214554) baseStart_3214554 baseEnd_3214554 := by
    simpa [prefixWord, tailWord_3214554, baseEnd_3214554] using wordTrace_append hprefix tailTrace_3214554
  have hstable : (prefixWord ++ tailWord_3214554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214554).length < 2 ^ (prefixWord ++ tailWord_3214554).sum := by decide
  have hdescent : baseEnd_3214554 < baseStart_3214554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214561 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_3214561 : Nat := 118140960795 + 3214561 * 2 ^ 59
def prefixEnd_3214561 : Nat := 4983230072969 + 3 ^ 40 * 3214561 * 2
def baseEnd_3214561 : Nat := 1650614886197702749004009

theorem tailTrace_3214561 : CollatzResearch.WordTrace tailWord_3214561 prefixEnd_3214561 1650614886197702749004009 := by
  unfold tailWord_3214561
  simp only [CollatzResearch.WordTrace]
  refine ⟨117244671707201975155523537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78163114471467983437015691 117244671707201975155523537)
  ·
    refine ⟨87933503780401481366642653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117244671707201975155523537 87933503780401481366642653)
    ·
      refine ⟨32975063917650555512490995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87933503780401481366642653 32975063917650555512490995)
      ·
        refine ⟨49462595876475833268736493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32975063917650555512490995 49462595876475833268736493)
        ·
          refine ⟨18548473453678437475776185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49462595876475833268736493 18548473453678437475776185)
          ·
            refine ⟨13911355090258828106832139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18548473453678437475776185 13911355090258828106832139)
            ·
              refine ⟨20867032635388242160248209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13911355090258828106832139 20867032635388242160248209)
              ·
                refine ⟨15650274476541181620186157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20867032635388242160248209 15650274476541181620186157)
                ·
                  refine ⟨5868852928702943107569809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15650274476541181620186157 5868852928702943107569809)
                  ·
                    refine ⟨4401639696527207330677357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868852928702943107569809 4401639696527207330677357)
                    ·
                      refine ⟨1650614886197702749004009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4401639696527207330677357 1650614886197702749004009)
                      ·
                        rfl

theorem cell23_3214561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_3214561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214561 prefixEnd_3214561 := by exact prefixLift 3214561
  have htrace : WordTrace (prefixWord ++ tailWord_3214561) baseStart_3214561 baseEnd_3214561 := by
    simpa [prefixWord, tailWord_3214561, baseEnd_3214561] using wordTrace_append hprefix tailTrace_3214561
  have hstable : (prefixWord ++ tailWord_3214561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214561).length < 2 ^ (prefixWord ++ tailWord_3214561).sum := by decide
  have hdescent : baseEnd_3214561 < baseStart_3214561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214564 : List Nat := [2, 3, 1, 1, 1, 2, 5, 8]
def baseStart_3214564 : Nat := 118140960795 + 3214564 * 2 ^ 59
def prefixEnd_3214564 : Nat := 4983230072969 + 3 ^ 40 * 3214564 * 2
def baseEnd_3214564 : Nat := 61133941727395045824685

theorem tailTrace_3214564 : CollatzResearch.WordTrace tailWord_3214564 prefixEnd_3214564 61133941727395045824685 := by
  unfold tailWord_3214564
  simp only [CollatzResearch.WordTrace]
  refine ⟨58622390563095553333941373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78163187417460737778588497 58622390563095553333941373)
  ·
    refine ⟨21983396461160832500228015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58622390563095553333941373 21983396461160832500228015)
    ·
      refine ⟨32975094691741248750342023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21983396461160832500228015 32975094691741248750342023)
      ·
        refine ⟨49462642037611873125513035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32975094691741248750342023 49462642037611873125513035)
        ·
          refine ⟨74193963056417809688269553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49462642037611873125513035 74193963056417809688269553)
          ·
            refine ⟨55645472292313357266202165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74193963056417809688269553 55645472292313357266202165)
            ·
              refine ⟨5216763027404377243706453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55645472292313357266202165 5216763027404377243706453)
              ·
                refine ⟨61133941727395045824685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5216763027404377243706453 61133941727395045824685)
                ·
                  rfl

theorem cell23_3214564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 8].length) (baseStart_3214564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214564 prefixEnd_3214564 := by exact prefixLift 3214564
  have htrace : WordTrace (prefixWord ++ tailWord_3214564) baseStart_3214564 baseEnd_3214564 := by
    simpa [prefixWord, tailWord_3214564, baseEnd_3214564] using wordTrace_append hprefix tailTrace_3214564
  have hstable : (prefixWord ++ tailWord_3214564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214564).length < 2 ^ (prefixWord ++ tailWord_3214564).sum := by decide
  have hdescent : baseEnd_3214564 < baseStart_3214564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214571 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 4]
def baseStart_3214571 : Nat := 118140960795 + 3214571 * 2 ^ 59
def prefixEnd_3214571 : Nat := 4983230072969 + 3 ^ 40 * 3214571 * 2
def baseEnd_3214571 : Nat := 1650620021004247709878963

theorem tailTrace_3214571 : CollatzResearch.WordTrace tailWord_3214571 prefixEnd_3214571 1650620021004247709878963 := by
  unfold tailWord_3214571
  simp only [CollatzResearch.WordTrace]
  refine ⟨117245036437165746863387567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78163357624777164575591711 117245036437165746863387567)
  ·
    refine ⟨175867554655748620295081351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117245036437165746863387567 175867554655748620295081351)
    ·
      refine ⟨263801331983622930442622027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175867554655748620295081351 263801331983622930442622027)
      ·
        refine ⟨395701997975434395663933041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263801331983622930442622027 395701997975434395663933041)
        ·
          refine ⟨296776498481575796747949781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395701997975434395663933041 296776498481575796747949781)
          ·
            refine ⟨6955699183161932736280073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 296776498481575796747949781 6955699183161932736280073)
            ·
              refine ⟨5216774387371449552210055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955699183161932736280073 5216774387371449552210055)
              ·
                refine ⟨7825161581057174328315083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216774387371449552210055 7825161581057174328315083)
                ·
                  refine ⟨11737742371585761492472625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7825161581057174328315083 11737742371585761492472625)
                  ·
                    refine ⟨8803306778689321119354469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11737742371585761492472625 8803306778689321119354469)
                    ·
                      refine ⟨1650620021004247709878963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8803306778689321119354469 1650620021004247709878963)
                      ·
                        rfl

theorem cell23_3214571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 4].length) (baseStart_3214571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214571 prefixEnd_3214571 := by exact prefixLift 3214571
  have htrace : WordTrace (prefixWord ++ tailWord_3214571) baseStart_3214571 baseEnd_3214571 := by
    simpa [prefixWord, tailWord_3214571, baseEnd_3214571] using wordTrace_append hprefix tailTrace_3214571
  have hstable : (prefixWord ++ tailWord_3214571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214571).length < 2 ^ (prefixWord ++ tailWord_3214571).sum := by decide
  have hdescent : baseEnd_3214571 < baseStart_3214571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214575 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 3, 2, 2]
def baseStart_3214575 : Nat := 118140960795 + 3214575 * 2 ^ 59
def prefixEnd_3214575 : Nat := 4983230072969 + 3 ^ 40 * 3214575 * 2
def baseEnd_3214575 : Nat := 1650622074926865694228945

theorem tailTrace_3214575 : CollatzResearch.WordTrace tailWord_3214575 prefixEnd_3214575 1650622074926865694228945 := by
  unfold tailWord_3214575
  simp only [CollatzResearch.WordTrace]
  refine ⟨117245182329151255546533179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78163454886100837031022119 117245182329151255546533179)
  ·
    refine ⟨175867773493726883319799769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117245182329151255546533179 175867773493726883319799769)
    ·
      refine ⟨131900830120295162489849827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175867773493726883319799769 131900830120295162489849827)
      ·
        refine ⟨197851245180442743734774741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131900830120295162489849827 197851245180442743734774741)
        ·
          refine ⟨4637138558916626806283783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 197851245180442743734774741 4637138558916626806283783)
          ·
            refine ⟨6955707838374940209425675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637138558916626806283783 6955707838374940209425675)
            ·
              refine ⟨10433561757562410314138513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955707838374940209425675 10433561757562410314138513)
              ·
                refine ⟨7825171318171807735603885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10433561757562410314138513 7825171318171807735603885)
                ·
                  refine ⟨2934439244314427900851457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7825171318171807735603885 2934439244314427900851457)
                  ·
                    refine ⟨2200829433235820925638593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934439244314427900851457 2200829433235820925638593)
                    ·
                      refine ⟨1650622074926865694228945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200829433235820925638593 1650622074926865694228945)
                      ·
                        rfl

theorem cell23_3214575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 2, 2].length) (baseStart_3214575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214575 prefixEnd_3214575 := by exact prefixLift 3214575
  have htrace : WordTrace (prefixWord ++ tailWord_3214575) baseStart_3214575 baseEnd_3214575 := by
    simpa [prefixWord, tailWord_3214575, baseEnd_3214575] using wordTrace_append hprefix tailTrace_3214575
  have hstable : (prefixWord ++ tailWord_3214575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214575).length < 2 ^ (prefixWord ++ tailWord_3214575).sum := by decide
  have hdescent : baseEnd_3214575 < baseStart_3214575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214591 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_3214591 : Nat := 118140960795 + 3214591 * 2 ^ 59
def prefixEnd_3214591 : Nat := 4983230072969 + 3 ^ 40 * 3214591 * 2
def baseEnd_3214591 : Nat := 1650630290617337631628871

theorem tailTrace_3214591 : CollatzResearch.WordTrace tailWord_3214591 prefixEnd_3214591 1650630290617337631628871 := by
  unfold tailWord_3214591
  simp only [CollatzResearch.WordTrace]
  refine ⟨117245765897093290279115627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78163843931395526852743751 117245765897093290279115627)
  ·
    refine ⟨175868648845639935418673441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117245765897093290279115627 175868648845639935418673441)
    ·
      refine ⟨131901486634229951564005081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175868648845639935418673441 131901486634229951564005081)
      ·
        refine ⟨98926114975672463673003811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131901486634229951564005081 98926114975672463673003811)
        ·
          refine ⟨148389172463508695509505717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98926114975672463673003811 148389172463508695509505717)
          ·
            refine ⟨13911484918453940204016161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148389172463508695509505717 13911484918453940204016161)
            ·
              refine ⟨10433613688840455153012121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13911484918453940204016161 10433613688840455153012121)
              ·
                refine ⟨7825210266630341364759091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10433613688840455153012121 7825210266630341364759091)
                ·
                  refine ⟨11737815399945512047138637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7825210266630341364759091 11737815399945512047138637)
                  ·
                    refine ⟨4401680774979567017676989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11737815399945512047138637 4401680774979567017676989)
                    ·
                      refine ⟨1650630290617337631628871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4401680774979567017676989 1650630290617337631628871)
                      ·
                        rfl

theorem cell23_3214591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_3214591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214591 prefixEnd_3214591 := by exact prefixLift 3214591
  have htrace : WordTrace (prefixWord ++ tailWord_3214591) baseStart_3214591 baseEnd_3214591 := by
    simpa [prefixWord, tailWord_3214591, baseEnd_3214591] using wordTrace_append hprefix tailTrace_3214591
  have hstable : (prefixWord ++ tailWord_3214591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214591).length < 2 ^ (prefixWord ++ tailWord_3214591).sum := by decide
  have hdescent : baseEnd_3214591 < baseStart_3214591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214595 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 1, 2, 3]
def baseStart_3214595 : Nat := 118140960795 + 3214595 * 2 ^ 59
def prefixEnd_3214595 : Nat := 4983230072969 + 3 ^ 40 * 3214595 * 2
def baseEnd_3214595 : Nat := 1650632344539955615978853

theorem tailTrace_3214595 : CollatzResearch.WordTrace tailWord_3214595 prefixEnd_3214595 1650632344539955615978853 := by
  unfold tailWord_3214595
  simp only [CollatzResearch.WordTrace]
  refine ⟨117245911789078798962261239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78163941192719199308174159 117245911789078798962261239)
  ·
    refine ⟨175868867683618198443391859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117245911789078798962261239 175868867683618198443391859)
    ·
      refine ⟨263803301525427297665087789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175868867683618198443391859 263803301525427297665087789)
      ·
        refine ⟨98926238072035236624407921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263803301525427297665087789 98926238072035236624407921)
        ·
          refine ⟨74194678554026427468305941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98926238072035236624407921 74194678554026427468305941)
          ·
            refine ⟨3477875557219988787576841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74194678554026427468305941 3477875557219988787576841)
            ·
              refine ⟨2608406667914991590682631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3477875557219988787576841 2608406667914991590682631)
              ·
                refine ⟨3912610001872487386023947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608406667914991590682631 3912610001872487386023947)
                ·
                  refine ⟨5868915002808731079035921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912610001872487386023947 5868915002808731079035921)
                  ·
                    refine ⟨4401686252106548309276941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868915002808731079035921 4401686252106548309276941)
                    ·
                      refine ⟨1650632344539955615978853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4401686252106548309276941 1650632344539955615978853)
                      ·
                        rfl

theorem cell23_3214595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_3214595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214595 prefixEnd_3214595 := by exact prefixLift 3214595
  have htrace : WordTrace (prefixWord ++ tailWord_3214595) baseStart_3214595 baseEnd_3214595 := by
    simpa [prefixWord, tailWord_3214595, baseEnd_3214595] using wordTrace_append hprefix tailTrace_3214595
  have hstable : (prefixWord ++ tailWord_3214595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214595).length < 2 ^ (prefixWord ++ tailWord_3214595).sum := by decide
  have hdescent : baseEnd_3214595 < baseStart_3214595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214622 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3214622 : Nat := 118140960795 + 3214622 * 2 ^ 59
def prefixEnd_3214622 : Nat := 4983230072969 + 3 ^ 40 * 3214622 * 2
def baseEnd_3214622 : Nat := 1650646208517627010341229

theorem tailTrace_3214622 : CollatzResearch.WordTrace tailWord_3214622 prefixEnd_3214622 1650646208517627010341229 := by
  unfold tailWord_3214622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655862069997622821686765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78164597706653988382329413 14655862069997622821686765)
  ·
    refine ⟨5495948276249108558132537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14655862069997622821686765 5495948276249108558132537)
    ·
      refine ⟨4121961207186831418599403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5495948276249108558132537 4121961207186831418599403)
      ·
        refine ⟨6182941810780247127899105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121961207186831418599403 6182941810780247127899105)
        ·
          refine ⟨4637206358085185345924329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6182941810780247127899105 4637206358085185345924329)
          ·
            refine ⟨3477904768563889009443247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4637206358085185345924329 3477904768563889009443247)
            ·
              refine ⟨5216857152845833514164871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477904768563889009443247 5216857152845833514164871)
              ·
                refine ⟨7825285729268750271247307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216857152845833514164871 7825285729268750271247307)
                ·
                  refine ⟨11737928593903125406870961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7825285729268750271247307 11737928593903125406870961)
                  ·
                    refine ⟨8803446445427344055153221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11737928593903125406870961 8803446445427344055153221)
                    ·
                      refine ⟨1650646208517627010341229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8803446445427344055153221 1650646208517627010341229)
                      ·
                        rfl

theorem cell23_3214622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3214622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214622 prefixEnd_3214622 := by exact prefixLift 3214622
  have htrace : WordTrace (prefixWord ++ tailWord_3214622) baseStart_3214622 baseEnd_3214622 := by
    simpa [prefixWord, tailWord_3214622, baseEnd_3214622] using wordTrace_append hprefix tailTrace_3214622
  have hstable : (prefixWord ++ tailWord_3214622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214622).length < 2 ^ (prefixWord ++ tailWord_3214622).sum := by decide
  have hdescent : baseEnd_3214622 < baseStart_3214622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214664 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3214664 : Nat := 118140960795 + 3214664 * 2 ^ 59
def prefixEnd_3214664 : Nat := 4983230072969 + 3 ^ 40 * 3214664 * 2
def baseEnd_3214664 : Nat := 1650667774705115846016035

theorem tailTrace_3214664 : CollatzResearch.WordTrace tailWord_3214664 prefixEnd_3214664 1650667774705115846016035 := by
  unfold tailWord_3214664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58624214212914411873261523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78165618950552549164348697 58624214212914411873261523)
  ·
    refine ⟨87936321319371617809892285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58624214212914411873261523 87936321319371617809892285)
    ·
      refine ⟨32976120494764356678709607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87936321319371617809892285 32976120494764356678709607)
      ·
        refine ⟨49464180742146535018064411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32976120494764356678709607 49464180742146535018064411)
        ·
          refine ⟨74196271113219802527096617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49464180742146535018064411 74196271113219802527096617)
          ·
            refine ⟨55647203334914851895322463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74196271113219802527096617 55647203334914851895322463)
            ·
              refine ⟨83470805002372277842983695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55647203334914851895322463 83470805002372277842983695)
              ·
                refine ⟨125206207503558416764475543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83470805002372277842983695 125206207503558416764475543)
                ·
                  refine ⟨187809311255337625146713315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125206207503558416764475543 187809311255337625146713315)
                  ·
                    refine ⟨281713966883006437720069973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187809311255337625146713315 281713966883006437720069973)
                    ·
                      refine ⟨1650667774705115846016035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 281713966883006437720069973 1650667774705115846016035)
                      ·
                        rfl

theorem cell23_3214664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3214664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214664 prefixEnd_3214664 := by exact prefixLift 3214664
  have htrace : WordTrace (prefixWord ++ tailWord_3214664) baseStart_3214664 baseEnd_3214664 := by
    simpa [prefixWord, tailWord_3214664, baseEnd_3214664] using wordTrace_append hprefix tailTrace_3214664
  have hstable : (prefixWord ++ tailWord_3214664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214664).length < 2 ^ (prefixWord ++ tailWord_3214664).sum := by decide
  have hdescent : baseEnd_3214664 < baseStart_3214664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214681 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_3214681 : Nat := 118140960795 + 3214681 * 2 ^ 59
def prefixEnd_3214681 : Nat := 4983230072969 + 3 ^ 40 * 3214681 * 2
def baseEnd_3214681 : Nat := 1650676503876242279503457

theorem tailTrace_3214681 : CollatzResearch.WordTrace tailWord_3214681 prefixEnd_3214681 1650676503876242279503457 := by
  unfold tailWord_3214681
  simp only [CollatzResearch.WordTrace]
  refine ⟨117249048466767235649891897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78166032311178157099927931 117249048466767235649891897)
  ·
    refine ⟨87936786350075426737418923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117249048466767235649891897 87936786350075426737418923)
    ·
      refine ⟨131905179525113140106128385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87936786350075426737418923 131905179525113140106128385)
      ·
        refine ⟨98928884643834855079596289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131905179525113140106128385 98928884643834855079596289)
        ·
          refine ⟨74196663482876141309697217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98928884643834855079596289 74196663482876141309697217)
          ·
            refine ⟨55647497612157105982272913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74196663482876141309697217 55647497612157105982272913)
            ·
              refine ⟨41735623209117829486704685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55647497612157105982272913 41735623209117829486704685)
              ·
                refine ⟨15650858703419186057514257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41735623209117829486704685 15650858703419186057514257)
                ·
                  refine ⟨11738144027564389543135693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15650858703419186057514257 11738144027564389543135693)
                  ·
                    refine ⟨4401804010336646078675885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11738144027564389543135693 4401804010336646078675885)
                    ·
                      refine ⟨1650676503876242279503457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4401804010336646078675885 1650676503876242279503457)
                      ·
                        rfl

theorem cell23_3214681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_3214681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214681 prefixEnd_3214681 := by exact prefixLift 3214681
  have htrace : WordTrace (prefixWord ++ tailWord_3214681) baseStart_3214681 baseEnd_3214681 := by
    simpa [prefixWord, tailWord_3214681, baseEnd_3214681] using wordTrace_append hprefix tailTrace_3214681
  have hstable : (prefixWord ++ tailWord_3214681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214681).length < 2 ^ (prefixWord ++ tailWord_3214681).sum := by decide
  have hdescent : baseEnd_3214681 < baseStart_3214681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214682 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2]
def baseStart_3214682 : Nat := 118140960795 + 3214682 * 2 ^ 59
def prefixEnd_3214682 : Nat := 4983230072969 + 3 ^ 40 * 3214682 * 2
def baseEnd_3214682 : Nat := 1650677017356896775590953

theorem tailTrace_3214682 : CollatzResearch.WordTrace tailWord_3214682 prefixEnd_3214682 1650677017356896775590953 := by
  unfold tailWord_3214682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29312271234940903205169575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78166056626509075213785533 29312271234940903205169575)
  ·
    refine ⟨43968406852411354807754363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29312271234940903205169575 43968406852411354807754363)
    ·
      refine ⟨65952610278617032211631545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43968406852411354807754363 65952610278617032211631545)
      ·
        refine ⟨49464457708962774158723659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65952610278617032211631545 49464457708962774158723659)
        ·
          refine ⟨74196686563444161238085489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49464457708962774158723659 74196686563444161238085489)
          ·
            refine ⟨55647514922583120928564117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74196686563444161238085489 55647514922583120928564117)
            ·
              refine ⟨2608477261996083793526443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55647514922583120928564117 2608477261996083793526443)
              ·
                refine ⟨3912715892994125690289665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608477261996083793526443 3912715892994125690289665)
                ·
                  refine ⟨2934536919745594267717249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912715892994125690289665 2934536919745594267717249)
                  ·
                    refine ⟨2200902689809195700787937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934536919745594267717249 2200902689809195700787937)
                    ·
                      refine ⟨1650677017356896775590953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200902689809195700787937 1650677017356896775590953)
                      ·
                        rfl

theorem cell23_3214682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_3214682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214682 prefixEnd_3214682 := by exact prefixLift 3214682
  have htrace : WordTrace (prefixWord ++ tailWord_3214682) baseStart_3214682 baseEnd_3214682 := by
    simpa [prefixWord, tailWord_3214682, baseEnd_3214682] using wordTrace_append hprefix tailTrace_3214682
  have hstable : (prefixWord ++ tailWord_3214682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214682).length < 2 ^ (prefixWord ++ tailWord_3214682).sum := by decide
  have hdescent : baseEnd_3214682 < baseStart_3214682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214722 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3214722 : Nat := 118140960795 + 3214722 * 2 ^ 59
def prefixEnd_3214722 : Nat := 4983230072969 + 3 ^ 40 * 3214722 * 2
def baseEnd_3214722 : Nat := 183410839620341846565641

theorem tailTrace_3214722 : CollatzResearch.WordTrace tailWord_3214722 prefixEnd_3214722 183410839620341846565641 := by
  unfold tailWord_3214722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29312635964904674913033605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78167029239745799768089613 29312635964904674913033605)
  ·
    refine ⟨5496119243419626546193801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29312635964904674913033605 5496119243419626546193801)
    ·
      refine ⟨4122089432564719909645351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5496119243419626546193801 4122089432564719909645351)
      ·
        refine ⟨6183134148847079864468027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4122089432564719909645351 6183134148847079864468027)
        ·
          refine ⟨9274701223270619796702041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6183134148847079864468027 9274701223270619796702041)
          ·
            refine ⟨6956025917452964847526531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9274701223270619796702041 6956025917452964847526531)
            ·
              refine ⟨10434038876179447271289797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956025917452964847526531 10434038876179447271289797)
              ·
                refine ⟨1956382289283646363366837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10434038876179447271289797 1956382289283646363366837)
                ·
                  refine ⟨183410839620341846565641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956382289283646363366837 183410839620341846565641)
                  ·
                    rfl

theorem cell23_3214722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3214722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214722 prefixEnd_3214722 := by exact prefixLift 3214722
  have htrace : WordTrace (prefixWord ++ tailWord_3214722) baseStart_3214722 baseEnd_3214722 := by
    simpa [prefixWord, tailWord_3214722, baseEnd_3214722] using wordTrace_append hprefix tailTrace_3214722
  have hstable : (prefixWord ++ tailWord_3214722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214722).length < 2 ^ (prefixWord ++ tailWord_3214722).sum := by decide
  have hdescent : baseEnd_3214722 < baseStart_3214722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214771 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 3]
def baseStart_3214771 : Nat := 118140960795 + 3214771 * 2 ^ 59
def prefixEnd_3214771 : Nat := 4983230072969 + 3 ^ 40 * 3214771 * 2
def baseEnd_3214771 : Nat := 1650722717135146927378043

theorem tailTrace_3214771 : CollatzResearch.WordTrace tailWord_3214771 prefixEnd_3214771 1650722717135146927378043 := by
  unfold tailWord_3214771
  simp only [CollatzResearch.WordTrace]
  refine ⟨117252331036441181020668167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78168220690960787347112111 117252331036441181020668167)
  ·
    refine ⟨175878496554661771531002251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117252331036441181020668167 175878496554661771531002251)
    ·
      refine ⟨263817744831992657296503377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175878496554661771531002251 263817744831992657296503377)
      ·
        refine ⟨197863308623994492972377533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263817744831992657296503377 197863308623994492972377533)
        ·
          refine ⟨74198740733997934864641575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197863308623994492972377533 74198740733997934864641575)
          ·
            refine ⟨111298111100996902296962363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74198740733997934864641575 111298111100996902296962363)
            ·
              refine ⟨166947166651495353445443545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111298111100996902296962363 166947166651495353445443545)
              ·
                refine ⟨125210374988621515084082659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166947166651495353445443545 125210374988621515084082659)
                ·
                  refine ⟨187815562482932272626123989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125210374988621515084082659 187815562482932272626123989)
                  ·
                    refine ⟨4401927245693725139674781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 187815562482932272626123989 4401927245693725139674781)
                    ·
                      refine ⟨1650722717135146927378043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4401927245693725139674781 1650722717135146927378043)
                      ·
                        rfl

theorem cell23_3214771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_3214771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214771 prefixEnd_3214771 := by exact prefixLift 3214771
  have htrace : WordTrace (prefixWord ++ tailWord_3214771) baseStart_3214771 baseEnd_3214771 := by
    simpa [prefixWord, tailWord_3214771, baseEnd_3214771] using wordTrace_append hprefix tailTrace_3214771
  have hstable : (prefixWord ++ tailWord_3214771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214771).length < 2 ^ (prefixWord ++ tailWord_3214771).sum := by decide
  have hdescent : baseEnd_3214771 < baseStart_3214771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214781 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3214781 : Nat := 118140960795 + 3214781 * 2 ^ 59
def prefixEnd_3214781 : Nat := 4983230072969 + 3 ^ 40 * 3214781 * 2
def baseEnd_3214781 : Nat := 1650727851941691888252997

theorem tailTrace_3214781 : CollatzResearch.WordTrace tailWord_3214781 prefixEnd_3214781 1650727851941691888252997 := by
  unfold tailWord_3214781
  simp only [CollatzResearch.WordTrace]
  refine ⟨117252695766404952728532197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78168463844269968485688131 117252695766404952728532197)
  ·
    refine ⟨21984880456200928636599787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117252695766404952728532197 21984880456200928636599787)
    ·
      refine ⟨32977320684301392954899681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21984880456200928636599787 32977320684301392954899681)
      ·
        refine ⟨24732990513226044716174761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32977320684301392954899681 24732990513226044716174761)
        ·
          refine ⟨18549742884919533537131071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24732990513226044716174761 18549742884919533537131071)
          ·
            refine ⟨27824614327379300305696607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18549742884919533537131071 27824614327379300305696607)
            ·
              refine ⟨41736921491068950458544911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27824614327379300305696607 41736921491068950458544911)
              ·
                refine ⟨62605382236603425687817367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41736921491068950458544911 62605382236603425687817367)
                ·
                  refine ⟨93908073354905138531726051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62605382236603425687817367 93908073354905138531726051)
                  ·
                    refine ⟨140862110032357707797589077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93908073354905138531726051 140862110032357707797589077)
                    ·
                      refine ⟨1650727851941691888252997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 140862110032357707797589077 1650727851941691888252997)
                      ·
                        rfl

theorem cell23_3214781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3214781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214781 prefixEnd_3214781 := by exact prefixLift 3214781
  have htrace : WordTrace (prefixWord ++ tailWord_3214781) baseStart_3214781 baseEnd_3214781 := by
    simpa [prefixWord, tailWord_3214781, baseEnd_3214781] using wordTrace_append hprefix tailTrace_3214781
  have hstable : (prefixWord ++ tailWord_3214781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214781).length < 2 ^ (prefixWord ++ tailWord_3214781).sum := by decide
  have hdescent : baseEnd_3214781 < baseStart_3214781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214805 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3214805 : Nat := 118140960795 + 3214805 * 2 ^ 59
def prefixEnd_3214805 : Nat := 4983230072969 + 3 ^ 40 * 3214805 * 2
def baseEnd_3214805 : Nat := 1650740175477399794352887

theorem tailTrace_3214805 : CollatzResearch.WordTrace tailWord_3214805 prefixEnd_3214805 1650740175477399794352887 := by
  unfold tailWord_3214805
  simp only [CollatzResearch.WordTrace]
  refine ⟨117253571118318004827405869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78169047412212003218270579 117253571118318004827405869)
  ·
    refine ⟨43970089169369251810277201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117253571118318004827405869 43970089169369251810277201)
    ·
      refine ⟨32977566877026938857707901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43970089169369251810277201 32977566877026938857707901)
      ·
        refine ⟨12366587578885102071640463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32977566877026938857707901 12366587578885102071640463)
        ·
          refine ⟨18549881368327653107460695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12366587578885102071640463 18549881368327653107460695)
          ·
            refine ⟨27824822052491479661191043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18549881368327653107460695 27824822052491479661191043)
            ·
              refine ⟨41737233078737219491786565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27824822052491479661191043 41737233078737219491786565)
              ·
                refine ⟨7825731202263228654709981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41737233078737219491786565 7825731202263228654709981)
                ·
                  refine ⟨2934649200848710745516243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7825731202263228654709981 2934649200848710745516243)
                  ·
                    refine ⟨4401973801273066118274365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2934649200848710745516243 4401973801273066118274365)
                    ·
                      refine ⟨1650740175477399794352887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4401973801273066118274365 1650740175477399794352887)
                      ·
                        rfl

theorem cell23_3214805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3214805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214805 prefixEnd_3214805 := by exact prefixLift 3214805
  have htrace : WordTrace (prefixWord ++ tailWord_3214805) baseStart_3214805 baseEnd_3214805 := by
    simpa [prefixWord, tailWord_3214805, baseEnd_3214805] using wordTrace_append hprefix tailTrace_3214805
  have hstable : (prefixWord ++ tailWord_3214805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214805).length < 2 ^ (prefixWord ++ tailWord_3214805).sum := by decide
  have hdescent : baseEnd_3214805 < baseStart_3214805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214808 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 1, 5]
def baseStart_3214808 : Nat := 118140960795 + 3214808 * 2 ^ 59
def prefixEnd_3214808 : Nat := 4983230072969 + 3 ^ 40 * 3214808 * 2
def baseEnd_3214808 : Nat := 550247238639787760871791

theorem tailTrace_3214808 : CollatzResearch.WordTrace tailWord_3214808 prefixEnd_3214808 550247238639787760871791 := by
  unfold tailWord_3214808
  simp only [CollatzResearch.WordTrace]
  refine ⟨58626840268653568169882539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78169120358204757559843385 58626840268653568169882539)
  ·
    refine ⟨87940260402980352254823809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58626840268653568169882539 87940260402980352254823809)
    ·
      refine ⟨65955195302235264191117857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87940260402980352254823809 65955195302235264191117857)
      ·
        refine ⟨49466396476676448143338393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65955195302235264191117857 49466396476676448143338393)
        ·
          refine ⟨37099797357507336107503795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49466396476676448143338393 37099797357507336107503795)
          ·
            refine ⟨55649696036261004161255693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37099797357507336107503795 55649696036261004161255693)
            ·
              refine ⟨20868636013597876560470885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55649696036261004161255693 20868636013597876560470885)
              ·
                refine ⟨3912869252549601855088291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20868636013597876560470885 3912869252549601855088291)
                ·
                  refine ⟨5869303878824402782632437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912869252549601855088291 5869303878824402782632437)
                  ·
                    refine ⟨550247238639787760871791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5869303878824402782632437 550247238639787760871791)
                    ·
                      rfl

theorem cell23_3214808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_3214808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214808 prefixEnd_3214808 := by exact prefixLift 3214808
  have htrace : WordTrace (prefixWord ++ tailWord_3214808) baseStart_3214808 baseEnd_3214808 := by
    simpa [prefixWord, tailWord_3214808, baseEnd_3214808] using wordTrace_append hprefix tailTrace_3214808
  have hstable : (prefixWord ++ tailWord_3214808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214808).length < 2 ^ (prefixWord ++ tailWord_3214808).sum := by decide
  have hdescent : baseEnd_3214808 < baseStart_3214808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214815 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 2, 3, 2]
def baseStart_3214815 : Nat := 118140960795 + 3214815 * 2 ^ 59
def prefixEnd_3214815 : Nat := 4983230072969 + 3 ^ 40 * 3214815 * 2
def baseEnd_3214815 : Nat := 1650745310283944755227841

theorem tailTrace_3214815 : CollatzResearch.WordTrace tailWord_3214815 prefixEnd_3214815 1650745310283944755227841 := by
  unfold tailWord_3214815
  simp only [CollatzResearch.WordTrace]
  refine ⟨117253935848281776535269899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78169290565521184356846599 117253935848281776535269899)
  ·
    refine ⟨175880903772422664802904849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117253935848281776535269899 175880903772422664802904849)
    ·
      refine ⟨131910677829316998602178637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175880903772422664802904849 131910677829316998602178637)
      ·
        refine ⟨49466504185993874475816989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131910677829316998602178637 49466504185993874475816989)
        ·
          refine ⟨18549939069747702928431371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49466504185993874475816989 18549939069747702928431371)
          ·
            refine ⟨27824908604621554392647057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18549939069747702928431371 27824908604621554392647057)
            ·
              refine ⟨20868681453466165794485293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27824908604621554392647057 20868681453466165794485293)
              ·
                refine ⟨7825755545049812172931985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20868681453466165794485293 7825755545049812172931985)
                ·
                  refine ⟨5869316658787359129698989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7825755545049812172931985 5869316658787359129698989)
                  ·
                    refine ⟨2200993747045259673637121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5869316658787359129698989 2200993747045259673637121)
                    ·
                      refine ⟨1650745310283944755227841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2200993747045259673637121 1650745310283944755227841)
                      ·
                        rfl

theorem cell23_3214815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_3214815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214815 prefixEnd_3214815 := by exact prefixLift 3214815
  have htrace : WordTrace (prefixWord ++ tailWord_3214815) baseStart_3214815 baseEnd_3214815 := by
    simpa [prefixWord, tailWord_3214815, baseEnd_3214815] using wordTrace_append hprefix tailTrace_3214815
  have hstable : (prefixWord ++ tailWord_3214815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214815).length < 2 ^ (prefixWord ++ tailWord_3214815).sum := by decide
  have hdescent : baseEnd_3214815 < baseStart_3214815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214846 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3214846 : Nat := 118140960795 + 3214846 * 2 ^ 59
def prefixEnd_3214846 : Nat := 4983230072969 + 3 ^ 40 * 3214846 * 2
def baseEnd_3214846 : Nat := 183417914242692681548911

theorem tailTrace_3214846 : CollatzResearch.WordTrace tailWord_3214846 prefixEnd_3214846 183417914242692681548911 := by
  unfold tailWord_3214846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14656883313896183603706049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78170044340779645886432261 14656883313896183603706049)
  ·
    refine ⟨10992662485422137702779537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14656883313896183603706049 10992662485422137702779537)
    ·
      refine ⟨8244496864066603277084653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10992662485422137702779537 8244496864066603277084653)
      ·
        refine ⟨3091686324024976228906745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8244496864066603277084653 3091686324024976228906745)
        ·
          refine ⟨2318764743018732171680059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091686324024976228906745 2318764743018732171680059)
          ·
            refine ⟨3478147114528098257520089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318764743018732171680059 3478147114528098257520089)
            ·
              refine ⟨2608610335896073693140067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3478147114528098257520089 2608610335896073693140067)
              ·
                refine ⟨3912915503844110539710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608610335896073693140067 3912915503844110539710101)
                ·
                  refine ⟨183417914242692681548911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3912915503844110539710101 183417914242692681548911)
                  ·
                    rfl

theorem cell23_3214846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3214846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214846 prefixEnd_3214846 := by exact prefixLift 3214846
  have htrace : WordTrace (prefixWord ++ tailWord_3214846) baseStart_3214846 baseEnd_3214846 := by
    simpa [prefixWord, tailWord_3214846, baseEnd_3214846] using wordTrace_append hprefix tailTrace_3214846
  have hstable : (prefixWord ++ tailWord_3214846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214846).length < 2 ^ (prefixWord ++ tailWord_3214846).sum := by decide
  have hdescent : baseEnd_3214846 < baseStart_3214846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214858 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3214858 : Nat := 118140960795 + 3214858 * 2 ^ 59
def prefixEnd_3214858 : Nat := 4983230072969 + 3 ^ 40 * 3214858 * 2
def baseEnd_3214858 : Nat := 1650767389952088086990143

theorem tailTrace_3214858 : CollatzResearch.WordTrace tailWord_3214858 prefixEnd_3214858 1650767389952088086990143 := by
  unfold tailWord_3214858
  simp only [CollatzResearch.WordTrace]
  refine ⟨29313876046781498719771307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78170336124750663252723485 29313876046781498719771307)
  ·
    refine ⟨43970814070172248079656961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29313876046781498719771307 43970814070172248079656961)
    ·
      refine ⟨32978110552629186059742721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43970814070172248079656961 32978110552629186059742721)
      ·
        refine ⟨24733582914471889544807041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32978110552629186059742721 24733582914471889544807041)
        ·
          refine ⟨18550187185853917158605281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24733582914471889544807041 18550187185853917158605281)
          ·
            refine ⟨13912640389390437868953961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18550187185853917158605281 13912640389390437868953961)
            ·
              refine ⟨10434480292042828401715471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13912640389390437868953961 10434480292042828401715471)
              ·
                refine ⟨15651720438064242602573207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10434480292042828401715471 15651720438064242602573207)
                ·
                  refine ⟨23477580657096363903859811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15651720438064242602573207 23477580657096363903859811)
                  ·
                    refine ⟨35216370985644545855789717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23477580657096363903859811 35216370985644545855789717)
                    ·
                      refine ⟨1650767389952088086990143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35216370985644545855789717 1650767389952088086990143)
                      ·
                        rfl

theorem cell23_3214858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3214858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214858 prefixEnd_3214858 := by exact prefixLift 3214858
  have htrace : WordTrace (prefixWord ++ tailWord_3214858) baseStart_3214858 baseEnd_3214858 := by
    simpa [prefixWord, tailWord_3214858, baseEnd_3214858] using wordTrace_append hprefix tailTrace_3214858
  have hstable : (prefixWord ++ tailWord_3214858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214858).length < 2 ^ (prefixWord ++ tailWord_3214858).sum := by decide
  have hdescent : baseEnd_3214858 < baseStart_3214858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214891 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_3214891 : Nat := 118140960795 + 3214891 * 2 ^ 59
def prefixEnd_3214891 : Nat := 4983230072969 + 3 ^ 40 * 3214891 * 2
def baseEnd_3214891 : Nat := 1650784334813686457877491

theorem tailTrace_3214891 : CollatzResearch.WordTrace tailWord_3214891 prefixEnd_3214891 1650784334813686457877491 := by
  unfold tailWord_3214891
  simp only [CollatzResearch.WordTrace]
  refine ⟨117256707796006441515036527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78171138530670961010024351 117256707796006441515036527)
  ·
    refine ⟨175885061694009662272554791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117256707796006441515036527 175885061694009662272554791)
    ·
      refine ⟨263827592541014493408832187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175885061694009662272554791 263827592541014493408832187)
      ·
        refine ⟨395741388811521740113248281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263827592541014493408832187 395741388811521740113248281)
        ·
          refine ⟨296806041608641305084936211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395741388811521740113248281 296806041608641305084936211)
          ·
            refine ⟨445209062412961957627404317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296806041608641305084936211 445209062412961957627404317)
            ·
              refine ⟨166953398404860734110276619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445209062412961957627404317 166953398404860734110276619)
              ·
                refine ⟨250430097607291101165414929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166953398404860734110276619 250430097607291101165414929)
                ·
                  refine ⟨187822573205468325874061197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250430097607291101165414929 187822573205468325874061197)
                  ·
                    refine ⟨70433464952050622202772949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187822573205468325874061197 70433464952050622202772949)
                    ·
                      refine ⟨1650784334813686457877491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70433464952050622202772949 1650784334813686457877491)
                      ·
                        rfl

theorem cell23_3214891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_3214891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214891 prefixEnd_3214891 := by exact prefixLift 3214891
  have htrace : WordTrace (prefixWord ++ tailWord_3214891) baseStart_3214891 baseEnd_3214891 := by
    simpa [prefixWord, tailWord_3214891, baseEnd_3214891] using wordTrace_append hprefix tailTrace_3214891
  have hstable : (prefixWord ++ tailWord_3214891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214891).length < 2 ^ (prefixWord ++ tailWord_3214891).sum := by decide
  have hdescent : baseEnd_3214891 < baseStart_3214891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214902 : List Nat := [5, 1, 2, 1, 3, 2, 1, 8]
def baseStart_3214902 : Nat := 118140960795 + 3214902 * 2 ^ 59
def prefixEnd_3214902 : Nat := 4983230072969 + 3 ^ 40 * 3214902 * 2
def baseEnd_3214902 : Nat := 61140369744477256105183

theorem tailTrace_3214902 : CollatzResearch.WordTrace tailWord_3214902 prefixEnd_3214902 61140369744477256105183 := by
  unfold tailWord_3214902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328569312435411899605435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78171405999311060262457973 7328569312435411899605435)
  ·
    refine ⟨10992853968653117849408153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7328569312435411899605435 10992853968653117849408153)
    ·
      refine ⟨8244640476489838387056115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10992853968653117849408153 8244640476489838387056115)
      ·
        refine ⟨12366960714734757580584173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8244640476489838387056115 12366960714734757580584173)
        ·
          refine ⟨4637610268025534092719065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12366960714734757580584173 4637610268025534092719065)
          ·
            refine ⟨3478207701019150569539299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4637610268025534092719065 3478207701019150569539299)
            ·
              refine ⟨5217311551528725854308949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478207701019150569539299 5217311551528725854308949)
              ·
                refine ⟨61140369744477256105183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5217311551528725854308949 61140369744477256105183)
                ·
                  rfl

theorem cell23_3214902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_3214902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214902 prefixEnd_3214902 := by exact prefixLift 3214902
  have htrace : WordTrace (prefixWord ++ tailWord_3214902) baseStart_3214902 baseEnd_3214902 := by
    simpa [prefixWord, tailWord_3214902, baseEnd_3214902] using wordTrace_append hprefix tailTrace_3214902
  have hstable : (prefixWord ++ tailWord_3214902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214902).length < 2 ^ (prefixWord ++ tailWord_3214902).sum := by decide
  have hdescent : baseEnd_3214902 < baseStart_3214902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214922 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_3214922 : Nat := 118140960795 + 3214922 * 2 ^ 59
def prefixEnd_3214922 : Nat := 4983230072969 + 3 ^ 40 * 3214922 * 2
def baseEnd_3214922 : Nat := 1650800252713975836589849

theorem tailTrace_3214922 : CollatzResearch.WordTrace tailWord_3214922 prefixEnd_3214922 1650800252713975836589849 := by
  unfold tailWord_3214922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29314459614723533452353755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78171892305929422539610013 29314459614723533452353755)
  ·
    refine ⟨43971689422085300178530633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29314459614723533452353755 43971689422085300178530633)
    ·
      refine ⟨32978767066563975133897975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43971689422085300178530633 32978767066563975133897975)
      ·
        refine ⟨49468150599845962700846963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32978767066563975133897975 49468150599845962700846963)
        ·
          refine ⟨74202225899768944051270445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49468150599845962700846963 74202225899768944051270445)
          ·
            refine ⟨27825834712413354019226417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74202225899768944051270445 27825834712413354019226417)
            ·
              refine ⟨20869376034310015514419813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27825834712413354019226417 20869376034310015514419813)
              ·
                refine ⟨3913008006433127908953715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20869376034310015514419813 3913008006433127908953715)
                ·
                  refine ⟨5869512009649691863430573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913008006433127908953715 5869512009649691863430573)
                  ·
                    refine ⟨2201067003618634448786465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5869512009649691863430573 2201067003618634448786465)
                    ·
                      refine ⟨1650800252713975836589849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201067003618634448786465 1650800252713975836589849)
                      ·
                        rfl

theorem cell23_3214922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_3214922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214922 prefixEnd_3214922 := by exact prefixLift 3214922
  have htrace : WordTrace (prefixWord ++ tailWord_3214922) baseStart_3214922 baseEnd_3214922 := by
    simpa [prefixWord, tailWord_3214922, baseEnd_3214922] using wordTrace_append hprefix tailTrace_3214922
  have hstable : (prefixWord ++ tailWord_3214922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214922).length < 2 ^ (prefixWord ++ tailWord_3214922).sum := by decide
  have hdescent : baseEnd_3214922 < baseStart_3214922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214938 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3214938 : Nat := 118140960795 + 3214938 * 2 ^ 59
def prefixEnd_3214938 : Nat := 4983230072969 + 3 ^ 40 * 3214938 * 2
def baseEnd_3214938 : Nat := 1650808468404447773989775

theorem tailTrace_3214938 : CollatzResearch.WordTrace tailWord_3214938 prefixEnd_3214938 1650808468404447773989775 := by
  unfold tailWord_3214938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29314605506709042135499367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78172281351224112361331645 29314605506709042135499367)
  ·
    refine ⟨43971908260063563203249051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29314605506709042135499367 43971908260063563203249051)
    ·
      refine ⟨65957862390095344804873577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43971908260063563203249051 65957862390095344804873577)
      ·
        refine ⟨49468396792571508603655183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65957862390095344804873577 49468396792571508603655183)
        ·
          refine ⟨74202595188857262905482775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49468396792571508603655183 74202595188857262905482775)
          ·
            refine ⟨111303892783285894358224163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74202595188857262905482775 111303892783285894358224163)
            ·
              refine ⟨166955839174928841537336245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111303892783285894358224163 166955839174928841537336245)
              ·
                refine ⟨15652109922649578894125273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166955839174928841537336245 15652109922649578894125273)
                ·
                  refine ⟨11739082441987184170593955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15652109922649578894125273 11739082441987184170593955)
                  ·
                    refine ⟨17608623662980776255890933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11739082441987184170593955 17608623662980776255890933)
                    ·
                      refine ⟨1650808468404447773989775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17608623662980776255890933 1650808468404447773989775)
                      ·
                        rfl

theorem cell23_3214938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3214938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214938 prefixEnd_3214938 := by exact prefixLift 3214938
  have htrace : WordTrace (prefixWord ++ tailWord_3214938) baseStart_3214938 baseEnd_3214938 := by
    simpa [prefixWord, tailWord_3214938, baseEnd_3214938] using wordTrace_append hprefix tailTrace_3214938
  have hstable : (prefixWord ++ tailWord_3214938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214938).length < 2 ^ (prefixWord ++ tailWord_3214938).sum := by decide
  have hdescent : baseEnd_3214938 < baseStart_3214938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214988 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_3214988 : Nat := 118140960795 + 3214988 * 2 ^ 59
def prefixEnd_3214988 : Nat := 4983230072969 + 3 ^ 40 * 3214988 * 2
def baseEnd_3214988 : Nat := 550278047479057526121515

theorem tailTrace_3214988 : CollatzResearch.WordTrace tailWord_3214988 prefixEnd_3214988 550278047479057526121515 := by
  unfold tailWord_3214988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58630122838327513540658809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78173497117770018054211745 58630122838327513540658809)
  ·
    refine ⟨43972592128745635155494107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58630122838327513540658809 43972592128745635155494107)
    ·
      refine ⟨65958888193118452733241161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43972592128745635155494107 65958888193118452733241161)
      ·
        refine ⟨49469166144838839549930871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65958888193118452733241161 49469166144838839549930871)
        ·
          refine ⟨74203749217258259324896307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49469166144838839549930871 74203749217258259324896307)
          ·
            refine ⟨111305623825887388987344461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74203749217258259324896307 111305623825887388987344461)
            ·
              refine ⟨41739608934707770870254173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111305623825887388987344461 41739608934707770870254173)
              ·
                refine ⟨15652353350515414076345315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41739608934707770870254173 15652353350515414076345315)
                ·
                  refine ⟨23478530025773121114517973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15652353350515414076345315 23478530025773121114517973)
                  ·
                    refine ⟨550278047479057526121515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23478530025773121114517973 550278047479057526121515)
                    ·
                      rfl

theorem cell23_3214988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_3214988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214988 prefixEnd_3214988 := by exact prefixLift 3214988
  have htrace : WordTrace (prefixWord ++ tailWord_3214988) baseStart_3214988 baseEnd_3214988 := by
    simpa [prefixWord, tailWord_3214988, baseEnd_3214988] using wordTrace_append hprefix tailTrace_3214988
  have hstable : (prefixWord ++ tailWord_3214988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214988).length < 2 ^ (prefixWord ++ tailWord_3214988).sum := by decide
  have hdescent : baseEnd_3214988 < baseStart_3214988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215009 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 5]
def baseStart_3215009 : Nat := 118140960795 + 3215009 * 2 ^ 59
def prefixEnd_3215009 : Nat := 4983230072969 + 3 ^ 40 * 3215009 * 2
def baseEnd_3215009 : Nat := 183427213947879666244661

theorem tailTrace_3215009 : CollatzResearch.WordTrace tailWord_3215009 prefixEnd_3215009 183427213947879666244661 := by
  unfold tailWord_3215009
  simp only [CollatzResearch.WordTrace]
  refine ⟨117261011609578947667832081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78174007739719298445221387 117261011609578947667832081)
  ·
    refine ⟨87945758707184210750874061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117261011609578947667832081 87945758707184210750874061)
    ·
      refine ⟨32979659515194079031577773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87945758707184210750874061 32979659515194079031577773)
      ·
        refine ⟨12367372318197779636841665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32979659515194079031577773 12367372318197779636841665)
        ·
          refine ⟨9275529238648334727631249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12367372318197779636841665 9275529238648334727631249)
          ·
            refine ⟨6956646928986251045723437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9275529238648334727631249 6956646928986251045723437)
            ·
              refine ⟨2608742598369844142146289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6956646928986251045723437 2608742598369844142146289)
              ·
                refine ⟨1956556948777383106609717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608742598369844142146289 1956556948777383106609717)
                ·
                  refine ⟨183427213947879666244661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956556948777383106609717 183427213947879666244661)
                  ·
                    rfl

theorem cell23_3215009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 5].length) (baseStart_3215009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215009 prefixEnd_3215009 := by exact prefixLift 3215009
  have htrace : WordTrace (prefixWord ++ tailWord_3215009) baseStart_3215009 baseEnd_3215009 := by
    simpa [prefixWord, tailWord_3215009, baseEnd_3215009] using wordTrace_append hprefix tailTrace_3215009
  have hstable : (prefixWord ++ tailWord_3215009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215009).length < 2 ^ (prefixWord ++ tailWord_3215009).sum := by decide
  have hdescent : baseEnd_3215009 < baseStart_3215009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215035 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 3, 4]
def baseStart_3215035 : Nat := 118140960795 + 3215035 * 2 ^ 59
def prefixEnd_3215035 : Nat := 4983230072969 + 3 ^ 40 * 3215035 * 2
def baseEnd_3215035 : Nat := 550286092009311298158943

theorem tailTrace_3215035 : CollatzResearch.WordTrace tailWord_3215035 prefixEnd_3215035 550286092009311298158943 := by
  unfold tailWord_3215035
  simp only [CollatzResearch.WordTrace]
  refine ⟨117261959907484754108278559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78174639938323169405519039 117261959907484754108278559)
  ·
    refine ⟨175892939861227131162417839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117261959907484754108278559 175892939861227131162417839)
    ·
      refine ⟨263839409791840696743626759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175892939861227131162417839 263839409791840696743626759)
      ·
        refine ⟨395759114687761045115440139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263839409791840696743626759 395759114687761045115440139)
        ·
          refine ⟨593638672031641567673160209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395759114687761045115440139 593638672031641567673160209)
          ·
            refine ⟨445229004023731175754870157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593638672031641567673160209 445229004023731175754870157)
            ·
              refine ⟨166960876508899190908076309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445229004023731175754870157 166960876508899190908076309)
              ·
                refine ⟨7826291086354649573816077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166960876508899190908076309 7826291086354649573816077)
                ·
                  refine ⟨2934859157382993590181029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7826291086354649573816077 2934859157382993590181029)
                  ·
                    refine ⟨550286092009311298158943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934859157382993590181029 550286092009311298158943)
                    ·
                      rfl

theorem cell23_3215035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 4].length) (baseStart_3215035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215035 prefixEnd_3215035 := by exact prefixLift 3215035
  have htrace : WordTrace (prefixWord ++ tailWord_3215035) baseStart_3215035 baseEnd_3215035 := by
    simpa [prefixWord, tailWord_3215035, baseEnd_3215035] using wordTrace_append hprefix tailTrace_3215035
  have hstable : (prefixWord ++ tailWord_3215035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215035).length < 2 ^ (prefixWord ++ tailWord_3215035).sum := by decide
  have hdescent : baseEnd_3215035 < baseStart_3215035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215045 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_3215045 : Nat := 118140960795 + 3215045 * 2 ^ 59
def prefixEnd_3215045 : Nat := 4983230072969 + 3 ^ 40 * 3215045 * 2
def baseEnd_3215045 : Nat := 1650863410834478855351783

theorem tailTrace_3215045 : CollatzResearch.WordTrace tailWord_3215045 prefixEnd_3215045 1650863410834478855351783 := by
  unfold tailWord_3215045
  simp only [CollatzResearch.WordTrace]
  refine ⟨117262324637448525816142589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78174883091632350544095059 117262324637448525816142589)
  ·
    refine ⟨43973371739043197181053471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117262324637448525816142589 43973371739043197181053471)
    ·
      refine ⟨65960057608564795771580207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43973371739043197181053471 65960057608564795771580207)
      ·
        refine ⟨98940086412847193657370311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65960057608564795771580207 98940086412847193657370311)
        ·
          refine ⟨148410129619270790486055467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98940086412847193657370311 148410129619270790486055467)
          ·
            refine ⟨222615194428906185729083201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148410129619270790486055467 222615194428906185729083201)
            ·
              refine ⟨166961395821679639296812401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222615194428906185729083201 166961395821679639296812401)
              ·
                refine ⟨125221046866259729472609301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166961395821679639296812401 125221046866259729472609301)
                ·
                  refine ⟨5869736571855924819028561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125221046866259729472609301 5869736571855924819028561)
                  ·
                    refine ⟨4402302428891943614271421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5869736571855924819028561 4402302428891943614271421)
                    ·
                      refine ⟨1650863410834478855351783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4402302428891943614271421 1650863410834478855351783)
                      ·
                        rfl

theorem cell23_3215045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_3215045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215045 prefixEnd_3215045 := by exact prefixLift 3215045
  have htrace : WordTrace (prefixWord ++ tailWord_3215045) baseStart_3215045 baseEnd_3215045 := by
    simpa [prefixWord, tailWord_3215045, baseEnd_3215045] using wordTrace_append hprefix tailTrace_3215045
  have hstable : (prefixWord ++ tailWord_3215045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215045).length < 2 ^ (prefixWord ++ tailWord_3215045).sum := by decide
  have hdescent : baseEnd_3215045 < baseStart_3215045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215065 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 6]
def baseStart_3215065 : Nat := 118140960795 + 3215065 * 2 ^ 59
def prefixEnd_3215065 : Nat := 4983230072969 + 3 ^ 40 * 3215065 * 2
def baseEnd_3215065 : Nat := 183430408938618753011299

theorem tailTrace_3215065 : CollatzResearch.WordTrace tailWord_3215065 prefixEnd_3215065 183430408938618753011299 := by
  unfold tailWord_3215065
  simp only [CollatzResearch.WordTrace]
  refine ⟨117263054097376069231870649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78175369398250712821247099 117263054097376069231870649)
  ·
    refine ⟨87947290573032051923902987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117263054097376069231870649 87947290573032051923902987)
    ·
      refine ⟨131920935859548077885854481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87947290573032051923902987 131920935859548077885854481)
      ·
        refine ⟨98940701894661058414390861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131920935859548077885854481 98940701894661058414390861)
        ·
          refine ⟨37102763210497896905396573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98940701894661058414390861 37102763210497896905396573)
          ·
            refine ⟨13913536203936711339523715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37102763210497896905396573 13913536203936711339523715)
            ·
              refine ⟨20870304305905067009285573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13913536203936711339523715 20870304305905067009285573)
              ·
                refine ⟨3913182057357200064241045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20870304305905067009285573 3913182057357200064241045)
                ·
                  refine ⟨183430408938618753011299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3913182057357200064241045 183430408938618753011299)
                  ·
                    rfl

theorem cell23_3215065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_3215065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215065 prefixEnd_3215065 := by exact prefixLift 3215065
  have htrace : WordTrace (prefixWord ++ tailWord_3215065) baseStart_3215065 baseEnd_3215065 := by
    simpa [prefixWord, tailWord_3215065, baseEnd_3215065] using wordTrace_append hprefix tailTrace_3215065
  have hstable : (prefixWord ++ tailWord_3215065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215065).length < 2 ^ (prefixWord ++ tailWord_3215065).sum := by decide
  have hdescent : baseEnd_3215065 < baseStart_3215065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215095 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 3, 5]
def baseStart_3215095 : Nat := 118140960795 + 3215095 * 2 ^ 59
def prefixEnd_3215095 : Nat := 4983230072969 + 3 ^ 40 * 3215095 * 2
def baseEnd_3215095 : Nat := 550296361622401219908851

theorem tailTrace_3215095 : CollatzResearch.WordTrace tailWord_3215095 prefixEnd_3215095 550296361622401219908851 := by
  unfold tailWord_3215095
  simp only [CollatzResearch.WordTrace]
  refine ⟨117264148287267384355462739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78176098858178256236975159 117264148287267384355462739)
  ·
    refine ⟨175896222430901076533194109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117264148287267384355462739 175896222430901076533194109)
    ·
      refine ⟨65961083411587903699947791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175896222430901076533194109 65961083411587903699947791)
      ·
        refine ⟨98941625117381855549921687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65961083411587903699947791 98941625117381855549921687)
        ·
          refine ⟨148412437676072783324882531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98941625117381855549921687 148412437676072783324882531)
          ·
            refine ⟨222618656514109174987323797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148412437676072783324882531 222618656514109174987323797)
            ·
              refine ⟨10435249524098867577530803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222618656514109174987323797 10435249524098867577530803)
              ·
                refine ⟨15652874286148301366296205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435249524098867577530803 15652874286148301366296205)
                ·
                  refine ⟨5869827857305613012361077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15652874286148301366296205 5869827857305613012361077)
                  ·
                    refine ⟨550296361622401219908851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5869827857305613012361077 550296361622401219908851)
                    ·
                      rfl

theorem cell23_3215095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_3215095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215095 prefixEnd_3215095 := by exact prefixLift 3215095
  have htrace : WordTrace (prefixWord ++ tailWord_3215095) baseStart_3215095 baseEnd_3215095 := by
    simpa [prefixWord, tailWord_3215095, baseEnd_3215095] using wordTrace_append hprefix tailTrace_3215095
  have hstable : (prefixWord ++ tailWord_3215095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215095).length < 2 ^ (prefixWord ++ tailWord_3215095).sum := by decide
  have hdescent : baseEnd_3215095 < baseStart_3215095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215112 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 1, 5]
def baseStart_3215112 : Nat := 118140960795 + 3215112 * 2 ^ 59
def prefixEnd_3215112 : Nat := 4983230072969 + 3 ^ 40 * 3215112 * 2
def baseEnd_3215112 : Nat := 550299271346110031071325

theorem tailTrace_3215112 : CollatzResearch.WordTrace tailWord_3215112 prefixEnd_3215112 550299271346110031071325 := by
  unfold tailWord_3215112
  simp only [CollatzResearch.WordTrace]
  refine ⟨58632384164102898129415795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78176512218803864172554393 58632384164102898129415795)
  ·
    refine ⟨87948576246154347194123693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58632384164102898129415795 87948576246154347194123693)
    ·
      refine ⟨32980716092307880197796385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87948576246154347194123693 32980716092307880197796385)
      ·
        refine ⟨24735537069230910148347289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32980716092307880197796385 24735537069230910148347289)
        ·
          refine ⟨18551652801923182611260467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24735537069230910148347289 18551652801923182611260467)
          ·
            refine ⟨27827479202884773916890701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18551652801923182611260467 27827479202884773916890701)
            ·
              refine ⟨10435304701081790218834013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27827479202884773916890701 10435304701081790218834013)
              ·
                refine ⟨3913239262905671332062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10435304701081790218834013 3913239262905671332062755)
                ·
                  refine ⟨5869858894358506998094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913239262905671332062755 5869858894358506998094133)
                  ·
                    refine ⟨550299271346110031071325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5869858894358506998094133 550299271346110031071325)
                    ·
                      rfl

theorem cell23_3215112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_3215112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215112 prefixEnd_3215112 := by exact prefixLift 3215112
  have htrace : WordTrace (prefixWord ++ tailWord_3215112) baseStart_3215112 baseEnd_3215112 := by
    simpa [prefixWord, tailWord_3215112, baseEnd_3215112] using wordTrace_append hprefix tailTrace_3215112
  have hstable : (prefixWord ++ tailWord_3215112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215112).length < 2 ^ (prefixWord ++ tailWord_3215112).sum := by decide
  have hdescent : baseEnd_3215112 < baseStart_3215112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215192 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 9, 2]
def baseStart_3215192 : Nat := 118140960795 + 3215192 * 2 ^ 59
def prefixEnd_3215192 : Nat := 4983230072969 + 3 ^ 40 * 3215192 * 2
def baseEnd_3215192 : Nat := 1650938892490689780213607

theorem tailTrace_3215192 : CollatzResearch.WordTrace tailWord_3215192 prefixEnd_3215192 1650938892490689780213607 := by
  unfold tailWord_3215192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58633843083957984960871915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78178457445277313281162553 58633843083957984960871915)
  ·
    refine ⟨87950764625936977441307873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58633843083957984960871915 87950764625936977441307873)
    ·
      refine ⟨65963073469452733080980905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87950764625936977441307873 65963073469452733080980905)
      ·
        refine ⟨49472305102089549810735679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65963073469452733080980905 49472305102089549810735679)
        ·
          refine ⟨74208457653134324716103519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49472305102089549810735679 74208457653134324716103519)
          ·
            refine ⟨111312686479701487074155279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74208457653134324716103519 111312686479701487074155279)
            ·
              refine ⟨166969029719552230611232919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111312686479701487074155279 166969029719552230611232919)
              ·
                refine ⟨250453544579328345916849379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166969029719552230611232919 250453544579328345916849379)
                ·
                  refine ⟨375680316868992518875274069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250453544579328345916849379 375680316868992518875274069)
                  ·
                    refine ⟨2201251856654253040284809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 375680316868992518875274069 2201251856654253040284809)
                    ·
                      refine ⟨1650938892490689780213607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201251856654253040284809 1650938892490689780213607)
                      ·
                        rfl

theorem cell23_3215192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_3215192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215192 prefixEnd_3215192 := by exact prefixLift 3215192
  have htrace : WordTrace (prefixWord ++ tailWord_3215192) baseStart_3215192 baseEnd_3215192 := by
    simpa [prefixWord, tailWord_3215192, baseEnd_3215192] using wordTrace_append hprefix tailTrace_3215192
  have hstable : (prefixWord ++ tailWord_3215192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215192).length < 2 ^ (prefixWord ++ tailWord_3215192).sum := by decide
  have hdescent : baseEnd_3215192 < baseStart_3215192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215203 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 1, 2, 3]
def baseStart_3215203 : Nat := 118140960795 + 3215203 * 2 ^ 59
def prefixEnd_3215203 : Nat := 4983230072969 + 3 ^ 40 * 3215203 * 2
def baseEnd_3215203 : Nat := 1650944540777889237176057

theorem tailTrace_3215203 : CollatzResearch.WordTrace tailWord_3215203 prefixEnd_3215203 1650944540777889237176057 := by
  unfold tailWord_3215203
  simp only [CollatzResearch.WordTrace]
  refine ⟨117268087370876118800394263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78178724913917412533596175 117268087370876118800394263)
  ·
    refine ⟨175902131056314178200591395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117268087370876118800394263 175902131056314178200591395)
    ·
      refine ⟨263853196584471267300887093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175902131056314178200591395 263853196584471267300887093)
      ·
        refine ⟨24736237179794181309458165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263853196584471267300887093 24736237179794181309458165)
        ·
          refine ⟨2319022235605704497761703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24736237179794181309458165 2319022235605704497761703)
          ·
            refine ⟨3478533353408556746642555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319022235605704497761703 3478533353408556746642555)
            ·
              refine ⟨5217800030112835119963833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478533353408556746642555 5217800030112835119963833)
              ·
                refine ⟨3913350022584626339972875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5217800030112835119963833 3913350022584626339972875)
                ·
                  refine ⟨5870025033876939509959313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913350022584626339972875 5870025033876939509959313)
                  ·
                    refine ⟨4402518775407704632469485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5870025033876939509959313 4402518775407704632469485)
                    ·
                      refine ⟨1650944540777889237176057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4402518775407704632469485 1650944540777889237176057)
                      ·
                        rfl

theorem cell23_3215203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_3215203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215203 prefixEnd_3215203 := by exact prefixLift 3215203
  have htrace : WordTrace (prefixWord ++ tailWord_3215203) baseStart_3215203 baseEnd_3215203 := by
    simpa [prefixWord, tailWord_3215203, baseEnd_3215203] using wordTrace_append hprefix tailTrace_3215203
  have hstable : (prefixWord ++ tailWord_3215203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215203).length < 2 ^ (prefixWord ++ tailWord_3215203).sum := by decide
  have hdescent : baseEnd_3215203 < baseStart_3215203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215205 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3215205 : Nat := 118140960795 + 3215205 * 2 ^ 59
def prefixEnd_3215205 : Nat := 4983230072969 + 3 ^ 40 * 3215205 * 2
def baseEnd_3215205 : Nat := 1650945567739198229351047

theorem tailTrace_3215205 : CollatzResearch.WordTrace tailWord_3215205 prefixEnd_3215205 1650945567739198229351047 := by
  unfold tailWord_3215205
  simp only [CollatzResearch.WordTrace]
  refine ⟨117268160316868873141967069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78178773544579248761311379 117268160316868873141967069)
  ·
    refine ⟨43975560118825827428237651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117268160316868873141967069 43975560118825827428237651)
    ·
      refine ⟨65963340178238741142356477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43975560118825827428237651 65963340178238741142356477)
      ·
        refine ⟨24736252566839527928383679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65963340178238741142356477 24736252566839527928383679)
        ·
          refine ⟨37104378850259291892575519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24736252566839527928383679 37104378850259291892575519)
          ·
            refine ⟨55656568275388937838863279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37104378850259291892575519 55656568275388937838863279)
            ·
              refine ⟨83484852413083406758294919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55656568275388937838863279 83484852413083406758294919)
              ·
                refine ⟨125227278619625110137442379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83484852413083406758294919 125227278619625110137442379)
                ·
                  refine ⟨187840917929437665206163569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125227278619625110137442379 187840917929437665206163569)
                  ·
                    refine ⟨140880688447078248904622677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187840917929437665206163569 140880688447078248904622677)
                    ·
                      refine ⟨1650945567739198229351047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 140880688447078248904622677 1650945567739198229351047)
                      ·
                        rfl

theorem cell23_3215205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3215205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215205 prefixEnd_3215205 := by exact prefixLift 3215205
  have htrace : WordTrace (prefixWord ++ tailWord_3215205) baseStart_3215205 baseEnd_3215205 := by
    simpa [prefixWord, tailWord_3215205, baseEnd_3215205] using wordTrace_append hprefix tailTrace_3215205
  have hstable : (prefixWord ++ tailWord_3215205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215205).length < 2 ^ (prefixWord ++ tailWord_3215205).sum := by decide
  have hdescent : baseEnd_3215205 < baseStart_3215205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215215 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 6, 6]
def baseStart_3215215 : Nat := 118140960795 + 3215215 * 2 ^ 59
def prefixEnd_3215215 : Nat := 4983230072969 + 3 ^ 40 * 3215215 * 2
def baseEnd_3215215 : Nat := 550316900848581063408667

theorem tailTrace_3215215 : CollatzResearch.WordTrace tailWord_3215215 prefixEnd_3215215 550316900848581063408667 := by
  unfold tailWord_3215215
  simp only [CollatzResearch.WordTrace]
  refine ⟨117268525046832644849831099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78179016697888429899887399 117268525046832644849831099)
  ·
    refine ⟨175902787570248967274746649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117268525046832644849831099 175902787570248967274746649)
    ·
      refine ⟨131927090677686725456059987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175902787570248967274746649 131927090677686725456059987)
      ·
        refine ⟨197890636016530088184089981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131927090677686725456059987 197890636016530088184089981)
        ·
          refine ⟨74208988506198783069033743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197890636016530088184089981 74208988506198783069033743)
          ·
            refine ⟨111313482759298174603550615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74208988506198783069033743 111313482759298174603550615)
            ·
              refine ⟨166970224138947261905325923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111313482759298174603550615 166970224138947261905325923)
              ·
                refine ⟨250455336208420892857988885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166970224138947261905325923 250455336208420892857988885)
                ·
                  refine ⟨11740093884769729352718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 250455336208420892857988885 11740093884769729352718229)
                  ·
                    refine ⟨550316900848581063408667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11740093884769729352718229 550316900848581063408667)
                    ·
                      rfl

theorem cell23_3215215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_3215215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215215 prefixEnd_3215215 := by exact prefixLift 3215215
  have htrace : WordTrace (prefixWord ++ tailWord_3215215) baseStart_3215215 baseEnd_3215215 := by
    simpa [prefixWord, tailWord_3215215, baseEnd_3215215] using wordTrace_append hprefix tailTrace_3215215
  have hstable : (prefixWord ++ tailWord_3215215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215215).length < 2 ^ (prefixWord ++ tailWord_3215215).sum := by decide
  have hdescent : baseEnd_3215215 < baseStart_3215215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215279 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 5]
def baseStart_3215279 : Nat := 118140960795 + 3215279 * 2 ^ 59
def prefixEnd_3215279 : Nat := 4983230072969 + 3 ^ 40 * 3215279 * 2
def baseEnd_3215279 : Nat := 183442618367514548869523

theorem tailTrace_3215279 : CollatzResearch.WordTrace tailWord_3215279 prefixEnd_3215279 183442618367514548869523 := by
  unfold tailWord_3215279
  simp only [CollatzResearch.WordTrace]
  refine ⟨117270859318600783780160891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78180572879067189186773927 117270859318600783780160891)
  ·
    refine ⟨175906288977901175670241337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117270859318600783780160891 175906288977901175670241337)
    ·
      refine ⟨131929716733425881752681003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175906288977901175670241337 131929716733425881752681003)
      ·
        refine ⟨197894575100138822629021505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131929716733425881752681003 197894575100138822629021505)
        ·
          refine ⟨148420931325104116971766129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197894575100138822629021505 148420931325104116971766129)
          ·
            refine ⟨111315698493828087728824597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148420931325104116971766129 111315698493828087728824597)
            ·
              refine ⟨5217923366898191612288653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111315698493828087728824597 5217923366898191612288653)
              ·
                refine ⟨1956721262586821854608245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5217923366898191612288653 1956721262586821854608245)
                ·
                  refine ⟨183442618367514548869523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956721262586821854608245 183442618367514548869523)
                  ·
                    rfl

theorem cell23_3215279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 5].length) (baseStart_3215279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215279 prefixEnd_3215279 := by exact prefixLift 3215279
  have htrace : WordTrace (prefixWord ++ tailWord_3215279) baseStart_3215279 baseEnd_3215279 := by
    simpa [prefixWord, tailWord_3215279, baseEnd_3215279] using wordTrace_append hprefix tailTrace_3215279
  have hstable : (prefixWord ++ tailWord_3215279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215279).length < 2 ^ (prefixWord ++ tailWord_3215279).sum := by decide
  have hdescent : baseEnd_3215279 < baseStart_3215279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215312 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_3215312 : Nat := 118140960795 + 3215312 * 2 ^ 59
def prefixEnd_3215312 : Nat := 4983230072969 + 3 ^ 40 * 3215312 * 2
def baseEnd_3215312 : Nat := 1651000510169229310713055

theorem tailTrace_3215312 : CollatzResearch.WordTrace tailWord_3215312 prefixEnd_3215312 1651000510169229310713055 := by
  unfold tailWord_3215312
  simp only [CollatzResearch.WordTrace]
  refine ⟨58636031463740615208056095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78181375284987486944074793 58636031463740615208056095)
  ·
    refine ⟨87954047195610922812084143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58636031463740615208056095 87954047195610922812084143)
    ·
      refine ⟨131931070793416384218126215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87954047195610922812084143 131931070793416384218126215)
      ·
        refine ⟨197896606190124576327189323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131931070793416384218126215 197896606190124576327189323)
        ·
          refine ⟨296844909285186864490783985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197896606190124576327189323 296844909285186864490783985)
          ·
            refine ⟨222633681963890148368087989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296844909285186864490783985 222633681963890148368087989)
            ·
              refine ⟨20871907684114701409508249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222633681963890148368087989 20871907684114701409508249)
              ·
                refine ⟨15653930763086026057131187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20871907684114701409508249 15653930763086026057131187)
                ·
                  refine ⟨23480896144629039085696781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15653930763086026057131187 23480896144629039085696781)
                  ·
                    refine ⟨8805336054235889657136293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23480896144629039085696781 8805336054235889657136293)
                    ·
                      refine ⟨1651000510169229310713055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8805336054235889657136293 1651000510169229310713055)
                      ·
                        rfl

theorem cell23_3215312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_3215312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215312 prefixEnd_3215312 := by exact prefixLift 3215312
  have htrace : WordTrace (prefixWord ++ tailWord_3215312) baseStart_3215312 baseEnd_3215312 := by
    simpa [prefixWord, tailWord_3215312, baseEnd_3215312] using wordTrace_append hprefix tailTrace_3215312
  have hstable : (prefixWord ++ tailWord_3215312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215312).length < 2 ^ (prefixWord ++ tailWord_3215312).sum := by decide
  have hdescent : baseEnd_3215312 < baseStart_3215312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215329 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_3215329 : Nat := 118140960795 + 3215329 * 2 ^ 59
def prefixEnd_3215329 : Nat := 4983230072969 + 3 ^ 40 * 3215329 * 2
def baseEnd_3215329 : Nat := 1651009239340355744200477

theorem tailTrace_3215329 : CollatzResearch.WordTrace tailWord_3215329 prefixEnd_3215329 1651009239340355744200477 := by
  unfold tailWord_3215329
  simp only [CollatzResearch.WordTrace]
  refine ⟨117272682968419642319481041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78181788645613094879654027 117272682968419642319481041)
  ·
    refine ⟨87954512226314731739610781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117272682968419642319481041 87954512226314731739610781)
    ·
      refine ⟨32982942084868024402354043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87954512226314731739610781 32982942084868024402354043)
      ·
        refine ⟨49474413127302036603531065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32982942084868024402354043 49474413127302036603531065)
        ·
          refine ⟨37105809845476527452648299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49474413127302036603531065 37105809845476527452648299)
          ·
            refine ⟨55658714768214791178972449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37105809845476527452648299 55658714768214791178972449)
            ·
              refine ⟨41744036076161093384229337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55658714768214791178972449 41744036076161093384229337)
              ·
                refine ⟨31308027057120820038172003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41744036076161093384229337 31308027057120820038172003)
                ·
                  refine ⟨46962040585681230057258005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31308027057120820038172003 46962040585681230057258005)
                  ·
                    refine ⟨2201345652453807658933969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46962040585681230057258005 2201345652453807658933969)
                    ·
                      refine ⟨1651009239340355744200477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201345652453807658933969 1651009239340355744200477)
                      ·
                        rfl

theorem cell23_3215329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_3215329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215329 prefixEnd_3215329 := by exact prefixLift 3215329
  have htrace : WordTrace (prefixWord ++ tailWord_3215329) baseStart_3215329 baseEnd_3215329 := by
    simpa [prefixWord, tailWord_3215329, baseEnd_3215329] using wordTrace_append hprefix tailTrace_3215329
  have hstable : (prefixWord ++ tailWord_3215329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215329).length < 2 ^ (prefixWord ++ tailWord_3215329).sum := by decide
  have hdescent : baseEnd_3215329 < baseStart_3215329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215330 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_3215330 : Nat := 118140960795 + 3215330 * 2 ^ 59
def prefixEnd_3215330 : Nat := 4983230072969 + 3 ^ 40 * 3215330 * 2
def baseEnd_3215330 : Nat := 183445528091223360031997

theorem tailTrace_3215330 : CollatzResearch.WordTrace tailWord_3215330 prefixEnd_3215330 183445528091223360031997 := by
  unfold tailWord_3215330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29318179860354004872566861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78181812960944012993511629 29318179860354004872566861)
  ·
    refine ⟨10994317447632751827212573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29318179860354004872566861 10994317447632751827212573)
    ·
      refine ⟨4122869042862281935204715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10994317447632751827212573 4122869042862281935204715)
      ·
        refine ⟨6184303564293422902807073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4122869042862281935204715 6184303564293422902807073)
        ·
          refine ⟨4638227673220067177105305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184303564293422902807073 4638227673220067177105305)
          ·
            refine ⟨3478670754915050382828979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4638227673220067177105305 3478670754915050382828979)
            ·
              refine ⟨5218006132372575574243469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478670754915050382828979 5218006132372575574243469)
              ·
                refine ⟨1956752299639715840341301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5218006132372575574243469 1956752299639715840341301)
                ·
                  refine ⟨183445528091223360031997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956752299639715840341301 183445528091223360031997)
                  ·
                    rfl

theorem cell23_3215330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_3215330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215330 prefixEnd_3215330 := by exact prefixLift 3215330
  have htrace : WordTrace (prefixWord ++ tailWord_3215330) baseStart_3215330 baseEnd_3215330 := by
    simpa [prefixWord, tailWord_3215330, baseEnd_3215330] using wordTrace_append hprefix tailTrace_3215330
  have hstable : (prefixWord ++ tailWord_3215330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215330).length < 2 ^ (prefixWord ++ tailWord_3215330).sum := by decide
  have hdescent : baseEnd_3215330 < baseStart_3215330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215352 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 8]
def baseStart_3215352 : Nat := 118140960795 + 3215352 * 2 ^ 59
def prefixEnd_3215352 : Nat := 4983230072969 + 3 ^ 40 * 3215352 * 2
def baseEnd_3215352 : Nat := 183446783266156572690319

theorem tailTrace_3215352 : CollatzResearch.WordTrace tailWord_3215352 prefixEnd_3215352 183446783266156572690319 := by
  unfold tailWord_3215352
  simp only [CollatzResearch.WordTrace]
  refine ⟨58636760923668158623784155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78182347898224211498378873 58636760923668158623784155)
  ·
    refine ⟨87955141385502237935676233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58636760923668158623784155 87955141385502237935676233)
    ·
      refine ⟨65966356039126678451757175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87955141385502237935676233 65966356039126678451757175)
      ·
        refine ⟨98949534058690017677635763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65966356039126678451757175 98949534058690017677635763)
        ·
          refine ⟨148424301088035026516453645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98949534058690017677635763 148424301088035026516453645)
          ·
            refine ⟨55659112908013134943670117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148424301088035026516453645 55659112908013134943670117)
            ·
              refine ⟨10436083670252462801938147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55659112908013134943670117 10436083670252462801938147)
              ·
                refine ⟨15654125505378694202907221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10436083670252462801938147 15654125505378694202907221)
                ·
                  refine ⟨183446783266156572690319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15654125505378694202907221 183446783266156572690319)
                  ·
                    rfl

theorem cell23_3215352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_3215352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215352 prefixEnd_3215352 := by exact prefixLift 3215352
  have htrace : WordTrace (prefixWord ++ tailWord_3215352) baseStart_3215352 baseEnd_3215352 := by
    simpa [prefixWord, tailWord_3215352, baseEnd_3215352] using wordTrace_append hprefix tailTrace_3215352
  have hstable : (prefixWord ++ tailWord_3215352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215352).length < 2 ^ (prefixWord ++ tailWord_3215352).sum := by decide
  have hdescent : baseEnd_3215352 < baseStart_3215352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215380 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3215380 : Nat := 118140960795 + 3215380 * 2 ^ 59
def prefixEnd_3215380 : Nat := 4983230072969 + 3 ^ 40 * 3215380 * 2
def baseEnd_3215380 : Nat := 1651035426853735044662743

theorem tailTrace_3215380 : CollatzResearch.WordTrace tailWord_3215380 prefixEnd_3215380 1651035426853735044662743 := by
  unfold tailWord_3215380
  simp only [CollatzResearch.WordTrace]
  refine ⟨58637271545617439014793797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78183028727489918686391729 58637271545617439014793797)
  ·
    refine ⟨10994488414803269815273837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58637271545617439014793797 10994488414803269815273837)
    ·
      refine ⟨4122933155551226180727689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10994488414803269815273837 4122933155551226180727689)
      ·
        refine ⟨3092199866663419635545767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4122933155551226180727689 3092199866663419635545767)
        ·
          refine ⟨4638299799995129453318651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092199866663419635545767 4638299799995129453318651)
          ·
            refine ⟨6957449699992694179977977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638299799995129453318651 6957449699992694179977977)
            ·
              refine ⟨5218087274994520634983483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6957449699992694179977977 5218087274994520634983483)
              ·
                refine ⟨7827130912491780952475225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218087274994520634983483 7827130912491780952475225)
                ·
                  refine ⟨5870348184368835714356419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7827130912491780952475225 5870348184368835714356419)
                  ·
                    refine ⟨8805522276553253571534629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5870348184368835714356419 8805522276553253571534629)
                    ·
                      refine ⟨1651035426853735044662743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8805522276553253571534629 1651035426853735044662743)
                      ·
                        rfl

theorem cell23_3215380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3215380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215380 prefixEnd_3215380 := by exact prefixLift 3215380
  have htrace : WordTrace (prefixWord ++ tailWord_3215380) baseStart_3215380 baseEnd_3215380 := by
    simpa [prefixWord, tailWord_3215380, baseEnd_3215380] using wordTrace_append hprefix tailTrace_3215380
  have hstable : (prefixWord ++ tailWord_3215380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215380).length < 2 ^ (prefixWord ++ tailWord_3215380).sum := by decide
  have hdescent : baseEnd_3215380 < baseStart_3215380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215383 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3215383 : Nat := 118140960795 + 3215383 * 2 ^ 59
def prefixEnd_3215383 : Nat := 4983230072969 + 3 ^ 40 * 3215383 * 2
def baseEnd_3215383 : Nat := 1651036967295698532925229

theorem tailTrace_3215383 : CollatzResearch.WordTrace tailWord_3215383 prefixEnd_3215383 1651036967295698532925229 := by
  unfold tailWord_3215383
  simp only [CollatzResearch.WordTrace]
  refine ⟨117274652510224009541946803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78183101673482673027964535 117274652510224009541946803)
  ·
    refine ⟨175911978765336014312920205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117274652510224009541946803 175911978765336014312920205)
    ·
      refine ⟨65966992037001005367345077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175911978765336014312920205 65966992037001005367345077)
      ·
        refine ⟨6184405503468844253188601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65966992037001005367345077 6184405503468844253188601)
        ·
          refine ⟨4638304127601633189891451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184405503468844253188601 4638304127601633189891451)
          ·
            refine ⟨6957456191402449784837177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638304127601633189891451 6957456191402449784837177)
            ·
              refine ⟨5218092143551837338627883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6957456191402449784837177 5218092143551837338627883)
              ·
                refine ⟨7827138215327756007941825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218092143551837338627883 7827138215327756007941825)
                ·
                  refine ⟨5870353661495817005956369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7827138215327756007941825 5870353661495817005956369)
                  ·
                    refine ⟨4402765246121862754467277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5870353661495817005956369 4402765246121862754467277)
                    ·
                      refine ⟨1651036967295698532925229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4402765246121862754467277 1651036967295698532925229)
                      ·
                        rfl

theorem cell23_3215383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3215383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215383 prefixEnd_3215383 := by exact prefixLift 3215383
  have htrace : WordTrace (prefixWord ++ tailWord_3215383) baseStart_3215383 baseEnd_3215383 := by
    simpa [prefixWord, tailWord_3215383, baseEnd_3215383] using wordTrace_append hprefix tailTrace_3215383
  have hstable : (prefixWord ++ tailWord_3215383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215383).length < 2 ^ (prefixWord ++ tailWord_3215383).sum := by decide
  have hdescent : baseEnd_3215383 < baseStart_3215383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215429 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_3215429 : Nat := 118140960795 + 3215429 * 2 ^ 59
def prefixEnd_3215429 : Nat := 4983230072969 + 3 ^ 40 * 3215429 * 2
def baseEnd_3215429 : Nat := 550353529135268450983339

theorem tailTrace_3215429 : CollatzResearch.WordTrace tailWord_3215429 prefixEnd_3215429 550353529135268450983339 := by
  unfold tailWord_3215429
  simp only [CollatzResearch.WordTrace]
  refine ⟨117276330268057359398121341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78184220178704906265414227 117276330268057359398121341)
  ·
    refine ⟨43978623850521509774295503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117276330268057359398121341 43978623850521509774295503)
    ·
      refine ⟨65967935775782264661443255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43978623850521509774295503 65967935775782264661443255)
      ·
        refine ⟨98951903663673396992164883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65967935775782264661443255 98951903663673396992164883)
        ·
          refine ⟨148427855495510095488247325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98951903663673396992164883 148427855495510095488247325)
          ·
            refine ⟨55660445810816285808092747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148427855495510095488247325 55660445810816285808092747)
            ·
              refine ⟨83490668716224428712139121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55660445810816285808092747 83490668716224428712139121)
              ·
                refine ⟨62618001537168321534104341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83490668716224428712139121 62618001537168321534104341)
                ·
                  refine ⟨2935218822054765071911141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62618001537168321534104341 2935218822054765071911141)
                  ·
                    refine ⟨550353529135268450983339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935218822054765071911141 550353529135268450983339)
                    ·
                      rfl

theorem cell23_3215429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_3215429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215429 prefixEnd_3215429 := by exact prefixLift 3215429
  have htrace : WordTrace (prefixWord ++ tailWord_3215429) baseStart_3215429 baseEnd_3215429 := by
    simpa [prefixWord, tailWord_3215429, baseEnd_3215429] using wordTrace_append hprefix tailTrace_3215429
  have hstable : (prefixWord ++ tailWord_3215429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215429).length < 2 ^ (prefixWord ++ tailWord_3215429).sum := by decide
  have hdescent : baseEnd_3215429 < baseStart_3215429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215430 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3215430 : Nat := 118140960795 + 3215430 * 2 ^ 59
def prefixEnd_3215430 : Nat := 4983230072969 + 3 ^ 40 * 3215430 * 2
def baseEnd_3215430 : Nat := 1651061100886459849037513

theorem tailTrace_3215430 : CollatzResearch.WordTrace tailWord_3215430 prefixEnd_3215430 1651061100886459849037513 := by
  unfold tailWord_3215430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664886460657929267778367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78184244494035824379271829 3664886460657929267778367)
  ·
    refine ⟨5497329690986893901667551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3664886460657929267778367 5497329690986893901667551)
    ·
      refine ⟨8245994536480340852501327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497329690986893901667551 8245994536480340852501327)
      ·
        refine ⟨12368991804720511278751991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8245994536480340852501327 12368991804720511278751991)
        ·
          refine ⟨18553487707080766918127987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12368991804720511278751991 18553487707080766918127987)
          ·
            refine ⟨27830231560621150377191981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18553487707080766918127987 27830231560621150377191981)
            ·
              refine ⟨10436336835232931391446993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27830231560621150377191981 10436336835232931391446993)
              ·
                refine ⟨7827252626424698543585245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10436336835232931391446993 7827252626424698543585245)
                ·
                  refine ⟨2935219734909261953844467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7827252626424698543585245 2935219734909261953844467)
                  ·
                    refine ⟨4402829602363892930766701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2935219734909261953844467 4402829602363892930766701)
                    ·
                      refine ⟨1651061100886459849037513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4402829602363892930766701 1651061100886459849037513)
                      ·
                        rfl

theorem cell23_3215430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3215430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215430 prefixEnd_3215430 := by exact prefixLift 3215430
  have htrace : WordTrace (prefixWord ++ tailWord_3215430) baseStart_3215430 baseEnd_3215430 := by
    simpa [prefixWord, tailWord_3215430, baseEnd_3215430] using wordTrace_append hprefix tailTrace_3215430
  have hstable : (prefixWord ++ tailWord_3215430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215430).length < 2 ^ (prefixWord ++ tailWord_3215430).sum := by decide
  have hdescent : baseEnd_3215430 < baseStart_3215430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215449 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3215449 : Nat := 118140960795 + 3215449 * 2 ^ 59
def prefixEnd_3215449 : Nat := 4983230072969 + 3 ^ 40 * 3215449 * 2
def baseEnd_3215449 : Nat := 1651070857018895274699925

theorem tailTrace_3215449 : CollatzResearch.WordTrace tailWord_3215449 prefixEnd_3215449 1651070857018895274699925 := by
  unfold tailWord_3215449
  simp only [CollatzResearch.WordTrace]
  refine ⟨117277059727984902813849401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78184706485323268542566267 117277059727984902813849401)
  ·
    refine ⟨87957794795988677110387051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117277059727984902813849401 87957794795988677110387051)
    ·
      refine ⟨131936692193983015665580577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87957794795988677110387051 131936692193983015665580577)
      ·
        refine ⟨98952519145487261749185433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131936692193983015665580577 98952519145487261749185433)
        ·
          refine ⟨74214389359115446311889075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98952519145487261749185433 74214389359115446311889075)
          ·
            refine ⟨111321584038673169467833613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74214389359115446311889075 111321584038673169467833613)
            ·
              refine ⟨41745594014502438550437605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111321584038673169467833613 41745594014502438550437605)
              ·
                refine ⟨7827298877719207228207051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41745594014502438550437605 7827298877719207228207051)
                ·
                  refine ⟨11740948316578810842310577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7827298877719207228207051 11740948316578810842310577)
                  ·
                    refine ⟨8805711237434108131732933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11740948316578810842310577 8805711237434108131732933)
                    ·
                      refine ⟨1651070857018895274699925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8805711237434108131732933 1651070857018895274699925)
                      ·
                        rfl

theorem cell23_3215449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3215449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215449 prefixEnd_3215449 := by exact prefixLift 3215449
  have htrace : WordTrace (prefixWord ++ tailWord_3215449) baseStart_3215449 baseEnd_3215449 := by
    simpa [prefixWord, tailWord_3215449, baseEnd_3215449] using wordTrace_append hprefix tailTrace_3215449
  have hstable : (prefixWord ++ tailWord_3215449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215449).length < 2 ^ (prefixWord ++ tailWord_3215449).sum := by decide
  have hdescent : baseEnd_3215449 < baseStart_3215449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215470 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_3215470 : Nat := 118140960795 + 3215470 * 2 ^ 59
def prefixEnd_3215470 : Nat := 4983230072969 + 3 ^ 40 * 3215470 * 2
def baseEnd_3215470 : Nat := 1651081640112639692537329

theorem tailTrace_3215470 : CollatzResearch.WordTrace tailWord_3215470 prefixEnd_3215470 1651081640112639692537329 := by
  unfold tailWord_3215470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14659728207613602925045483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78185217107272548933575909 14659728207613602925045483)
  ·
    refine ⟨21989592311420404387568225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14659728207613602925045483 21989592311420404387568225)
    ·
      refine ⟨16492194233565303290676169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21989592311420404387568225 16492194233565303290676169)
      ·
        refine ⟨12369145675173977468007127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16492194233565303290676169 12369145675173977468007127)
        ·
          refine ⟨18553718512760966202010691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12369145675173977468007127 18553718512760966202010691)
          ·
            refine ⟨27830577769141449303016037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18553718512760966202010691 27830577769141449303016037)
            ·
              refine ⟨5218233331714021744315507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27830577769141449303016037 5218233331714021744315507)
              ·
                refine ⟨7827349997571032616473261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218233331714021744315507 7827349997571032616473261)
                ·
                  refine ⟨2935256249089137231177473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7827349997571032616473261 2935256249089137231177473)
                  ·
                    refine ⟨2201442186816852923383105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935256249089137231177473 2201442186816852923383105)
                    ·
                      refine ⟨1651081640112639692537329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201442186816852923383105 1651081640112639692537329)
                      ·
                        rfl

theorem cell23_3215470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_3215470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215470 prefixEnd_3215470 := by exact prefixLift 3215470
  have htrace : WordTrace (prefixWord ++ tailWord_3215470) baseStart_3215470 baseEnd_3215470 := by
    simpa [prefixWord, tailWord_3215470, baseEnd_3215470] using wordTrace_append hprefix tailTrace_3215470
  have hstable : (prefixWord ++ tailWord_3215470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215470).length < 2 ^ (prefixWord ++ tailWord_3215470).sum := by decide
  have hdescent : baseEnd_3215470 < baseStart_3215470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215539 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4]
def baseStart_3215539 : Nat := 118140960795 + 3215539 * 2 ^ 59
def prefixEnd_3215539 : Nat := 4983230072969 + 3 ^ 40 * 3215539 * 2
def baseEnd_3215539 : Nat := 1651117070277799922574511

theorem tailTrace_3215539 : CollatzResearch.WordTrace tailWord_3215539 prefixEnd_3215539 1651117070277799922574511 := by
  unfold tailWord_3215539
  simp only [CollatzResearch.WordTrace]
  refine ⟨117280342297658848184625671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78186894865105898789750447 117280342297658848184625671)
  ·
    refine ⟨175920513446488272276938507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117280342297658848184625671 175920513446488272276938507)
    ·
      refine ⟨263880770169732408415407761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175920513446488272276938507 263880770169732408415407761)
      ·
        refine ⟨197910577627299306311555821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263880770169732408415407761 197910577627299306311555821)
        ·
          refine ⟨74216466610237239866833433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197910577627299306311555821 74216466610237239866833433)
          ·
            refine ⟨55662349957677929900125075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74216466610237239866833433 55662349957677929900125075)
            ·
              refine ⟨83493524936516894850187613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55662349957677929900125075 83493524936516894850187613)
              ·
                refine ⟨31310071851193835568820355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83493524936516894850187613 31310071851193835568820355)
                ·
                  refine ⟨46965107776790753353230533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31310071851193835568820355 46965107776790753353230533)
                  ·
                    refine ⟨8805957708148266253730725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46965107776790753353230533 8805957708148266253730725)
                    ·
                      refine ⟨1651117070277799922574511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8805957708148266253730725 1651117070277799922574511)
                      ·
                        rfl

theorem cell23_3215539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_3215539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215539 prefixEnd_3215539 := by exact prefixLift 3215539
  have htrace : WordTrace (prefixWord ++ tailWord_3215539) baseStart_3215539 baseEnd_3215539 := by
    simpa [prefixWord, tailWord_3215539, baseEnd_3215539] using wordTrace_append hprefix tailTrace_3215539
  have hstable : (prefixWord ++ tailWord_3215539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215539).length < 2 ^ (prefixWord ++ tailWord_3215539).sum := by decide
  have hdescent : baseEnd_3215539 < baseStart_3215539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215549 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 9]
def baseStart_3215549 : Nat := 118140960795 + 3215549 * 2 ^ 59
def prefixEnd_3215549 : Nat := 4983230072969 + 3 ^ 40 * 3215549 * 2
def baseEnd_3215549 : Nat := 183458022787149431494385

theorem tailTrace_3215549 : CollatzResearch.WordTrace tailWord_3215549 prefixEnd_3215549 183458022787149431494385 := by
  unfold tailWord_3215549
  simp only [CollatzResearch.WordTrace]
  refine ⟨117280707027622619892489701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78187138018415079928326467 117280707027622619892489701)
  ·
    refine ⟨21990132567679241229841819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117280707027622619892489701 21990132567679241229841819)
    ·
      refine ⟨32985198851518861844762729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21990132567679241229841819 32985198851518861844762729)
      ·
        refine ⟨24738899138639146383572047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32985198851518861844762729 24738899138639146383572047)
        ·
          refine ⟨37108348707958719575358071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24738899138639146383572047 37108348707958719575358071)
          ·
            refine ⟨55662523061938079363037107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37108348707958719575358071 55662523061938079363037107)
            ·
              refine ⟨83493784592907119044555661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55662523061938079363037107 83493784592907119044555661)
              ·
                refine ⟨31310169222340169641708373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83493784592907119044555661 31310169222340169641708373)
                ·
                  refine ⟨183458022787149431494385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31310169222340169641708373 183458022787149431494385)
                  ·
                    rfl

theorem cell23_3215549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_3215549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215549 prefixEnd_3215549 := by exact prefixLift 3215549
  have htrace : WordTrace (prefixWord ++ tailWord_3215549) baseStart_3215549 baseEnd_3215549 := by
    simpa [prefixWord, tailWord_3215549, baseEnd_3215549] using wordTrace_append hprefix tailTrace_3215549
  have hstable : (prefixWord ++ tailWord_3215549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215549).length < 2 ^ (prefixWord ++ tailWord_3215549).sum := by decide
  have hdescent : baseEnd_3215549 < baseStart_3215549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215564 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3215564 : Nat := 118140960795 + 3215564 * 2 ^ 59
def prefixEnd_3215564 : Nat := 4983230072969 + 3 ^ 40 * 3215564 * 2
def baseEnd_3215564 : Nat := 1651129907294162324761897

theorem tailTrace_3215564 : CollatzResearch.WordTrace tailWord_3215564 prefixEnd_3215564 1651129907294162324761897 := by
  unfold tailWord_3215564
  simp only [CollatzResearch.WordTrace]
  refine ⟨58640627061284138727142873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78187502748378851636190497 58640627061284138727142873)
  ·
    refine ⟨43980470295963104045357155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58640627061284138727142873 43980470295963104045357155)
    ·
      refine ⟨65970705443944656068035733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43980470295963104045357155 65970705443944656068035733)
      ·
        refine ⟨3092376817684905753189175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65970705443944656068035733 3092376817684905753189175)
        ·
          refine ⟨4638565226527358629783763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092376817684905753189175 4638565226527358629783763)
          ·
            refine ⟨6957847839791037944675645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638565226527358629783763 6957847839791037944675645)
            ·
              refine ⟨2609192939921639229253367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6957847839791037944675645 2609192939921639229253367)
              ·
                refine ⟨3913789409882458843880051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609192939921639229253367 3913789409882458843880051)
                ·
                  refine ⟨5870684114823688265820077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913789409882458843880051 5870684114823688265820077)
                  ·
                    refine ⟨2201506543058883099682529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5870684114823688265820077 2201506543058883099682529)
                    ·
                      refine ⟨1651129907294162324761897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201506543058883099682529 1651129907294162324761897)
                      ·
                        rfl

theorem cell23_3215564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3215564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215564 prefixEnd_3215564 := by exact prefixLift 3215564
  have htrace : WordTrace (prefixWord ++ tailWord_3215564) baseStart_3215564 baseEnd_3215564 := by
    simpa [prefixWord, tailWord_3215564, baseEnd_3215564] using wordTrace_append hprefix tailTrace_3215564
  have hstable : (prefixWord ++ tailWord_3215564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215564).length < 2 ^ (prefixWord ++ tailWord_3215564).sum := by decide
  have hdescent : baseEnd_3215564 < baseStart_3215564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215606 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3215606 : Nat := 118140960795 + 3215606 * 2 ^ 59
def prefixEnd_3215606 : Nat := 4983230072969 + 3 ^ 40 * 3215606 * 2
def baseEnd_3215606 : Nat := 1651151473481651160436703

theorem tailTrace_3215606 : CollatzResearch.WordTrace tailWord_3215606 prefixEnd_3215606 1651151473481651160436703 := by
  unfold tailWord_3215606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330174124276007414207167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78188523992277412418209781 7330174124276007414207167)
  ·
    refine ⟨10995261186414011121310751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7330174124276007414207167 10995261186414011121310751)
    ·
      refine ⟨16492891779621016681966127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10995261186414011121310751 16492891779621016681966127)
      ·
        refine ⟨24739337669431525022949191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16492891779621016681966127 24739337669431525022949191)
        ·
          refine ⟨37109006504147287534423787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24739337669431525022949191 37109006504147287534423787)
          ·
            refine ⟨55663509756220931301635681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37109006504147287534423787 55663509756220931301635681)
            ·
              refine ⟨41747632317165698476226761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55663509756220931301635681 41747632317165698476226761)
              ·
                refine ⟨31310724237874273857170071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41747632317165698476226761 31310724237874273857170071)
                ·
                  refine ⟨46966086356811410785755107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31310724237874273857170071 46966086356811410785755107)
                  ·
                    refine ⟨70449129535217116178632661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46966086356811410785755107 70449129535217116178632661)
                    ·
                      refine ⟨1651151473481651160436703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70449129535217116178632661 1651151473481651160436703)
                      ·
                        rfl

theorem cell23_3215606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3215606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215606 prefixEnd_3215606 := by exact prefixLift 3215606
  have htrace : WordTrace (prefixWord ++ tailWord_3215606) baseStart_3215606 baseEnd_3215606 := by
    simpa [prefixWord, tailWord_3215606, baseEnd_3215606] using wordTrace_append hprefix tailTrace_3215606
  have hstable : (prefixWord ++ tailWord_3215606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215606).length < 2 ^ (prefixWord ++ tailWord_3215606).sum := by decide
  have hdescent : baseEnd_3215606 < baseStart_3215606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215609 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_3215609 : Nat := 118140960795 + 3215609 * 2 ^ 59
def prefixEnd_3215609 : Nat := 4983230072969 + 3 ^ 40 * 3215609 * 2
def baseEnd_3215609 : Nat := 550384337974538216233063

theorem tailTrace_3215609 : CollatzResearch.WordTrace tailWord_3215609 prefixEnd_3215609 550384337974538216233063 := by
  unfold tailWord_3215609
  simp only [CollatzResearch.WordTrace]
  refine ⟨117282895407405250139673881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78188596938270166759782587 117282895407405250139673881)
  ·
    refine ⟨87962171555553937604755411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117282895407405250139673881 87962171555553937604755411)
    ·
      refine ⟨131943257333330906407133117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87962171555553937604755411 131943257333330906407133117)
      ·
        refine ⟨49478721499999089902674919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131943257333330906407133117 49478721499999089902674919)
        ·
          refine ⟨74218082249998634854012379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49478721499999089902674919 74218082249998634854012379)
          ·
            refine ⟨111327123374997952281018569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74218082249998634854012379 111327123374997952281018569)
            ·
              refine ⟨83495342531248464210763927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111327123374997952281018569 83495342531248464210763927)
              ·
                refine ⟨125243013796872696316145891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83495342531248464210763927 125243013796872696316145891)
                ·
                  refine ⟨187864520695309044474218837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125243013796872696316145891 187864520695309044474218837)
                  ·
                    refine ⟨550384337974538216233063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 187864520695309044474218837 550384337974538216233063)
                    ·
                      rfl

theorem cell23_3215609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_3215609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215609 prefixEnd_3215609 := by exact prefixLift 3215609
  have htrace : WordTrace (prefixWord ++ tailWord_3215609) baseStart_3215609 baseEnd_3215609 := by
    simpa [prefixWord, tailWord_3215609, baseEnd_3215609] using wordTrace_append hprefix tailTrace_3215609
  have hstable : (prefixWord ++ tailWord_3215609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215609).length < 2 ^ (prefixWord ++ tailWord_3215609).sum := by decide
  have hdescent : baseEnd_3215609 < baseStart_3215609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215633 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 2, 4, 2]
def baseStart_3215633 : Nat := 118140960795 + 3215633 * 2 ^ 59
def prefixEnd_3215633 : Nat := 4983230072969 + 3 ^ 40 * 3215633 * 2
def baseEnd_3215633 : Nat := 1651165337459322554799079

theorem tailTrace_3215633 : CollatzResearch.WordTrace tailWord_3215633 prefixEnd_3215633 1651165337459322554799079 := by
  unfold tailWord_3215633
  simp only [CollatzResearch.WordTrace]
  refine ⟨117283770759318302238547553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78189180506212201492365035 117283770759318302238547553)
  ·
    refine ⟨87962828069488726678910665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117283770759318302238547553 87962828069488726678910665)
    ·
      refine ⟨65972121052116545009182999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87962828069488726678910665 65972121052116545009182999)
      ·
        refine ⟨98958181578174817513774499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65972121052116545009182999 98958181578174817513774499)
        ·
          refine ⟨148437272367262226270661749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98958181578174817513774499 148437272367262226270661749)
          ·
            refine ⟨13915994284430833712874539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148437272367262226270661749 13915994284430833712874539)
            ·
              refine ⟨20873991426646250569311809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13915994284430833712874539 20873991426646250569311809)
              ·
                refine ⟨15655493569984687926983857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20873991426646250569311809 15655493569984687926983857)
                ·
                  refine ⟨11741620177488515945237893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15655493569984687926983857 11741620177488515945237893)
                  ·
                    refine ⟨2201553783279096739732105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11741620177488515945237893 2201553783279096739732105)
                    ·
                      refine ⟨1651165337459322554799079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201553783279096739732105 1651165337459322554799079)
                      ·
                        rfl

theorem cell23_3215633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_3215633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215633 prefixEnd_3215633 := by exact prefixLift 3215633
  have htrace : WordTrace (prefixWord ++ tailWord_3215633) baseStart_3215633 baseEnd_3215633 := by
    simpa [prefixWord, tailWord_3215633, baseEnd_3215633] using wordTrace_append hprefix tailTrace_3215633
  have hstable : (prefixWord ++ tailWord_3215633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215633).length < 2 ^ (prefixWord ++ tailWord_3215633).sum := by decide
  have hdescent : baseEnd_3215633 < baseStart_3215633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215650 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_3215650 : Nat := 118140960795 + 3215650 * 2 ^ 59
def prefixEnd_3215650 : Nat := 4983230072969 + 3 ^ 40 * 3215650 * 2
def baseEnd_3215650 : Nat := 1651174066630448988286501

theorem tailTrace_3215650 : CollatzResearch.WordTrace tailWord_3215650 prefixEnd_3215650 1651174066630448988286501 := by
  unfold tailWord_3215650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29321097700064178535479101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78189593866837809427944269 29321097700064178535479101)
  ·
    refine ⟨10995411637524066950804663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29321097700064178535479101 10995411637524066950804663)
    ·
      refine ⟨16493117456286100426206995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10995411637524066950804663 16493117456286100426206995)
      ·
        refine ⟨24739676184429150639310493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16493117456286100426206995 24739676184429150639310493)
        ·
          refine ⟨9277378569160931489741435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24739676184429150639310493 9277378569160931489741435)
          ·
            refine ⟨13916067853741397234612153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277378569160931489741435 13916067853741397234612153)
            ·
              refine ⟨10437050890306047925959115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13916067853741397234612153 10437050890306047925959115)
              ·
                refine ⟨15655576335459071888938673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10437050890306047925959115 15655576335459071888938673)
                ·
                  refine ⟨11741682251594303916704005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15655576335459071888938673 11741682251594303916704005)
                  ·
                    refine ⟨2201565422173931984382001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11741682251594303916704005 2201565422173931984382001)
                    ·
                      refine ⟨1651174066630448988286501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201565422173931984382001 1651174066630448988286501)
                      ·
                        rfl

theorem cell23_3215650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_3215650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215650 prefixEnd_3215650 := by exact prefixLift 3215650
  have htrace : WordTrace (prefixWord ++ tailWord_3215650) baseStart_3215650 baseEnd_3215650 := by
    simpa [prefixWord, tailWord_3215650, baseEnd_3215650] using wordTrace_append hprefix tailTrace_3215650
  have hstable : (prefixWord ++ tailWord_3215650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215650).length < 2 ^ (prefixWord ++ tailWord_3215650).sum := by decide
  have hdescent : baseEnd_3215650 < baseStart_3215650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215683 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 3]
def baseStart_3215683 : Nat := 118140960795 + 3215683 * 2 ^ 59
def prefixEnd_3215683 : Nat := 4983230072969 + 3 ^ 40 * 3215683 * 2
def baseEnd_3215683 : Nat := 1651191011492047359173849

theorem tailTrace_3215683 : CollatzResearch.WordTrace tailWord_3215683 prefixEnd_3215683 1651191011492047359173849 := by
  unfold tailWord_3215683
  simp only [CollatzResearch.WordTrace]
  refine ⟨117285594409137160777867703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78190396272758107185245135 117285594409137160777867703)
  ·
    refine ⟨175928391613705741166801555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117285594409137160777867703 175928391613705741166801555)
    ·
      refine ⟨263892587420558611750202333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175928391613705741166801555 263892587420558611750202333)
      ·
        refine ⟨98959720282709479406325875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263892587420558611750202333 98959720282709479406325875)
        ·
          refine ⟨148439580424064219109488813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98959720282709479406325875 148439580424064219109488813)
          ·
            refine ⟨55664842659024082166058305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148439580424064219109488813 55664842659024082166058305)
            ·
              refine ⟨41748631994268061624543729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55664842659024082166058305 41748631994268061624543729)
              ·
                refine ⟨31311473995701046218407797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41748631994268061624543729 31311473995701046218407797)
                ·
                  refine ⟨2935450687096973082975731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31311473995701046218407797 2935450687096973082975731)
                  ·
                    refine ⟨4403176030645459624463597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2935450687096973082975731 4403176030645459624463597)
                    ·
                      refine ⟨1651191011492047359173849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4403176030645459624463597 1651191011492047359173849)
                      ·
                        rfl

theorem cell23_3215683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_3215683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215683 prefixEnd_3215683 := by exact prefixLift 3215683
  have htrace : WordTrace (prefixWord ++ tailWord_3215683) baseStart_3215683 baseEnd_3215683 := by
    simpa [prefixWord, tailWord_3215683, baseEnd_3215683] using wordTrace_append hprefix tailTrace_3215683
  have hstable : (prefixWord ++ tailWord_3215683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215683).length < 2 ^ (prefixWord ++ tailWord_3215683).sum := by decide
  have hdescent : baseEnd_3215683 < baseStart_3215683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215706 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3215706 : Nat := 118140960795 + 3215706 * 2 ^ 59
def prefixEnd_3215706 : Nat := 4983230072969 + 3 ^ 40 * 3215706 * 2
def baseEnd_3215706 : Nat := 1651202821547100769186243

theorem tailTrace_3215706 : CollatzResearch.WordTrace tailWord_3215706 prefixEnd_3215706 1651202821547100769186243 := by
  unfold tailWord_3215706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29321608322013458926488743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78190955525369223803969981 29321608322013458926488743)
  ·
    refine ⟨43982412483020188389733115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29321608322013458926488743 43982412483020188389733115)
    ·
      refine ⟨65973618724530282584599673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43982412483020188389733115 65973618724530282584599673)
      ·
        refine ⟨49480214043397711938449755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65973618724530282584599673 49480214043397711938449755)
        ·
          refine ⟨74220321065096567907674633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49480214043397711938449755 74220321065096567907674633)
          ·
            refine ⟨55665240798822425930755975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74220321065096567907674633 55665240798822425930755975)
            ·
              refine ⟨83497861198233638896133963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55665240798822425930755975 83497861198233638896133963)
              ·
                refine ⟨125246791797350458344200945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83497861198233638896133963 125246791797350458344200945)
                ·
                  refine ⟨93935093848012843758150709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125246791797350458344200945 93935093848012843758150709)
                  ·
                    refine ⟨8806415048251204102326629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93935093848012843758150709 8806415048251204102326629)
                    ·
                      refine ⟨1651202821547100769186243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8806415048251204102326629 1651202821547100769186243)
                      ·
                        rfl

theorem cell23_3215706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3215706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215706 prefixEnd_3215706 := by exact prefixLift 3215706
  have htrace : WordTrace (prefixWord ++ tailWord_3215706) baseStart_3215706 baseEnd_3215706 := by
    simpa [prefixWord, tailWord_3215706, baseEnd_3215706] using wordTrace_append hprefix tailTrace_3215706
  have hstable : (prefixWord ++ tailWord_3215706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215706).length < 2 ^ (prefixWord ++ tailWord_3215706).sum := by decide
  have hdescent : baseEnd_3215706 < baseStart_3215706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215720 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 1, 5]
def baseStart_3215720 : Nat := 118140960795 + 3215720 * 2 ^ 59
def prefixEnd_3215720 : Nat := 4983230072969 + 3 ^ 40 * 3215720 * 2
def baseEnd_3215720 : Nat := 550403336758754571470393

theorem tailTrace_3215720 : CollatzResearch.WordTrace tailWord_3215720 prefixEnd_3215720 550403336758754571470393 := by
  unfold tailWord_3215720
  simp only [CollatzResearch.WordTrace]
  refine ⟨58643471955001558048482307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78191295940002077397976409 58643471955001558048482307)
  ·
    refine ⟨87965207932502337072723461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58643471955001558048482307 87965207932502337072723461)
    ·
      refine ⟨16493476487344188201135649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87965207932502337072723461 16493476487344188201135649)
      ·
        refine ⟨12370107365508141150851737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16493476487344188201135649 12370107365508141150851737)
        ·
          refine ⟨9277580524131105863138803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370107365508141150851737 9277580524131105863138803)
          ·
            refine ⟨13916370786196658794708205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277580524131105863138803 13916370786196658794708205)
            ·
              refine ⟨5218639044823747048015577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13916370786196658794708205 5218639044823747048015577)
              ·
                refine ⟨3913979283617810286011683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5218639044823747048015577 3913979283617810286011683)
                ·
                  refine ⟨5870968925426715429017525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913979283617810286011683 5870968925426715429017525)
                  ·
                    refine ⟨550403336758754571470393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5870968925426715429017525 550403336758754571470393)
                    ·
                      rfl

theorem cell23_3215720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_3215720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215720 prefixEnd_3215720 := by exact prefixLift 3215720
  have htrace : WordTrace (prefixWord ++ tailWord_3215720) baseStart_3215720 baseEnd_3215720 := by
    simpa [prefixWord, tailWord_3215720, baseEnd_3215720] using wordTrace_append hprefix tailTrace_3215720
  have hstable : (prefixWord ++ tailWord_3215720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215720).length < 2 ^ (prefixWord ++ tailWord_3215720).sum := by decide
  have hdescent : baseEnd_3215720 < baseStart_3215720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215733 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3215733 : Nat := 118140960795 + 3215733 * 2 ^ 59
def prefixEnd_3215733 : Nat := 4983230072969 + 3 ^ 40 * 3215733 * 2
def baseEnd_3215733 : Nat := 550405561841590721182873

theorem tailTrace_3215733 : CollatzResearch.WordTrace tailWord_3215733 prefixEnd_3215733 550405561841590721182873 := by
  unfold tailWord_3215733
  simp only [CollatzResearch.WordTrace]
  refine ⟨117287418058956019317187853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78191612039304012878125235 117287418058956019317187853)
  ·
    refine ⟨43982781772108507243945445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117287418058956019317187853 43982781772108507243945445)
    ·
      refine ⟨8246771582270345108239771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43982781772108507243945445 8246771582270345108239771)
      ·
        refine ⟨12370157373405517662359657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246771582270345108239771 12370157373405517662359657)
        ·
          refine ⟨9277618030054138246769743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370157373405517662359657 9277618030054138246769743)
          ·
            refine ⟨13916427045081207370154615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277618030054138246769743 13916427045081207370154615)
            ·
              refine ⟨20874640567621811055231923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916427045081207370154615 20874640567621811055231923)
              ·
                refine ⟨31311960851432716582847885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20874640567621811055231923 31311960851432716582847885)
                ·
                  refine ⟨11741985319287268718567957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31311960851432716582847885 11741985319287268718567957)
                  ·
                    refine ⟨550405561841590721182873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11741985319287268718567957 550405561841590721182873)
                    ·
                      rfl

theorem cell23_3215733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3215733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215733 prefixEnd_3215733 := by exact prefixLift 3215733
  have htrace : WordTrace (prefixWord ++ tailWord_3215733) baseStart_3215733 baseEnd_3215733 := by
    simpa [prefixWord, tailWord_3215733, baseEnd_3215733] using wordTrace_append hprefix tailTrace_3215733
  have hstable : (prefixWord ++ tailWord_3215733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215733).length < 2 ^ (prefixWord ++ tailWord_3215733).sum := by decide
  have hdescent : baseEnd_3215733 < baseStart_3215733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215740 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_3215740 : Nat := 118140960795 + 3215740 * 2 ^ 59
def prefixEnd_3215740 : Nat := 4983230072969 + 3 ^ 40 * 3215740 * 2
def baseEnd_3215740 : Nat := 1651220279889353636161087

theorem tailTrace_3215740 : CollatzResearch.WordTrace tailWord_3215740 prefixEnd_3215740 1651220279889353636161087 := by
  unfold tailWord_3215740
  simp only [CollatzResearch.WordTrace]
  refine ⟨58643836684965329756346337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78191782246620439675128449 58643836684965329756346337)
  ·
    refine ⟨43982877513723997317259753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58643836684965329756346337 43982877513723997317259753)
    ·
      refine ⟨32987158135292997987944815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43982877513723997317259753 32987158135292997987944815)
      ·
        refine ⟨49480737202939496981917223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32987158135292997987944815 49480737202939496981917223)
        ·
          refine ⟨74221105804409245472875835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49480737202939496981917223 74221105804409245472875835)
          ·
            refine ⟨111331658706613868209313753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74221105804409245472875835 111331658706613868209313753)
            ·
              refine ⟨83498744029960401156985315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111331658706613868209313753 83498744029960401156985315)
              ·
                refine ⟨125248116044940601735477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83498744029960401156985315 125248116044940601735477973)
                ·
                  refine ⟨2935502719803295353175265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125248116044940601735477973 2935502719803295353175265)
                  ·
                    refine ⟨2201627039852471514881449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935502719803295353175265 2201627039852471514881449)
                    ·
                      refine ⟨1651220279889353636161087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201627039852471514881449 1651220279889353636161087)
                      ·
                        rfl

theorem cell23_3215740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_3215740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215740 prefixEnd_3215740 := by exact prefixLift 3215740
  have htrace : WordTrace (prefixWord ++ tailWord_3215740) baseStart_3215740 baseEnd_3215740 := by
    simpa [prefixWord, tailWord_3215740, baseEnd_3215740] using wordTrace_append hprefix tailTrace_3215740
  have hstable : (prefixWord ++ tailWord_3215740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215740).length < 2 ^ (prefixWord ++ tailWord_3215740).sum := by decide
  have hdescent : baseEnd_3215740 < baseStart_3215740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215770 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3215770 : Nat := 118140960795 + 3215770 * 2 ^ 59
def prefixEnd_3215770 : Nat := 4983230072969 + 3 ^ 40 * 3215770 * 2
def baseEnd_3215770 : Nat := 1651235684308988518785949

theorem tailTrace_3215770 : CollatzResearch.WordTrace tailWord_3215770 prefixEnd_3215770 1651235684308988518785949 := by
  unfold tailWord_3215770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29322191889955493659071191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78192511706547983090856509 29322191889955493659071191)
  ·
    refine ⟨43983287834933240488606787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29322191889955493659071191 43983287834933240488606787)
    ·
      refine ⟨65974931752399860732910181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43983287834933240488606787 65974931752399860732910181)
      ·
        refine ⟨12370299703574973887420659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65974931752399860732910181 12370299703574973887420659)
        ·
          refine ⟨18555449555362460831130989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370299703574973887420659 18555449555362460831130989)
          ·
            refine ⟨6958293583260922811674121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18555449555362460831130989 6958293583260922811674121)
            ·
              refine ⟨5218720187445692108755591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6958293583260922811674121 5218720187445692108755591)
              ·
                refine ⟨7828080281168538163133387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218720187445692108755591 7828080281168538163133387)
                ·
                  refine ⟨11742120421752807244700081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7828080281168538163133387 11742120421752807244700081)
                  ·
                    refine ⟨8806590316314605433525061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11742120421752807244700081 8806590316314605433525061)
                    ·
                      refine ⟨1651235684308988518785949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8806590316314605433525061 1651235684308988518785949)
                      ·
                        rfl

theorem cell23_3215770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3215770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215770 prefixEnd_3215770 := by exact prefixLift 3215770
  have htrace : WordTrace (prefixWord ++ tailWord_3215770) baseStart_3215770 baseEnd_3215770 := by
    simpa [prefixWord, tailWord_3215770, baseEnd_3215770] using wordTrace_append hprefix tailTrace_3215770
  have hstable : (prefixWord ++ tailWord_3215770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215770).length < 2 ^ (prefixWord ++ tailWord_3215770).sum := by decide
  have hdescent : baseEnd_3215770 < baseStart_3215770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215774 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3215774 : Nat := 118140960795 + 3215774 * 2 ^ 59
def prefixEnd_3215774 : Nat := 4983230072969 + 3 ^ 40 * 3215774 * 2
def baseEnd_3215774 : Nat := 1651237738231606503135931

theorem tailTrace_3215774 : CollatzResearch.WordTrace tailWord_3215774 prefixEnd_3215774 1651237738231606503135931 := by
  unfold tailWord_3215774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661114181475935414928797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78192608967871655546286917 14661114181475935414928797)
  ·
    refine ⟨5497917818053475780598299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14661114181475935414928797 5497917818053475780598299)
    ·
      refine ⟨8246876727080213670897449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497917818053475780598299 8246876727080213670897449)
      ·
        refine ⟨6185157545310160253173087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8246876727080213670897449 6185157545310160253173087)
        ·
          refine ⟨9277736317965240379759631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185157545310160253173087 9277736317965240379759631)
          ·
            refine ⟨13916604476947860569639447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277736317965240379759631 13916604476947860569639447)
            ·
              refine ⟨20874906715421790854459171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916604476947860569639447 20874906715421790854459171)
              ·
                refine ⟨31312360073132686281688757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20874906715421790854459171 31312360073132686281688757)
                ·
                  refine ⟨2935533756856189338908321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31312360073132686281688757 2935533756856189338908321)
                  ·
                    refine ⟨2201650317642142004181241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935533756856189338908321 2201650317642142004181241)
                    ·
                      refine ⟨1651237738231606503135931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201650317642142004181241 1651237738231606503135931)
                      ·
                        rfl

theorem cell23_3215774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3215774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215774 prefixEnd_3215774 := by exact prefixLift 3215774
  have htrace : WordTrace (prefixWord ++ tailWord_3215774) baseStart_3215774 baseEnd_3215774 := by
    simpa [prefixWord, tailWord_3215774, baseEnd_3215774] using wordTrace_append hprefix tailTrace_3215774
  have hstable : (prefixWord ++ tailWord_3215774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215774).length < 2 ^ (prefixWord ++ tailWord_3215774).sum := by decide
  have hdescent : baseEnd_3215774 < baseStart_3215774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215833 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3215833 : Nat := 118140960795 + 3215833 * 2 ^ 59
def prefixEnd_3215833 : Nat := 4983230072969 + 3 ^ 40 * 3215833 * 2
def baseEnd_3215833 : Nat := 1651268033590221772298159

theorem tailTrace_3215833 : CollatzResearch.WordTrace tailWord_3215833 prefixEnd_3215833 1651268033590221772298159 := by
  unfold tailWord_3215833
  simp only [CollatzResearch.WordTrace]
  refine ⟨117291065358593736395828153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78194043572395824263885435 117291065358593736395828153)
  ·
    refine ⟨87968299018945302296871115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117291065358593736395828153 87968299018945302296871115)
    ·
      refine ⟨131952448528417953445306673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87968299018945302296871115 131952448528417953445306673)
      ·
        refine ⟨98964336396313465083980005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131952448528417953445306673 98964336396313465083980005)
        ·
          refine ⟨18555813074308774703246251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98964336396313465083980005 18555813074308774703246251)
          ·
            refine ⟨27833719611463162054869377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18555813074308774703246251 27833719611463162054869377)
            ·
              refine ⟨20875289708597371541152033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27833719611463162054869377 20875289708597371541152033)
              ·
                refine ⟨15656467281448028655864025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20875289708597371541152033 15656467281448028655864025)
                ·
                  refine ⟨11742350461086021491898019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15656467281448028655864025 11742350461086021491898019)
                  ·
                    refine ⟨17613525691629032237847029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11742350461086021491898019 17613525691629032237847029)
                    ·
                      refine ⟨1651268033590221772298159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17613525691629032237847029 1651268033590221772298159)
                      ·
                        rfl

theorem cell23_3215833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3215833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215833 prefixEnd_3215833 := by exact prefixLift 3215833
  have htrace : WordTrace (prefixWord ++ tailWord_3215833) baseStart_3215833 baseEnd_3215833 := by
    simpa [prefixWord, tailWord_3215833, baseEnd_3215833] using wordTrace_append hprefix tailTrace_3215833
  have hstable : (prefixWord ++ tailWord_3215833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215833).length < 2 ^ (prefixWord ++ tailWord_3215833).sum := by decide
  have hdescent : baseEnd_3215833 < baseStart_3215833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215842 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3215842 : Nat := 118140960795 + 3215842 * 2 ^ 59
def prefixEnd_3215842 : Nat := 4983230072969 + 3 ^ 40 * 3215842 * 2
def baseEnd_3215842 : Nat := 1651272654916112237085619

theorem tailTrace_3215842 : CollatzResearch.WordTrace tailWord_3215842 prefixEnd_3215842 1651272654916112237085619 := by
  unfold tailWord_3215842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29322848403890282733226445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78194262410374087288603853 29322848403890282733226445)
  ·
    refine ⟨10996068151458856024959917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29322848403890282733226445 10996068151458856024959917)
    ·
      refine ⟨4123525556797071009359969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10996068151458856024959917 4123525556797071009359969)
      ·
        refine ⟨3092644167597803257019977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4123525556797071009359969 3092644167597803257019977)
        ·
          refine ⟨2319483125698352442764983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3092644167597803257019977 2319483125698352442764983)
          ·
            refine ⟨3479224688547528664147475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319483125698352442764983 3479224688547528664147475)
            ·
              refine ⟨5218837032821292996221213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479224688547528664147475 5218837032821292996221213)
              ·
                refine ⟨1957063887307984873582955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5218837032821292996221213 1957063887307984873582955)
                ·
                  refine ⟨2935595830961977310374433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957063887307984873582955 2935595830961977310374433)
                  ·
                    refine ⟨2201696873221482982780825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935595830961977310374433 2201696873221482982780825)
                    ·
                      refine ⟨1651272654916112237085619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201696873221482982780825 1651272654916112237085619)
                      ·
                        rfl

theorem cell23_3215842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3215842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215842 prefixEnd_3215842 := by exact prefixLift 3215842
  have htrace : WordTrace (prefixWord ++ tailWord_3215842) baseStart_3215842 baseEnd_3215842 := by
    simpa [prefixWord, tailWord_3215842, baseEnd_3215842] using wordTrace_append hprefix tailTrace_3215842
  have hstable : (prefixWord ++ tailWord_3215842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215842).length < 2 ^ (prefixWord ++ tailWord_3215842).sum := by decide
  have hdescent : baseEnd_3215842 < baseStart_3215842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215847 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3215847 : Nat := 118140960795 + 3215847 * 2 ^ 59
def prefixEnd_3215847 : Nat := 4983230072969 + 3 ^ 40 * 3215847 * 2
def baseEnd_3215847 : Nat := 1651275222319384717523095

theorem tailTrace_3215847 : CollatzResearch.WordTrace tailWord_3215847 prefixEnd_3215847 1651275222319384717523095 := by
  unfold tailWord_3215847
  simp only [CollatzResearch.WordTrace]
  refine ⟨117291575980543016786837795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78194383987028677857891863 117291575980543016786837795)
  ·
    refine ⟨175937363970814525180256693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117291575980543016786837795 175937363970814525180256693)
    ·
      refine ⟨16494127872263861735649065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175937363970814525180256693 16494127872263861735649065)
      ·
        refine ⟨12370595904197896301736799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16494127872263861735649065 12370595904197896301736799)
        ·
          refine ⟨18555893856296844452605199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370595904197896301736799 18555893856296844452605199)
          ·
            refine ⟨27833840784445266678907799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18555893856296844452605199 27833840784445266678907799)
            ·
              refine ⟨41750761176667900018361699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27833840784445266678907799 41750761176667900018361699)
              ·
                refine ⟨62626141765001850027542549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41750761176667900018361699 62626141765001850027542549)
                ·
                  refine ⟨2935600395234461720041057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62626141765001850027542549 2935600395234461720041057)
                  ·
                    refine ⟨2201700296425846290030793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935600395234461720041057 2201700296425846290030793)
                    ·
                      refine ⟨1651275222319384717523095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201700296425846290030793 1651275222319384717523095)
                      ·
                        rfl

theorem cell23_3215847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3215847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215847 prefixEnd_3215847 := by exact prefixLift 3215847
  have htrace : WordTrace (prefixWord ++ tailWord_3215847) baseStart_3215847 baseEnd_3215847 := by
    simpa [prefixWord, tailWord_3215847, baseEnd_3215847] using wordTrace_append hprefix tailTrace_3215847
  have hstable : (prefixWord ++ tailWord_3215847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215847).length < 2 ^ (prefixWord ++ tailWord_3215847).sum := by decide
  have hdescent : baseEnd_3215847 < baseStart_3215847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215850 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3215850 : Nat := 118140960795 + 3215850 * 2 ^ 59
def prefixEnd_3215850 : Nat := 4983230072969 + 3 ^ 40 * 3215850 * 2
def baseEnd_3215850 : Nat := 1651276762761348205785581

theorem tailTrace_3215850 : CollatzResearch.WordTrace tailWord_3215850 prefixEnd_3215850 1651276762761348205785581 := by
  unfold tailWord_3215850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29322921349883037074799251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78194456933021432199464669 29322921349883037074799251)
  ·
    refine ⟨43984382024824555612198877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29322921349883037074799251 43984382024824555612198877)
    ·
      refine ⟨16494143259309208354574579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43984382024824555612198877 16494143259309208354574579)
      ·
        refine ⟨24741214888963812531861869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16494143259309208354574579 24741214888963812531861869)
        ·
          refine ⟨9277955583361429699448201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24741214888963812531861869 9277955583361429699448201)
          ·
            refine ⟨6958466687521072274586151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9277955583361429699448201 6958466687521072274586151)
            ·
              refine ⟨10437700031281608411879227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958466687521072274586151 10437700031281608411879227)
              ·
                refine ⟨15656550046922412617818841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10437700031281608411879227 15656550046922412617818841)
                ·
                  refine ⟨11742412535191809463364131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15656550046922412617818841 11742412535191809463364131)
                  ·
                    refine ⟨17613618802787714195046197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11742412535191809463364131 17613618802787714195046197)
                    ·
                      refine ⟨1651276762761348205785581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17613618802787714195046197 1651276762761348205785581)
                      ·
                        rfl

theorem cell23_3215850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3215850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215850 prefixEnd_3215850 := by exact prefixLift 3215850
  have htrace : WordTrace (prefixWord ++ tailWord_3215850) baseStart_3215850 baseEnd_3215850 := by
    simpa [prefixWord, tailWord_3215850, baseEnd_3215850] using wordTrace_append hprefix tailTrace_3215850
  have hstable : (prefixWord ++ tailWord_3215850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215850).length < 2 ^ (prefixWord ++ tailWord_3215850).sum := by decide
  have hdescent : baseEnd_3215850 < baseStart_3215850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215893 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3215893 : Nat := 118140960795 + 3215893 * 2 ^ 59
def prefixEnd_3215893 : Nat := 4983230072969 + 3 ^ 40 * 3215893 * 2
def baseEnd_3215893 : Nat := 1651298842429491537547883

theorem tailTrace_3215893 : CollatzResearch.WordTrace tailWord_3215893 prefixEnd_3215893 1651298842429491537547883 := by
  unfold tailWord_3215893
  simp only [CollatzResearch.WordTrace]
  refine ⟨117293253738376366643012333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78195502492250911095341555 117293253738376366643012333)
  ·
    refine ⟨43984970151891137491129625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117293253738376366643012333 43984970151891137491129625)
    ·
      refine ⟨32988727613918353118347219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43984970151891137491129625 32988727613918353118347219)
      ·
        refine ⟨49483091420877529677520829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32988727613918353118347219 49483091420877529677520829)
        ·
          refine ⟨18556159282829073629070311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49483091420877529677520829 18556159282829073629070311)
          ·
            refine ⟨27834238924243610443605467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556159282829073629070311 27834238924243610443605467)
            ·
              refine ⟨41751358386365415665408201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27834238924243610443605467 41751358386365415665408201)
              ·
                refine ⟨31313518789774061749056151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41751358386365415665408201 31313518789774061749056151)
                ·
                  refine ⟨46970278184661092623584227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31313518789774061749056151 46970278184661092623584227)
                  ·
                    refine ⟨70455417276991638935376341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46970278184661092623584227 70455417276991638935376341)
                    ·
                      refine ⟨1651298842429491537547883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70455417276991638935376341 1651298842429491537547883)
                      ·
                        rfl

theorem cell23_3215893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3215893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215893 prefixEnd_3215893 := by exact prefixLift 3215893
  have htrace : WordTrace (prefixWord ++ tailWord_3215893) baseStart_3215893 baseEnd_3215893 := by
    simpa [prefixWord, tailWord_3215893, baseEnd_3215893] using wordTrace_append hprefix tailTrace_3215893
  have hstable : (prefixWord ++ tailWord_3215893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215893).length < 2 ^ (prefixWord ++ tailWord_3215893).sum := by decide
  have hdescent : baseEnd_3215893 < baseStart_3215893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215900 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3215900 : Nat := 118140960795 + 3215900 * 2 ^ 59
def prefixEnd_3215900 : Nat := 4983230072969 + 3 ^ 40 * 3215900 * 2
def baseEnd_3215900 : Nat := 550434145598024336720117

theorem tailTrace_3215900 : CollatzResearch.WordTrace tailWord_3215900 prefixEnd_3215900 550434145598024336720117 := by
  unfold tailWord_3215900
  simp only [CollatzResearch.WordTrace]
  refine ⟨58646754524675503419258577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78195672699567337892344769 58646754524675503419258577)
  ·
    refine ⟨43985065893506627564443933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58646754524675503419258577 43985065893506627564443933)
    ·
      refine ⟨16494399710064985336666475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43985065893506627564443933 16494399710064985336666475)
      ·
        refine ⟨24741599565097478004999713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16494399710064985336666475 24741599565097478004999713)
        ·
          refine ⟨18556199673823108503749785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24741599565097478004999713 18556199673823108503749785)
          ·
            refine ⟨13917149755367331377812339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18556199673823108503749785 13917149755367331377812339)
            ·
              refine ⟨20875724633050997066718509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13917149755367331377812339 20875724633050997066718509)
              ·
                refine ⟨7828396737394123900019441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20875724633050997066718509 7828396737394123900019441)
                ·
                  refine ⟨5871297553045592925014581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828396737394123900019441 5871297553045592925014581)
                  ·
                    refine ⟨550434145598024336720117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5871297553045592925014581 550434145598024336720117)
                    ·
                      rfl

theorem cell23_3215900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3215900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215900 prefixEnd_3215900 := by exact prefixLift 3215900
  have htrace : WordTrace (prefixWord ++ tailWord_3215900) baseStart_3215900 baseEnd_3215900 := by
    simpa [prefixWord, tailWord_3215900, baseEnd_3215900] using wordTrace_append hprefix tailTrace_3215900
  have hstable : (prefixWord ++ tailWord_3215900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215900).length < 2 ^ (prefixWord ++ tailWord_3215900).sum := by decide
  have hdescent : baseEnd_3215900 < baseStart_3215900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215920 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_3215920 : Nat := 118140960795 + 3215920 * 2 ^ 59
def prefixEnd_3215920 : Nat := 4983230072969 + 3 ^ 40 * 3215920 * 2
def baseEnd_3215920 : Nat := 1651312706407162931910259

theorem tailTrace_3215920 : CollatzResearch.WordTrace tailWord_3215920 prefixEnd_3215920 1651312706407162931910259 := by
  unfold tailWord_3215920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58647119254639275127122607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78196159006185700169496809 58647119254639275127122607)
  ·
    refine ⟨87970678881958912690683911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58647119254639275127122607 87970678881958912690683911)
    ·
      refine ⟨131956018322938369036025867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87970678881958912690683911 131956018322938369036025867)
      ·
        refine ⟨197934027484407553554038801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131956018322938369036025867 197934027484407553554038801)
        ·
          refine ⟨148450520613305665165529101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197934027484407553554038801 148450520613305665165529101)
          ·
            refine ⟨55668945229989624437073413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148450520613305665165529101 55668945229989624437073413)
            ·
              refine ⟨10437927230623054581951265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55668945229989624437073413 10437927230623054581951265)
              ·
                refine ⟨7828445422967290936463449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10437927230623054581951265 7828445422967290936463449)
                ·
                  refine ⟨5871334067225468202347587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828445422967290936463449 5871334067225468202347587)
                  ·
                    refine ⟨8807001100838202303521381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5871334067225468202347587 8807001100838202303521381)
                    ·
                      refine ⟨1651312706407162931910259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8807001100838202303521381 1651312706407162931910259)
                      ·
                        rfl

theorem cell23_3215920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_3215920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215920 prefixEnd_3215920 := by exact prefixLift 3215920
  have htrace : WordTrace (prefixWord ++ tailWord_3215920) baseStart_3215920 baseEnd_3215920 := by
    simpa [prefixWord, tailWord_3215920, baseEnd_3215920] using wordTrace_append hprefix tailTrace_3215920
  have hstable : (prefixWord ++ tailWord_3215920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215920).length < 2 ^ (prefixWord ++ tailWord_3215920).sum := by decide
  have hdescent : baseEnd_3215920 < baseStart_3215920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215923 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_3215923 : Nat := 118140960795 + 3215923 * 2 ^ 59
def prefixEnd_3215923 : Nat := 4983230072969 + 3 ^ 40 * 3215923 * 2
def baseEnd_3215923 : Nat := 1651314246849126420172745

theorem tailTrace_3215923 : CollatzResearch.WordTrace tailWord_3215923 prefixEnd_3215923 1651314246849126420172745 := by
  unfold tailWord_3215923
  simp only [CollatzResearch.WordTrace]
  refine ⟨117294347928267681766604423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78196231952178454511069615 117294347928267681766604423)
  ·
    refine ⟨175941521892401522649906635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117294347928267681766604423 175941521892401522649906635)
    ·
      refine ⟨263912282838602283974859953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175941521892401522649906635 263912282838602283974859953)
      ·
        refine ⟨197934212128951712981144965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263912282838602283974859953 197934212128951712981144965)
        ·
          refine ⟨37112664774178446183964681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197934212128951712981144965 37112664774178446183964681)
          ·
            refine ⟨27834498580633834637973511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37112664774178446183964681 27834498580633834637973511)
            ·
              refine ⟨41751747870950751956960267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27834498580633834637973511 41751747870950751956960267)
              ·
                refine ⟨62627621806426127935440401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41751747870950751956960267 62627621806426127935440401)
                ·
                  refine ⟨46970716354819595951580301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62627621806426127935440401 46970716354819595951580301)
                  ·
                    refine ⟨17614018633057348481842613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46970716354819595951580301 17614018633057348481842613)
                    ·
                      refine ⟨1651314246849126420172745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17614018633057348481842613 1651314246849126420172745)
                      ·
                        rfl

theorem cell23_3215923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_3215923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215923 prefixEnd_3215923 := by exact prefixLift 3215923
  have htrace : WordTrace (prefixWord ++ tailWord_3215923) baseStart_3215923 baseEnd_3215923 := by
    simpa [prefixWord, tailWord_3215923, baseEnd_3215923] using wordTrace_append hprefix tailTrace_3215923
  have hstable : (prefixWord ++ tailWord_3215923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215923).length < 2 ^ (prefixWord ++ tailWord_3215923).sum := by decide
  have hdescent : baseEnd_3215923 < baseStart_3215923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215937 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3215937 : Nat := 118140960795 + 3215937 * 2 ^ 59
def prefixEnd_3215937 : Nat := 4983230072969 + 3 ^ 40 * 3215937 * 2
def baseEnd_3215937 : Nat := 1651321435578289365397681

theorem tailTrace_3215937 : CollatzResearch.WordTrace tailWord_3215937 prefixEnd_3215937 1651321435578289365397681 := by
  unfold tailWord_3215937
  simp only [CollatzResearch.WordTrace]
  refine ⟨117294858550216962157614065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78196572366811308105076043 117294858550216962157614065)
  ·
    refine ⟨87971143912662721618210549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117294858550216962157614065 87971143912662721618210549)
    ·
      refine ⟨8247294741812130151707239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87971143912662721618210549 8247294741812130151707239)
      ·
        refine ⟨12370942112718195227560859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247294741812130151707239 12370942112718195227560859)
        ·
          refine ⟨18556413169077292841341289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370942112718195227560859 18556413169077292841341289)
          ·
            refine ⟨13917309876807969631005967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18556413169077292841341289 13917309876807969631005967)
            ·
              refine ⟨20875964815211954446508951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13917309876807969631005967 20875964815211954446508951)
              ·
                refine ⟨31313947222817931669763427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20875964815211954446508951 31313947222817931669763427)
                ·
                  refine ⟨46970920834226897504645141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31313947222817931669763427 46970920834226897504645141)
                  ·
                    refine ⟨2201761914104385820530241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46970920834226897504645141 2201761914104385820530241)
                    ·
                      refine ⟨1651321435578289365397681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201761914104385820530241 1651321435578289365397681)
                      ·
                        rfl

theorem cell23_3215937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3215937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215937 prefixEnd_3215937 := by exact prefixLift 3215937
  have htrace : WordTrace (prefixWord ++ tailWord_3215937) baseStart_3215937 baseEnd_3215937 := by
    simpa [prefixWord, tailWord_3215937, baseEnd_3215937] using wordTrace_append hprefix tailTrace_3215937
  have hstable : (prefixWord ++ tailWord_3215937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215937).length < 2 ^ (prefixWord ++ tailWord_3215937).sum := by decide
  have hdescent : baseEnd_3215937 < baseStart_3215937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215957 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3215957 : Nat := 118140960795 + 3215957 * 2 ^ 59
def prefixEnd_3215957 : Nat := 4983230072969 + 3 ^ 40 * 3215957 * 2
def baseEnd_3215957 : Nat := 1651331705191379287147589

theorem tailTrace_3215957 : CollatzResearch.WordTrace tailWord_3215957 prefixEnd_3215957 1651331705191379287147589 := by
  unfold tailWord_3215957
  simp only [CollatzResearch.WordTrace]
  refine ⟨117295588010144505573342125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78197058673429670382228083 117295588010144505573342125)
  ·
    refine ⟨43985845503804189590003297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117295588010144505573342125 43985845503804189590003297)
    ·
      refine ⟨32989384127853142192502473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43985845503804189590003297 32989384127853142192502473)
      ·
        refine ⟨24742038095889856644376855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32989384127853142192502473 24742038095889856644376855)
        ·
          refine ⟨37113057143834784966565283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24742038095889856644376855 37113057143834784966565283)
          ·
            refine ⟨55669585715752177449847925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37113057143834784966565283 55669585715752177449847925)
            ·
              refine ⟨5219023660851766635923243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55669585715752177449847925 5219023660851766635923243)
              ·
                refine ⟨7828535491277649953884865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219023660851766635923243 7828535491277649953884865)
                ·
                  refine ⟨5871401618458237465413649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828535491277649953884865 5871401618458237465413649)
                  ·
                    refine ⟨4403551213843678099060237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871401618458237465413649 4403551213843678099060237)
                    ·
                      refine ⟨1651331705191379287147589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4403551213843678099060237 1651331705191379287147589)
                      ·
                        rfl

theorem cell23_3215957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3215957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3215957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3215957 prefixEnd_3215957 := by exact prefixLift 3215957
  have htrace : WordTrace (prefixWord ++ tailWord_3215957) baseStart_3215957 baseEnd_3215957 := by
    simpa [prefixWord, tailWord_3215957, baseEnd_3215957] using wordTrace_append hprefix tailTrace_3215957
  have hstable : (prefixWord ++ tailWord_3215957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215957).length < 2 ^ (prefixWord ++ tailWord_3215957).sum := by decide
  have hdescent : baseEnd_3215957 < baseStart_3215957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216004 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3216004 : Nat := 118140960795 + 3216004 * 2 ^ 59
def prefixEnd_3216004 : Nat := 4983230072969 + 3 ^ 40 * 3216004 * 2
def baseEnd_3216004 : Nat := 1651355838782140603259873

theorem tailTrace_3216004 : CollatzResearch.WordTrace tailWord_3216004 prefixEnd_3216004 1651355838782140603259873 := by
  unfold tailWord_3216004
  simp only [CollatzResearch.WordTrace]
  refine ⟨58648651120487116300151533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78198201493982821733535377 58648651120487116300151533)
  ·
    refine ⟨21993244170182668612556825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58648651120487116300151533 21993244170182668612556825)
    ·
      refine ⟨16494933127637001459417619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21993244170182668612556825 16494933127637001459417619)
      ·
        refine ⟨24742399691455502189126429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16494933127637001459417619 24742399691455502189126429)
        ·
          refine ⟨9278399884295813320922411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24742399691455502189126429 9278399884295813320922411)
          ·
            refine ⟨13917599826443719981383617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278399884295813320922411 13917599826443719981383617)
            ·
              refine ⟨10438199869832789986037713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13917599826443719981383617 10438199869832789986037713)
              ·
                refine ⟨7828649902374592489528285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438199869832789986037713 7828649902374592489528285)
                ·
                  refine ⟨2935743713390472183573107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7828649902374592489528285 2935743713390472183573107)
                  ·
                    refine ⟨4403615570085708275359661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2935743713390472183573107 4403615570085708275359661)
                    ·
                      refine ⟨1651355838782140603259873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4403615570085708275359661 1651355838782140603259873)
                      ·
                        rfl

theorem cell23_3216004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3216004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216004 prefixEnd_3216004 := by exact prefixLift 3216004
  have htrace : WordTrace (prefixWord ++ tailWord_3216004) baseStart_3216004 baseEnd_3216004 := by
    simpa [prefixWord, tailWord_3216004, baseEnd_3216004] using wordTrace_append hprefix tailTrace_3216004
  have hstable : (prefixWord ++ tailWord_3216004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216004).length < 2 ^ (prefixWord ++ tailWord_3216004).sum := by decide
  have hdescent : baseEnd_3216004 < baseStart_3216004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216007 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 1, 5]
def baseStart_3216007 : Nat := 118140960795 + 3216007 * 2 ^ 59
def prefixEnd_3216007 : Nat := 4983230072969 + 3 ^ 40 * 3216007 * 2
def baseEnd_3216007 : Nat := 550452459741368030507453

theorem tailTrace_3216007 : CollatzResearch.WordTrace tailWord_3216007 prefixEnd_3216007 550452459741368030507453 := by
  unfold tailWord_3216007
  simp only [CollatzResearch.WordTrace]
  refine ⟨117297411659963364112662275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78198274439975576075108183 117297411659963364112662275)
  ·
    refine ⟨175946117489945046168993413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117297411659963364112662275 175946117489945046168993413)
    ·
      refine ⟨32989897029364696156686265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175946117489945046168993413 32989897029364696156686265)
      ·
        refine ⟨24742422772023522117514699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32989897029364696156686265 24742422772023522117514699)
        ·
          refine ⟨37113634158035283176272049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24742422772023522117514699 37113634158035283176272049)
          ·
            refine ⟨27835225618526462382204037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37113634158035283176272049 27835225618526462382204037)
            ·
              refine ⟨5219104803473711696663257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27835225618526462382204037 5219104803473711696663257)
              ·
                refine ⟨3914328602605283772497443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5219104803473711696663257 3914328602605283772497443)
                ·
                  refine ⟨5871492903907925658746165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914328602605283772497443 5871492903907925658746165)
                  ·
                    refine ⟨550452459741368030507453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5871492903907925658746165 550452459741368030507453)
                    ·
                      rfl

theorem cell23_3216007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_3216007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216007 prefixEnd_3216007 := by exact prefixLift 3216007
  have htrace : WordTrace (prefixWord ++ tailWord_3216007) baseStart_3216007 baseEnd_3216007 := by
    simpa [prefixWord, tailWord_3216007, baseEnd_3216007] using wordTrace_append hprefix tailTrace_3216007
  have hstable : (prefixWord ++ tailWord_3216007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216007).length < 2 ^ (prefixWord ++ tailWord_3216007).sum := by decide
  have hdescent : baseEnd_3216007 < baseStart_3216007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216014 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3216014 : Nat := 118140960795 + 3216014 * 2 ^ 59
def prefixEnd_3216014 : Nat := 4983230072969 + 3 ^ 40 * 3216014 * 2
def baseEnd_3216014 : Nat := 1651360973588685564134827

theorem tailTrace_3216014 : CollatzResearch.WordTrace tailWord_3216014 prefixEnd_3216014 1651360973588685564134827 := by
  unfold tailWord_3216014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14662208371367250538520887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78198444647292002872111397 14662208371367250538520887)
  ·
    refine ⟨21993312557050875807781331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14662208371367250538520887 21993312557050875807781331)
    ·
      refine ⟨32989968835576313711671997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21993312557050875807781331 32989968835576313711671997)
      ·
        refine ⟨12371238313341117641876999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32989968835576313711671997 12371238313341117641876999)
        ·
          refine ⟨18556857470011676462815499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12371238313341117641876999 18556857470011676462815499)
          ·
            refine ⟨27835286205017514694223249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556857470011676462815499 27835286205017514694223249)
            ·
              refine ⟨20876464653763136020667437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27835286205017514694223249 20876464653763136020667437)
              ·
                refine ⟨7828674245161176007750289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20876464653763136020667437 7828674245161176007750289)
                ·
                  refine ⟨5871505683870882005812717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828674245161176007750289 5871505683870882005812717)
                  ·
                    refine ⟨2201814631451580752179769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5871505683870882005812717 2201814631451580752179769)
                    ·
                      refine ⟨1651360973588685564134827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201814631451580752179769 1651360973588685564134827)
                      ·
                        rfl

theorem cell23_3216014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3216014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216014 prefixEnd_3216014 := by exact prefixLift 3216014
  have htrace : WordTrace (prefixWord ++ tailWord_3216014) baseStart_3216014 baseEnd_3216014 := by
    simpa [prefixWord, tailWord_3216014, baseEnd_3216014] using wordTrace_append hprefix tailTrace_3216014
  have hstable : (prefixWord ++ tailWord_3216014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216014).length < 2 ^ (prefixWord ++ tailWord_3216014).sum := by decide
  have hdescent : baseEnd_3216014 < baseStart_3216014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216037 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_3216037 : Nat := 118140960795 + 3216037 * 2 ^ 59
def prefixEnd_3216037 : Nat := 4983230072969 + 3 ^ 40 * 3216037 * 2
def baseEnd_3216037 : Nat := 550457594547912991382407

theorem tailTrace_3216037 : CollatzResearch.WordTrace tailWord_3216037 prefixEnd_3216037 550457594547912991382407 := by
  unfold tailWord_3216037
  simp only [CollatzResearch.WordTrace]
  refine ⟨117298505849854679236254365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78199003899903119490836243 117298505849854679236254365)
  ·
    refine ⟨43986939693695504713595387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117298505849854679236254365 43986939693695504713595387)
    ·
      refine ⟨65980409540543257070393081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43986939693695504713595387 65980409540543257070393081)
      ·
        refine ⟨49485307155407442802794811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65980409540543257070393081 49485307155407442802794811)
        ·
          refine ⟨74227960733111164204192217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49485307155407442802794811 74227960733111164204192217)
          ·
            refine ⟨55670970549833373153144163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74227960733111164204192217 55670970549833373153144163)
            ·
              refine ⟨83506455824750059729716245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55670970549833373153144163 83506455824750059729716245)
              ·
                refine ⟨3914365116785159049830449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83506455824750059729716245 3914365116785159049830449)
                ·
                  refine ⟨2935773837588869287372837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914365116785159049830449 2935773837588869287372837)
                  ·
                    refine ⟨550457594547912991382407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935773837588869287372837 550457594547912991382407)
                    ·
                      rfl

theorem cell23_3216037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_3216037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216037 prefixEnd_3216037 := by exact prefixLift 3216037
  have htrace : WordTrace (prefixWord ++ tailWord_3216037) baseStart_3216037 baseEnd_3216037 := by
    simpa [prefixWord, tailWord_3216037, baseEnd_3216037] using wordTrace_append hprefix tailTrace_3216037
  have hstable : (prefixWord ++ tailWord_3216037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216037).length < 2 ^ (prefixWord ++ tailWord_3216037).sum := by decide
  have hdescent : baseEnd_3216037 < baseStart_3216037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216064 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3]
def baseStart_3216064 : Nat := 118140960795 + 3216064 * 2 ^ 59
def prefixEnd_3216064 : Nat := 4983230072969 + 3 ^ 40 * 3216064 * 2
def baseEnd_3216064 : Nat := 1651386647621410368509597

theorem tailTrace_3216064 : CollatzResearch.WordTrace tailWord_3216064 prefixEnd_3216064 1651386647621410368509597 := by
  unfold tailWord_3216064
  simp only [CollatzResearch.WordTrace]
  refine ⟨58649745310378431423743623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78199660413837908564991497 58649745310378431423743623)
  ·
    refine ⟨87974617965567647135615435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58649745310378431423743623 87974617965567647135615435)
    ·
      refine ⟨131961926948351470703423153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87974617965567647135615435 131961926948351470703423153)
      ·
        refine ⟨98971445211263603027567365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131961926948351470703423153 98971445211263603027567365)
        ·
          refine ⟨18557145977111925567668881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98971445211263603027567365 18557145977111925567668881)
          ·
            refine ⟨13917859482833944175751661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18557145977111925567668881 13917859482833944175751661)
            ·
              refine ⟨5219197306062729065906873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13917859482833944175751661 5219197306062729065906873)
              ·
                refine ⟨3914397979547046799430155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5219197306062729065906873 3914397979547046799430155)
                ·
                  refine ⟨5871596969320570199145233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914397979547046799430155 5871596969320570199145233)
                  ·
                    refine ⟨4403697726990427649358925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871596969320570199145233 4403697726990427649358925)
                    ·
                      refine ⟨1651386647621410368509597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4403697726990427649358925 1651386647621410368509597)
                      ·
                        rfl

theorem cell23_3216064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_3216064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216064 prefixEnd_3216064 := by exact prefixLift 3216064
  have htrace : WordTrace (prefixWord ++ tailWord_3216064) baseStart_3216064 baseEnd_3216064 := by
    simpa [prefixWord, tailWord_3216064, baseEnd_3216064] using wordTrace_append hprefix tailTrace_3216064
  have hstable : (prefixWord ++ tailWord_3216064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216064).length < 2 ^ (prefixWord ++ tailWord_3216064).sum := by decide
  have hdescent : baseEnd_3216064 < baseStart_3216064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216095 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 1, 2, 2]
def baseStart_3216095 : Nat := 118140960795 + 3216095 * 2 ^ 59
def prefixEnd_3216095 : Nat := 4983230072969 + 3 ^ 40 * 3216095 * 2
def baseEnd_3216095 : Nat := 1651402565521699747221955

theorem tailTrace_3216095 : CollatzResearch.WordTrace tailWord_3216095 prefixEnd_3216095 1651402565521699747221955 := by
  unfold tailWord_3216095
  simp only [CollatzResearch.WordTrace]
  refine ⟨117300621283644555141865739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78200414189096370094577159 117300621283644555141865739)
  ·
    refine ⟨175950931925466832712798609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117300621283644555141865739 175950931925466832712798609)
    ·
      refine ⟨131963198944100124534598957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175950931925466832712798609 131963198944100124534598957)
      ·
        refine ⟨49486199604037546700474609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131963198944100124534598957 49486199604037546700474609)
        ·
          refine ⟨37114649703028160025355957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49486199604037546700474609 37114649703028160025355957)
          ·
            refine ⟨3479498409658890002377121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37114649703028160025355957 3479498409658890002377121)
            ·
              refine ⟨2609623807244167501782841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479498409658890002377121 2609623807244167501782841)
              ·
                refine ⟨1957217855433125626337131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609623807244167501782841 1957217855433125626337131)
                ·
                  refine ⟨2935826783149688439505697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957217855433125626337131 2935826783149688439505697)
                  ·
                    refine ⟨2201870087362266329629273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935826783149688439505697 2201870087362266329629273)
                    ·
                      refine ⟨1651402565521699747221955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201870087362266329629273 1651402565521699747221955)
                      ·
                        rfl

theorem cell23_3216095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_3216095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216095 prefixEnd_3216095 := by exact prefixLift 3216095
  have htrace : WordTrace (prefixWord ++ tailWord_3216095) baseStart_3216095 baseEnd_3216095 := by
    simpa [prefixWord, tailWord_3216095, baseEnd_3216095] using wordTrace_append hprefix tailTrace_3216095
  have hstable : (prefixWord ++ tailWord_3216095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216095).length < 2 ^ (prefixWord ++ tailWord_3216095).sum := by decide
  have hdescent : baseEnd_3216095 < baseStart_3216095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216140 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 11]
def baseStart_3216140 : Nat := 118140960795 + 3216140 * 2 ^ 59
def prefixEnd_3216140 : Nat := 4983230072969 + 3 ^ 40 * 3216140 * 2
def baseEnd_3216140 : Nat := 183491741350128007906583

theorem tailTrace_3216140 : CollatzResearch.WordTrace tailWord_3216140 prefixEnd_3216140 183491741350128007906583 := by
  unfold tailWord_3216140
  simp only [CollatzResearch.WordTrace]
  refine ⟨58651131284240763913626937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78201508378987685218169249 58651131284240763913626937)
  ·
    refine ⟨43988348463180572935220203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58651131284240763913626937 43988348463180572935220203)
    ·
      refine ⟨65982522694770859402830305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43988348463180572935220203 65982522694770859402830305)
      ·
        refine ⟨49486892021078144552122729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65982522694770859402830305 49486892021078144552122729)
        ·
          refine ⟨37115169015808608414092047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49486892021078144552122729 37115169015808608414092047)
          ·
            refine ⟨55672753523712912621138071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37115169015808608414092047 55672753523712912621138071)
            ·
              refine ⟨83509130285569368931707107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55672753523712912621138071 83509130285569368931707107)
              ·
                refine ⟨125263695428354053397560661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83509130285569368931707107 125263695428354053397560661)
                ·
                  refine ⟨183491741350128007906583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 125263695428354053397560661 183491741350128007906583)
                  ·
                    rfl

theorem cell23_3216140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_3216140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216140 prefixEnd_3216140 := by exact prefixLift 3216140
  have htrace : WordTrace (prefixWord ++ tailWord_3216140) baseStart_3216140 baseEnd_3216140 := by
    simpa [prefixWord, tailWord_3216140, baseEnd_3216140] using wordTrace_append hprefix tailTrace_3216140
  have hstable : (prefixWord ++ tailWord_3216140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216140).length < 2 ^ (prefixWord ++ tailWord_3216140).sum := by decide
  have hdescent : baseEnd_3216140 < baseStart_3216140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216174 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_3216174 : Nat := 118140960795 + 3216174 * 2 ^ 59
def prefixEnd_3216174 : Nat := 4983230072969 + 3 ^ 40 * 3216174 * 2
def baseEnd_3216174 : Nat := 183493681165933882014899

theorem tailTrace_3216174 : CollatzResearch.WordTrace tailWord_3216174 prefixEnd_3216174 183493681165933882014899 := by
  unfold tailWord_3216174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14662937831294793954248947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78202335100238901089327717 14662937831294793954248947)
  ·
    refine ⟨21994406746942190931373421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14662937831294793954248947 21994406746942190931373421)
    ·
      refine ⟨8247902530103321599265033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21994406746942190931373421 8247902530103321599265033)
      ·
        refine ⟨6185926897577491199448775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8247902530103321599265033 6185926897577491199448775)
        ·
          refine ⟨9278890346366236799173163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185926897577491199448775 9278890346366236799173163)
          ·
            refine ⟨13918335519549355198759745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278890346366236799173163 13918335519549355198759745)
            ·
              refine ⟨10438751639662016399069809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13918335519549355198759745 10438751639662016399069809)
              ·
                refine ⟨7829063729746512299302357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438751639662016399069809 7829063729746512299302357)
                ·
                  refine ⟨183493681165933882014899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7829063729746512299302357 183493681165933882014899)
                  ·
                    rfl

theorem cell23_3216174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_3216174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216174 prefixEnd_3216174 := by exact prefixLift 3216174
  have htrace : WordTrace (prefixWord ++ tailWord_3216174) baseStart_3216174 baseEnd_3216174 := by
    simpa [prefixWord, tailWord_3216174, baseEnd_3216174] using wordTrace_append hprefix tailTrace_3216174
  have hstable : (prefixWord ++ tailWord_3216174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216174).length < 2 ^ (prefixWord ++ tailWord_3216174).sum := by decide
  have hdescent : baseEnd_3216174 < baseStart_3216174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216191 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 5]
def baseStart_3216191 : Nat := 118140960795 + 3216191 * 2 ^ 59
def prefixEnd_3216191 : Nat := 4983230072969 + 3 ^ 40 * 3216191 * 2
def baseEnd_3216191 : Nat := 183494651073836819069057

theorem tailTrace_3216191 : CollatzResearch.WordTrace tailWord_3216191 prefixEnd_3216191 183494651073836819069057 := by
  unfold tailWord_3216191
  simp only [CollatzResearch.WordTrace]
  refine ⟨117304122691296763537360427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78202748460864509024906951 117304122691296763537360427)
  ·
    refine ⟨175956184036945145306040641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117304122691296763537360427 175956184036945145306040641)
    ·
      refine ⟨131967138027708858979530481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175956184036945145306040641 131967138027708858979530481)
      ·
        refine ⟨98975353520781644234647861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131967138027708858979530481 98975353520781644234647861)
        ·
          refine ⟨9278939392573279146998237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98975353520781644234647861 9278939392573279146998237)
          ·
            refine ⟨3479602272214979680124339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9278939392573279146998237 3479602272214979680124339)
            ·
              refine ⟨5219403408322469520186509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479602272214979680124339 5219403408322469520186509)
              ·
                refine ⟨1957276278120926070069941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5219403408322469520186509 1957276278120926070069941)
                ·
                  refine ⟨183494651073836819069057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1957276278120926070069941 183494651073836819069057)
                  ·
                    rfl

theorem cell23_3216191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 5].length) (baseStart_3216191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216191 prefixEnd_3216191 := by exact prefixLift 3216191
  have htrace : WordTrace (prefixWord ++ tailWord_3216191) baseStart_3216191 baseEnd_3216191 := by
    simpa [prefixWord, tailWord_3216191, baseEnd_3216191] using wordTrace_append hprefix tailTrace_3216191
  have hstable : (prefixWord ++ tailWord_3216191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216191).length < 2 ^ (prefixWord ++ tailWord_3216191).sum := by decide
  have hdescent : baseEnd_3216191 < baseStart_3216191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216204 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_3216204 : Nat := 118140960795 + 3216204 * 2 ^ 59
def prefixEnd_3216204 : Nat := 4983230072969 + 3 ^ 40 * 3216204 * 2
def baseEnd_3216204 : Nat := 550486178304346606919651

theorem tailTrace_3216204 : CollatzResearch.WordTrace tailWord_3216204 prefixEnd_3216204 550486178304346606919651 := by
  unfold tailWord_3216204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58652298420124833378791833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78203064560166444505055777 58652298420124833378791833)
  ·
    refine ⟨43989223815093625034093875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58652298420124833378791833 43989223815093625034093875)
    ·
      refine ⟨65983835722640437551140813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43989223815093625034093875 65983835722640437551140813)
      ·
        refine ⟨24743938395990164081677805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65983835722640437551140813 24743938395990164081677805)
        ·
          refine ⟨9278976898496311530629177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24743938395990164081677805 9278976898496311530629177)
          ·
            refine ⟨6959232673872233647971883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9278976898496311530629177 6959232673872233647971883)
            ·
              refine ⟨10438849010808350471957825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959232673872233647971883 10438849010808350471957825)
              ·
                refine ⟨7829136758106262853968369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438849010808350471957825 7829136758106262853968369)
                ·
                  refine ⟨5871852568579697140476277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7829136758106262853968369 5871852568579697140476277)
                  ·
                    refine ⟨550486178304346606919651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5871852568579697140476277 550486178304346606919651)
                    ·
                      rfl

theorem cell23_3216204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_3216204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216204 prefixEnd_3216204 := by exact prefixLift 3216204
  have htrace : WordTrace (prefixWord ++ tailWord_3216204) baseStart_3216204 baseEnd_3216204 := by
    simpa [prefixWord, tailWord_3216204, baseEnd_3216204] using wordTrace_append hprefix tailTrace_3216204
  have hstable : (prefixWord ++ tailWord_3216204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216204).length < 2 ^ (prefixWord ++ tailWord_3216204).sum := by decide
  have hdescent : baseEnd_3216204 < baseStart_3216204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216224 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 6, 2]
def baseStart_3216224 : Nat := 118140960795 + 3216224 * 2 ^ 59
def prefixEnd_3216224 : Nat := 4983230072969 + 3 ^ 40 * 3216224 * 2
def baseEnd_3216224 : Nat := 1651468804526129742508861

theorem tailTrace_3216224 : CollatzResearch.WordTrace tailWord_3216224 prefixEnd_3216224 1651468804526129742508861 := by
  unfold tailWord_3216224
  simp only [CollatzResearch.WordTrace]
  refine ⟨58652663150088605086655863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78203550866784806782207817 58652663150088605086655863)
  ·
    refine ⟨87978994725132907629983795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58652663150088605086655863 87978994725132907629983795)
    ·
      refine ⟨131968492087699361444975693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87978994725132907629983795 131968492087699361444975693)
      ·
        refine ⟨49488184532887260541865885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131968492087699361444975693 49488184532887260541865885)
        ·
          refine ⟨18558069199832722703199707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49488184532887260541865885 18558069199832722703199707)
          ·
            refine ⟨27837103799749084054799561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18558069199832722703199707 27837103799749084054799561)
            ·
              refine ⟨20877827849811813041099671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27837103799749084054799561 20877827849811813041099671)
              ·
                refine ⟨31316741774717719561649507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20877827849811813041099671 31316741774717719561649507)
                ·
                  refine ⟨46975112662076579342474261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31316741774717719561649507 46975112662076579342474261)
                  ·
                    refine ⟨2201958406034839656678481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46975112662076579342474261 2201958406034839656678481)
                    ·
                      refine ⟨1651468804526129742508861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2201958406034839656678481 1651468804526129742508861)
                      ·
                        rfl

theorem cell23_3216224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_3216224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216224 prefixEnd_3216224 := by exact prefixLift 3216224
  have htrace : WordTrace (prefixWord ++ tailWord_3216224) baseStart_3216224 baseEnd_3216224 := by
    simpa [prefixWord, tailWord_3216224, baseEnd_3216224] using wordTrace_append hprefix tailTrace_3216224
  have hstable : (prefixWord ++ tailWord_3216224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216224).length < 2 ^ (prefixWord ++ tailWord_3216224).sum := by decide
  have hdescent : baseEnd_3216224 < baseStart_3216224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216237 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3216237 : Nat := 118140960795 + 3216237 * 2 ^ 59
def prefixEnd_3216237 : Nat := 4983230072969 + 3 ^ 40 * 3216237 * 2
def baseEnd_3216237 : Nat := 1651475479774638191646301

theorem tailTrace_3216237 : CollatzResearch.WordTrace tailWord_3216237 prefixEnd_3216237 1651475479774638191646301 := by
  unfold tailWord_3216237
  simp only [CollatzResearch.WordTrace]
  refine ⟨117305800449130113393534965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78203866966086742262356643 117305800449130113393534965)
  ·
    refine ⟨10997418792105948130643903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117305800449130113393534965 10997418792105948130643903)
    ·
      refine ⟨16496128188158922195965855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10997418792105948130643903 16496128188158922195965855)
      ·
        refine ⟨24744192282238383293948783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16496128188158922195965855 24744192282238383293948783)
        ·
          refine ⟨37116288423357574940923175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24744192282238383293948783 37116288423357574940923175)
          ·
            refine ⟨55674432635036362411384763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37116288423357574940923175 55674432635036362411384763)
            ·
              refine ⟨83511648952554543617077145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55674432635036362411384763 83511648952554543617077145)
              ·
                refine ⟨62633736714415907712807859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83511648952554543617077145 62633736714415907712807859)
                ·
                  refine ⟨93950605071623861569211789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62633736714415907712807859 93950605071623861569211789)
                  ·
                    refine ⟨35231476901858948088454421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93950605071623861569211789 35231476901858948088454421)
                    ·
                      refine ⟨1651475479774638191646301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35231476901858948088454421 1651475479774638191646301)
                      ·
                        rfl

theorem cell23_3216237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3216237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216237 prefixEnd_3216237 := by exact prefixLift 3216237
  have htrace : WordTrace (prefixWord ++ tailWord_3216237) baseStart_3216237 baseEnd_3216237 := by
    simpa [prefixWord, tailWord_3216237, baseEnd_3216237] using wordTrace_append hprefix tailTrace_3216237
  have hstable : (prefixWord ++ tailWord_3216237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216237).length < 2 ^ (prefixWord ++ tailWord_3216237).sum := by decide
  have hdescent : baseEnd_3216237 < baseStart_3216237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216264 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 6]
def baseStart_3216264 : Nat := 118140960795 + 3216264 * 2 ^ 59
def prefixEnd_3216264 : Nat := 4983230072969 + 3 ^ 40 * 3216264 * 2
def baseEnd_3216264 : Nat := 183498815972478842889853

theorem tailTrace_3216264 : CollatzResearch.WordTrace tailWord_3216264 prefixEnd_3216264 183498815972478842889853 := by
  unfold tailWord_3216264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58653392610016148502383923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78204523480021531336511897 58653392610016148502383923)
  ·
    refine ⟨87980088915024222753575885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58653392610016148502383923 87980088915024222753575885)
    ·
      refine ⟨32992533343134083532590957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87980088915024222753575885 32992533343134083532590957)
      ·
        refine ⟨12372200003675281324721609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32992533343134083532590957 12372200003675281324721609)
        ·
          refine ⟨9279150002756460993541207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12372200003675281324721609 9279150002756460993541207)
          ·
            refine ⟨13918725004134691490311811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279150002756460993541207 13918725004134691490311811)
            ·
              refine ⟨20878087506202037235467717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13918725004134691490311811 20878087506202037235467717)
              ·
                refine ⟨3914641407412881981650197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20878087506202037235467717 3914641407412881981650197)
                ·
                  refine ⟨183498815972478842889853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3914641407412881981650197 183498815972478842889853)
                  ·
                    rfl

theorem cell23_3216264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 6].length) (baseStart_3216264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216264 prefixEnd_3216264 := by exact prefixLift 3216264
  have htrace : WordTrace (prefixWord ++ tailWord_3216264) baseStart_3216264 baseEnd_3216264 := by
    simpa [prefixWord, tailWord_3216264, baseEnd_3216264] using wordTrace_append hprefix tailTrace_3216264
  have hstable : (prefixWord ++ tailWord_3216264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216264).length < 2 ^ (prefixWord ++ tailWord_3216264).sum := by decide
  have hdescent : baseEnd_3216264 < baseStart_3216264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216268 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_3216268 : Nat := 118140960795 + 3216268 * 2 ^ 59
def prefixEnd_3216268 : Nat := 4983230072969 + 3 ^ 40 * 3216268 * 2
def baseEnd_3216268 : Nat := 550497132558309190119553

theorem tailTrace_3216268 : CollatzResearch.WordTrace tailWord_3216268 prefixEnd_3216268 550497132558309190119553 := by
  unfold tailWord_3216268
  simp only [CollatzResearch.WordTrace]
  refine ⟨58653465556008902843956729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78204620741345203791942305 58653465556008902843956729)
  ·
    refine ⟨43990099167006677132967547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58653465556008902843956729 43990099167006677132967547)
    ·
      refine ⟨65985148750510015699451321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43990099167006677132967547 65985148750510015699451321)
      ·
        refine ⟨49488861562882511774588491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65985148750510015699451321 49488861562882511774588491)
        ·
          refine ⟨74233292344323767661882737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49488861562882511774588491 74233292344323767661882737)
          ·
            refine ⟨55674969258242825746412053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74233292344323767661882737 55674969258242825746412053)
            ·
              refine ⟨2609764183980132456863065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55674969258242825746412053 2609764183980132456863065)
              ·
                refine ⟨1957323137985099342647299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609764183980132456863065 1957323137985099342647299)
                ·
                  refine ⟨2935984706977649013970949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957323137985099342647299 2935984706977649013970949)
                  ·
                    refine ⟨550497132558309190119553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935984706977649013970949 550497132558309190119553)
                    ·
                      rfl

theorem cell23_3216268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_3216268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216268 prefixEnd_3216268 := by exact prefixLift 3216268
  have htrace : WordTrace (prefixWord ++ tailWord_3216268) baseStart_3216268 baseEnd_3216268 := by
    simpa [prefixWord, tailWord_3216268, baseEnd_3216268] using wordTrace_append hprefix tailTrace_3216268
  have hstable : (prefixWord ++ tailWord_3216268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216268).length < 2 ^ (prefixWord ++ tailWord_3216268).sum := by decide
  have hdescent : baseEnd_3216268 < baseStart_3216268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216295 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_3216295 : Nat := 118140960795 + 3216295 * 2 ^ 59
def prefixEnd_3216295 : Nat := 4983230072969 + 3 ^ 40 * 3216295 * 2
def baseEnd_3216295 : Nat := 1651505261652598964721035

theorem tailTrace_3216295 : CollatzResearch.WordTrace tailWord_3216295 prefixEnd_3216295 1651505261652598964721035 := by
  unfold tailWord_3216295
  simp only [CollatzResearch.WordTrace]
  refine ⟨117307915882919989299146339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78205277255279992866097559 117307915882919989299146339)
  ·
    refine ⟨175961873824379983948719509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117307915882919989299146339 175961873824379983948719509)
    ·
      refine ⟨8248212835517811747596227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175961873824379983948719509 8248212835517811747596227)
      ·
        refine ⟨12372319253276717621394341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248212835517811747596227 12372319253276717621394341)
        ·
          refine ⟨2319809859989384554011439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12372319253276717621394341 2319809859989384554011439)
          ·
            refine ⟨3479714789984076831017159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319809859989384554011439 3479714789984076831017159)
            ·
              refine ⟨5219572184976115246525739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479714789984076831017159 5219572184976115246525739)
              ·
                refine ⟨7829358277464172869788609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219572184976115246525739 7829358277464172869788609)
                ·
                  refine ⟨5872018708098129652341457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7829358277464172869788609 5872018708098129652341457)
                  ·
                    refine ⟨4404014031073597239256093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872018708098129652341457 4404014031073597239256093)
                    ·
                      refine ⟨1651505261652598964721035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404014031073597239256093 1651505261652598964721035)
                      ·
                        rfl

theorem cell23_3216295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_3216295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216295 prefixEnd_3216295 := by exact prefixLift 3216295
  have htrace : WordTrace (prefixWord ++ tailWord_3216295) baseStart_3216295 baseEnd_3216295 := by
    simpa [prefixWord, tailWord_3216295, baseEnd_3216295] using wordTrace_append hprefix tailTrace_3216295
  have hstable : (prefixWord ++ tailWord_3216295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216295).length < 2 ^ (prefixWord ++ tailWord_3216295).sum := by decide
  have hdescent : baseEnd_3216295 < baseStart_3216295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216307 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 3, 6]
def baseStart_3216307 : Nat := 118140960795 + 3216307 * 2 ^ 59
def prefixEnd_3216307 : Nat := 4983230072969 + 3 ^ 40 * 3216307 * 2
def baseEnd_3216307 : Nat := 550503807806817639256993

theorem tailTrace_3216307 : CollatzResearch.WordTrace tailWord_3216307 prefixEnd_3216307 550503807806817639256993 := by
  unfold tailWord_3216307
  simp only [CollatzResearch.WordTrace]
  refine ⟨117308353558876515348583175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78205569039251010232388783 117308353558876515348583175)
  ·
    refine ⟨175962530338314773022874763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117308353558876515348583175 175962530338314773022874763)
    ·
      refine ⟨263943795507472159534312145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175962530338314773022874763 263943795507472159534312145)
      ·
        refine ⟨197957846630604119650734109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263943795507472159534312145 197957846630604119650734109)
        ·
          refine ⟨74234192486476544869025291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197957846630604119650734109 74234192486476544869025291)
          ·
            refine ⟨111351288729714817303537937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74234192486476544869025291 111351288729714817303537937)
            ·
              refine ⟨83513466547286112977653453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111351288729714817303537937 83513466547286112977653453)
              ·
                refine ⟨31317549955232292366620045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83513466547286112977653453 31317549955232292366620045)
                ·
                  refine ⟨11744081233212109637482517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31317549955232292366620045 11744081233212109637482517)
                  ·
                    refine ⟨550503807806817639256993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11744081233212109637482517 550503807806817639256993)
                    ·
                      rfl

theorem cell23_3216307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 6].length) (baseStart_3216307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216307 prefixEnd_3216307 := by exact prefixLift 3216307
  have htrace : WordTrace (prefixWord ++ tailWord_3216307) baseStart_3216307 baseEnd_3216307 := by
    simpa [prefixWord, tailWord_3216307, baseEnd_3216307] using wordTrace_append hprefix tailTrace_3216307
  have hstable : (prefixWord ++ tailWord_3216307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216307).length < 2 ^ (prefixWord ++ tailWord_3216307).sum := by decide
  have hdescent : baseEnd_3216307 < baseStart_3216307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216311 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 1, 5]
def baseStart_3216311 : Nat := 118140960795 + 3216311 * 2 ^ 59
def prefixEnd_3216311 : Nat := 4983230072969 + 3 ^ 40 * 3216311 * 2
def baseEnd_3216311 : Nat := 550504492447690300706987

theorem tailTrace_3216311 : CollatzResearch.WordTrace tailWord_3216311 prefixEnd_3216311 550504492447690300706987 := by
  unfold tailWord_3216311
  simp only [CollatzResearch.WordTrace]
  refine ⟨117308499450862024031728787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78205666300574682687819191 117308499450862024031728787)
  ·
    refine ⟨175962749176293036047593181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117308499450862024031728787 175962749176293036047593181)
    ·
      refine ⟨65986030941109888517847443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175962749176293036047593181 65986030941109888517847443)
      ·
        refine ⟨98979046411664832776771165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65986030941109888517847443 98979046411664832776771165)
        ·
          refine ⟨37117142404374312291289187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98979046411664832776771165 37117142404374312291289187)
          ·
            refine ⟨55675713606561468436933781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37117142404374312291289187 55675713606561468436933781)
            ·
              refine ⟨2609799075307568832981271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55675713606561468436933781 2609799075307568832981271)
              ·
                refine ⟨3914698612961353249471907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609799075307568832981271 3914698612961353249471907)
                ·
                  refine ⟨5872047919442029874207861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914698612961353249471907 5872047919442029874207861)
                  ·
                    refine ⟨550504492447690300706987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5872047919442029874207861 550504492447690300706987)
                    ·
                      rfl

theorem cell23_3216311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_3216311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216311 prefixEnd_3216311 := by exact prefixLift 3216311
  have htrace : WordTrace (prefixWord ++ tailWord_3216311) baseStart_3216311 baseEnd_3216311 := by
    simpa [prefixWord, tailWord_3216311, baseEnd_3216311] using wordTrace_append hprefix tailTrace_3216311
  have hstable : (prefixWord ++ tailWord_3216311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216311).length < 2 ^ (prefixWord ++ tailWord_3216311).sum := by decide
  have hdescent : baseEnd_3216311 < baseStart_3216311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216334 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3216334 : Nat := 118140960795 + 3216334 * 2 ^ 59
def prefixEnd_3216334 : Nat := 4983230072969 + 3 ^ 40 * 3216334 * 2
def baseEnd_3216334 : Nat := 1651525287398124312133355

theorem tailTrace_3216334 : CollatzResearch.WordTrace tailWord_3216334 prefixEnd_3216334 1651525287398124312133355 := by
  unfold tailWord_3216334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14663667291222337369977007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78206225553185799306544037 14663667291222337369977007)
  ·
    refine ⟨21995500936833506054965511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14663667291222337369977007 21995500936833506054965511)
    ·
      refine ⟨32993251405250259082448267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21995500936833506054965511 32993251405250259082448267)
      ·
        refine ⟨49489877107875388623672401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32993251405250259082448267 49489877107875388623672401)
        ·
          refine ⟨37117407830906541467754301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49489877107875388623672401 37117407830906541467754301)
          ·
            refine ⟨13919027936589953050407863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37117407830906541467754301 13919027936589953050407863)
            ·
              refine ⟨20878541904884929575611795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919027936589953050407863 20878541904884929575611795)
              ·
                refine ⟨31317812857327394363417693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20878541904884929575611795 31317812857327394363417693)
                ·
                  refine ⟨11744179821497772886281635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31317812857327394363417693 11744179821497772886281635)
                  ·
                    refine ⟨17616269732246659329422453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11744179821497772886281635 17616269732246659329422453)
                    ·
                      refine ⟨1651525287398124312133355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17616269732246659329422453 1651525287398124312133355)
                      ·
                        rfl

theorem cell23_3216334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3216334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216334 prefixEnd_3216334 := by exact prefixLift 3216334
  have htrace : WordTrace (prefixWord ++ tailWord_3216334) baseStart_3216334 baseEnd_3216334 := by
    simpa [prefixWord, tailWord_3216334, baseEnd_3216334] using wordTrace_append hprefix tailTrace_3216334
  have hstable : (prefixWord ++ tailWord_3216334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216334).length < 2 ^ (prefixWord ++ tailWord_3216334).sum := by decide
  have hdescent : baseEnd_3216334 < baseStart_3216334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216337 : List Nat := [1, 2, 2, 1, 2, 1, 4, 10]
def baseStart_3216337 : Nat := 118140960795 + 3216337 * 2 ^ 59
def prefixEnd_3216337 : Nat := 4983230072969 + 3 ^ 40 * 3216337 * 2
def baseEnd_3216337 : Nat := 61167660290373622236883

theorem tailTrace_3216337 : CollatzResearch.WordTrace tailWord_3216337 prefixEnd_3216337 61167660290373622236883 := by
  unfold tailWord_3216337
  simp only [CollatzResearch.WordTrace]
  refine ⟨117309447748767830472175265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78206298499178553648116843 117309447748767830472175265)
  ·
    refine ⟨87982085811575872854131449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117309447748767830472175265 87982085811575872854131449)
    ·
      refine ⟨65986564358681904640598587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87982085811575872854131449 65986564358681904640598587)
      ·
        refine ⟨98979846538022856960897881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65986564358681904640598587 98979846538022856960897881)
        ·
          refine ⟨74234884903517142720673411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98979846538022856960897881 74234884903517142720673411)
          ·
            refine ⟨111352327355275714081010117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74234884903517142720673411 111352327355275714081010117)
            ·
              refine ⟨20878561379114196390189397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111352327355275714081010117 20878561379114196390189397)
              ·
                refine ⟨61167660290373622236883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20878561379114196390189397 61167660290373622236883)
                ·
                  rfl

theorem cell23_3216337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 10].length) (baseStart_3216337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216337 prefixEnd_3216337 := by exact prefixLift 3216337
  have htrace : WordTrace (prefixWord ++ tailWord_3216337) baseStart_3216337 baseEnd_3216337 := by
    simpa [prefixWord, tailWord_3216337, baseEnd_3216337] using wordTrace_append hprefix tailTrace_3216337
  have hstable : (prefixWord ++ tailWord_3216337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216337).length < 2 ^ (prefixWord ++ tailWord_3216337).sum := by decide
  have hdescent : baseEnd_3216337 < baseStart_3216337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216344 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3216344 : Nat := 118140960795 + 3216344 * 2 ^ 59
def prefixEnd_3216344 : Nat := 4983230072969 + 3 ^ 40 * 3216344 * 2
def baseEnd_3216344 : Nat := 1651530422204669273008309

theorem tailTrace_3216344 : CollatzResearch.WordTrace tailWord_3216344 prefixEnd_3216344 1651530422204669273008309 := by
  unfold tailWord_3216344
  simp only [CollatzResearch.WordTrace]
  refine ⟨58654851529871235333840043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78206468706494980445120057 58654851529871235333840043)
  ·
    refine ⟨87982277294806853000760065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58654851529871235333840043 87982277294806853000760065)
    ·
      refine ⟨65986707971105139750570049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87982277294806853000760065 65986707971105139750570049)
      ·
        refine ⟨49490030978328854812927537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65986707971105139750570049 49490030978328854812927537)
        ·
          refine ⟨37117523233746641109695653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49490030978328854812927537 37117523233746641109695653)
          ·
            refine ⟨6959535606327495208067935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37117523233746641109695653 6959535606327495208067935)
            ·
              refine ⟨10439303409491242812101903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959535606327495208067935 10439303409491242812101903)
              ·
                refine ⟨15658955114236864218152855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439303409491242812101903 15658955114236864218152855)
                ·
                  refine ⟨23488432671355296327229283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15658955114236864218152855 23488432671355296327229283)
                  ·
                    refine ⟨35232649007032944490843925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23488432671355296327229283 35232649007032944490843925)
                    ·
                      refine ⟨1651530422204669273008309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35232649007032944490843925 1651530422204669273008309)
                      ·
                        rfl

theorem cell23_3216344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3216344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216344 prefixEnd_3216344 := by exact prefixLift 3216344
  have htrace : WordTrace (prefixWord ++ tailWord_3216344) baseStart_3216344 baseEnd_3216344 := by
    simpa [prefixWord, tailWord_3216344, baseEnd_3216344] using wordTrace_append hprefix tailTrace_3216344
  have hstable : (prefixWord ++ tailWord_3216344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216344).length < 2 ^ (prefixWord ++ tailWord_3216344).sum := by decide
  have hdescent : baseEnd_3216344 < baseStart_3216344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216402 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3216402 : Nat := 118140960795 + 3216402 * 2 ^ 59
def prefixEnd_3216402 : Nat := 4983230072969 + 3 ^ 40 * 3216402 * 2
def baseEnd_3216402 : Nat := 1651560204082630046083043

theorem tailTrace_3216402 : CollatzResearch.WordTrace tailWord_3216402 prefixEnd_3216402 1651560204082630046083043 := by
  unfold tailWord_3216402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29327954623383086643322865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78207878995688231048860973 29327954623383086643322865)
  ·
    refine ⟨21995965967537314982492149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29327954623383086643322865 21995965967537314982492149)
    ·
      refine ⟨2062121809456623279608639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21995965967537314982492149 2062121809456623279608639)
      ·
        refine ⟨3093182714184934919412959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062121809456623279608639 3093182714184934919412959)
        ·
          refine ⟨4639774071277402379119439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3093182714184934919412959 4639774071277402379119439)
          ·
            refine ⟨6959661106916103568679159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639774071277402379119439 6959661106916103568679159)
            ·
              refine ⟨10439491660374155353018739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959661106916103568679159 10439491660374155353018739)
              ·
                refine ⟨15659237490561233029528109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439491660374155353018739 15659237490561233029528109)
                ·
                  refine ⟨5872214058960462386073041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15659237490561233029528109 5872214058960462386073041)
                  ·
                    refine ⟨4404160544220346789554781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872214058960462386073041 4404160544220346789554781)
                    ·
                      refine ⟨1651560204082630046083043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404160544220346789554781 1651560204082630046083043)
                      ·
                        rfl

theorem cell23_3216402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3216402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216402 prefixEnd_3216402 := by exact prefixLift 3216402
  have htrace : WordTrace (prefixWord ++ tailWord_3216402) baseStart_3216402 baseEnd_3216402 := by
    simpa [prefixWord, tailWord_3216402, baseEnd_3216402] using wordTrace_append hprefix tailTrace_3216402
  have hstable : (prefixWord ++ tailWord_3216402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216402).length < 2 ^ (prefixWord ++ tailWord_3216402).sum := by decide
  have hdescent : baseEnd_3216402 < baseStart_3216402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216408 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 3, 3, 2]
def baseStart_3216408 : Nat := 118140960795 + 3216408 * 2 ^ 59
def prefixEnd_3216408 : Nat := 4983230072969 + 3 ^ 40 * 3216408 * 2
def baseEnd_3216408 : Nat := 1651563284966557022608015

theorem tailTrace_3216408 : CollatzResearch.WordTrace tailWord_3216408 prefixEnd_3216408 1651563284966557022608015 := by
  unfold tailWord_3216408
  simp only [CollatzResearch.WordTrace]
  refine ⟨58656018665755304799004939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78208024887673739732006585 58656018665755304799004939)
  ·
    refine ⟨87984027998632957198507409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58656018665755304799004939 87984027998632957198507409)
    ·
      refine ⟨65988020998974717898880557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87984027998632957198507409 65988020998974717898880557)
      ·
        refine ⟨24745507874615519212080209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65988020998974717898880557 24745507874615519212080209)
        ·
          refine ⟨18559130905961639409060157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24745507874615519212080209 18559130905961639409060157)
          ·
            refine ⟨6959674089735614778397559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18559130905961639409060157 6959674089735614778397559)
            ·
              refine ⟨10439511134603422167596339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959674089735614778397559 10439511134603422167596339)
              ·
                refine ⟨15659266701905133251394509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439511134603422167596339 15659266701905133251394509)
                ·
                  refine ⟨5872225013214424969272941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15659266701905133251394509 5872225013214424969272941)
                  ·
                    refine ⟨2202084379955409363477353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5872225013214424969272941 2202084379955409363477353)
                    ·
                      refine ⟨1651563284966557022608015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202084379955409363477353 1651563284966557022608015)
                      ·
                        rfl

theorem cell23_3216408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_3216408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216408 prefixEnd_3216408 := by exact prefixLift 3216408
  have htrace : WordTrace (prefixWord ++ tailWord_3216408) baseStart_3216408 baseEnd_3216408 := by
    simpa [prefixWord, tailWord_3216408, baseEnd_3216408] using wordTrace_append hprefix tailTrace_3216408
  have hstable : (prefixWord ++ tailWord_3216408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216408).length < 2 ^ (prefixWord ++ tailWord_3216408).sum := by decide
  have hdescent : baseEnd_3216408 < baseStart_3216408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216441 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3216441 : Nat := 118140960795 + 3216441 * 2 ^ 59
def prefixEnd_3216441 : Nat := 4983230072969 + 3 ^ 40 * 3216441 * 2
def baseEnd_3216441 : Nat := 1651580229828155393495363

theorem tailTrace_3216441 : CollatzResearch.WordTrace tailWord_3216441 prefixEnd_3216441 1651580229828155393495363 := by
  unfold tailWord_3216441
  simp only [CollatzResearch.WordTrace]
  refine ⟨117313240940391056233961177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78208827293594037489307451 117313240940391056233961177)
  ·
    refine ⟨87984930705293292175470883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117313240940391056233961177 87984930705293292175470883)
    ·
      refine ⟨131977396057939938263206325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87984930705293292175470883 131977396057939938263206325)
      ·
        refine ⟨12372880880431869212175593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131977396057939938263206325 12372880880431869212175593)
        ·
          refine ⟨9279660660323901909131695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12372880880431869212175593 9279660660323901909131695)
          ·
            refine ⟨13919490990485852863697543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279660660323901909131695 13919490990485852863697543)
            ·
              refine ⟨20879236485728779295546315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919490990485852863697543 20879236485728779295546315)
              ·
                refine ⟨31318854728593168943319473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20879236485728779295546315 31318854728593168943319473)
                ·
                  refine ⟨23489141046444876707489605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31318854728593168943319473 23489141046444876707489605)
                  ·
                    refine ⟨4404213946208414382654301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23489141046444876707489605 4404213946208414382654301)
                    ·
                      refine ⟨1651580229828155393495363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404213946208414382654301 1651580229828155393495363)
                      ·
                        rfl

theorem cell23_3216441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3216441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216441 prefixEnd_3216441 := by exact prefixLift 3216441
  have htrace : WordTrace (prefixWord ++ tailWord_3216441) baseStart_3216441 baseEnd_3216441 := by
    simpa [prefixWord, tailWord_3216441, baseEnd_3216441] using wordTrace_append hprefix tailTrace_3216441
  have hstable : (prefixWord ++ tailWord_3216441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216441).length < 2 ^ (prefixWord ++ tailWord_3216441).sum := by decide
  have hdescent : baseEnd_3216441 < baseStart_3216441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216455 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_3216455 : Nat := 118140960795 + 3216455 * 2 ^ 59
def prefixEnd_3216455 : Nat := 4983230072969 + 3 ^ 40 * 3216455 * 2
def baseEnd_3216455 : Nat := 1651587418557318338720299

theorem tailTrace_3216455 : CollatzResearch.WordTrace tailWord_3216455 prefixEnd_3216455 1651587418557318338720299 := by
  unfold tailWord_3216455
  simp only [CollatzResearch.WordTrace]
  refine ⟨117313751562340336624970819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78209167708226891083313879 117313751562340336624970819)
  ·
    refine ⟨175970627343510504937456229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117313751562340336624970819 175970627343510504937456229)
    ·
      refine ⟨32994492626908219675773043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175970627343510504937456229 32994492626908219675773043)
      ·
        refine ⟨49491738940362329513659565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32994492626908219675773043 49491738940362329513659565)
        ·
          refine ⟨18559402102635873567622337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49491738940362329513659565 18559402102635873567622337)
          ·
            refine ⟨13919551576976905175716753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18559402102635873567622337 13919551576976905175716753)
            ·
              refine ⟨10439663682732678881787565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13919551576976905175716753 10439663682732678881787565)
              ·
                refine ⟨3914873881024754580670337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10439663682732678881787565 3914873881024754580670337)
                ·
                  refine ⟨2936155410768565935502753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914873881024754580670337 2936155410768565935502753)
                  ·
                    refine ⟨2202116558076424451627065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936155410768565935502753 2202116558076424451627065)
                    ·
                      refine ⟨1651587418557318338720299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202116558076424451627065 1651587418557318338720299)
                      ·
                        rfl

theorem cell23_3216455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_3216455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216455 prefixEnd_3216455 := by exact prefixLift 3216455
  have htrace : WordTrace (prefixWord ++ tailWord_3216455) baseStart_3216455 baseEnd_3216455 := by
    simpa [prefixWord, tailWord_3216455, baseEnd_3216455] using wordTrace_append hprefix tailTrace_3216455
  have hstable : (prefixWord ++ tailWord_3216455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216455).length < 2 ^ (prefixWord ++ tailWord_3216455).sum := by decide
  have hdescent : baseEnd_3216455 < baseStart_3216455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216461 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 9]
def baseStart_3216461 : Nat := 118140960795 + 3216461 * 2 ^ 59
def prefixEnd_3216461 : Nat := 4983230072969 + 3 ^ 40 * 3216461 * 2
def baseEnd_3216461 : Nat := 183510055493471701693919

theorem tailTrace_3216461 : CollatzResearch.WordTrace tailWord_3216461 prefixEnd_3216461 183510055493471701693919 := by
  unfold tailWord_3216461
  simp only [CollatzResearch.WordTrace]
  refine ⟨117313970400318599649689237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78209313600212399766459491 117313970400318599649689237)
  ·
    refine ⟨5499092362514934358579183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117313970400318599649689237 5499092362514934358579183)
    ·
      refine ⟨8248638543772401537868775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499092362514934358579183 8248638543772401537868775)
      ·
        refine ⟨12372957815658602306803163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248638543772401537868775 12372957815658602306803163)
        ·
          refine ⟨18559436723487903460204745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372957815658602306803163 18559436723487903460204745)
          ·
            refine ⟨13919577542615927595153559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18559436723487903460204745 13919577542615927595153559)
            ·
              refine ⟨20879366313923891392730339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919577542615927595153559 20879366313923891392730339)
              ·
                refine ⟨31319049470885837089095509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20879366313923891392730339 31319049470885837089095509)
                ·
                  refine ⟨183510055493471701693919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31319049470885837089095509 183510055493471701693919)
                  ·
                    rfl

theorem cell23_3216461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_3216461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216461 prefixEnd_3216461 := by exact prefixLift 3216461
  have htrace : WordTrace (prefixWord ++ tailWord_3216461) baseStart_3216461 baseEnd_3216461 := by
    simpa [prefixWord, tailWord_3216461, baseEnd_3216461] using wordTrace_append hprefix tailTrace_3216461
  have hstable : (prefixWord ++ tailWord_3216461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216461).length < 2 ^ (prefixWord ++ tailWord_3216461).sum := by decide
  have hdescent : baseEnd_3216461 < baseStart_3216461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216531 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 3]
def baseStart_3216531 : Nat := 118140960795 + 3216531 * 2 ^ 59
def prefixEnd_3216531 : Nat := 4983230072969 + 3 ^ 40 * 3216531 * 2
def baseEnd_3216531 : Nat := 1651626443087060041369949

theorem tailTrace_3216531 : CollatzResearch.WordTrace tailWord_3216531 prefixEnd_3216531 1651626443087060041369949 := by
  unfold tailWord_3216531
  simp only [CollatzResearch.WordTrace]
  refine ⟨117316523510065001604737447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78211015673376667736491631 117316523510065001604737447)
  ·
    refine ⟨175974785265097502407106171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117316523510065001604737447 175974785265097502407106171)
    ·
      refine ⟨263962177897646253610659257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175974785265097502407106171 263962177897646253610659257)
      ·
        refine ⟨197971633423234690207994443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263962177897646253610659257 197971633423234690207994443)
        ·
          refine ⟨296957450134852035311991665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197971633423234690207994443 296957450134852035311991665)
          ·
            refine ⟨222718087601139026483993749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296957450134852035311991665 222718087601139026483993749)
            ·
              refine ⟨10439910356303391866437207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222718087601139026483993749 10439910356303391866437207)
              ·
                refine ⟨15659865534455087799655811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439910356303391866437207 15659865534455087799655811)
                ·
                  refine ⟨23489798301682631699483717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15659865534455087799655811 23489798301682631699483717)
                  ·
                    refine ⟨4404337181565493443653197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23489798301682631699483717 4404337181565493443653197)
                    ·
                      refine ⟨1651626443087060041369949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404337181565493443653197 1651626443087060041369949)
                      ·
                        rfl

theorem cell23_3216531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_3216531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216531 prefixEnd_3216531 := by exact prefixLift 3216531
  have htrace : WordTrace (prefixWord ++ tailWord_3216531) baseStart_3216531 baseEnd_3216531 := by
    simpa [prefixWord, tailWord_3216531, baseEnd_3216531] using wordTrace_append hprefix tailTrace_3216531
  have hstable : (prefixWord ++ tailWord_3216531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216531).length < 2 ^ (prefixWord ++ tailWord_3216531).sum := by decide
  have hdescent : baseEnd_3216531 < baseStart_3216531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216548 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_3216548 : Nat := 118140960795 + 3216548 * 2 ^ 59
def prefixEnd_3216548 : Nat := 4983230072969 + 3 ^ 40 * 3216548 * 2
def baseEnd_3216548 : Nat := 1651635172258186474857371

theorem tailTrace_3216548 : CollatzResearch.WordTrace tailWord_3216548 prefixEnd_3216548 1651635172258186474857371 := by
  unfold tailWord_3216548
  simp only [CollatzResearch.WordTrace]
  refine ⟨58658571775501706754053149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78211429034002275672070865 58658571775501706754053149)
  ·
    refine ⟨21996964415813140032769931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58658571775501706754053149 21996964415813140032769931)
    ·
      refine ⟨32995446623719710049154897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21996964415813140032769931 32995446623719710049154897)
      ·
        refine ⟨24746584967789782536866173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32995446623719710049154897 24746584967789782536866173)
        ·
          refine ⟨9279969362921168451324815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24746584967789782536866173 9279969362921168451324815)
          ·
            refine ⟨13919954044381752676987223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279969362921168451324815 13919954044381752676987223)
            ·
              refine ⟨20879931066572629015480835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919954044381752676987223 20879931066572629015480835)
              ·
                refine ⟨31319896599858943523221253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20879931066572629015480835 31319896599858943523221253)
                ·
                  refine ⟨5872480612473551910603985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31319896599858943523221253 5872480612473551910603985)
                  ·
                    refine ⟨4404360459355163932952989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872480612473551910603985 4404360459355163932952989)
                    ·
                      refine ⟨1651635172258186474857371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404360459355163932952989 1651635172258186474857371)
                      ·
                        rfl

theorem cell23_3216548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_3216548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216548 prefixEnd_3216548 := by exact prefixLift 3216548
  have htrace : WordTrace (prefixWord ++ tailWord_3216548) baseStart_3216548 baseEnd_3216548 := by
    simpa [prefixWord, tailWord_3216548, baseEnd_3216548] using wordTrace_append hprefix tailTrace_3216548
  have hstable : (prefixWord ++ tailWord_3216548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216548).length < 2 ^ (prefixWord ++ tailWord_3216548).sum := by decide
  have hdescent : baseEnd_3216548 < baseStart_3216548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216618 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3216618 : Nat := 118140960795 + 3216618 * 2 ^ 59
def prefixEnd_3216618 : Nat := 4983230072969 + 3 ^ 40 * 3216618 * 2
def baseEnd_3216618 : Nat := 1651671115904001200982049

theorem tailTrace_3216618 : CollatzResearch.WordTrace tailWord_3216618 prefixEnd_3216618 1651671115904001200982049 := by
  unfold tailWord_3216618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29329924165187453865788627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78213131107166543642103005 29329924165187453865788627)
  ·
    refine ⟨43994886247781180798682941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29329924165187453865788627 43994886247781180798682941)
    ·
      refine ⟨16498082342917942799506103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43994886247781180798682941 16498082342917942799506103)
      ·
        refine ⟨24747123514376914199259155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16498082342917942799506103 24747123514376914199259155)
        ·
          refine ⟨37120685271565371298888733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24747123514376914199259155 37120685271565371298888733)
          ·
            refine ⟨13920256976837014237083275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37120685271565371298888733 13920256976837014237083275)
            ·
              refine ⟨20880385465255521355624913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13920256976837014237083275 20880385465255521355624913)
              ·
                refine ⟨15660289098941641016718685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20880385465255521355624913 15660289098941641016718685)
                ·
                  refine ⟨5872608412103115381269507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15660289098941641016718685 5872608412103115381269507)
                  ·
                    refine ⟨8808912618154673071904261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5872608412103115381269507 8808912618154673071904261)
                    ·
                      refine ⟨1651671115904001200982049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8808912618154673071904261 1651671115904001200982049)
                      ·
                        rfl

theorem cell23_3216618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3216618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216618 prefixEnd_3216618 := by exact prefixLift 3216618
  have htrace : WordTrace (prefixWord ++ tailWord_3216618) baseStart_3216618 baseEnd_3216618 := by
    simpa [prefixWord, tailWord_3216618, baseEnd_3216618] using wordTrace_append hprefix tailTrace_3216618
  have hstable : (prefixWord ++ tailWord_3216618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216618).length < 2 ^ (prefixWord ++ tailWord_3216618).sum := by decide
  have hdescent : baseEnd_3216618 < baseStart_3216618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216631 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_3216631 : Nat := 118140960795 + 3216631 * 2 ^ 59
def prefixEnd_3216631 : Nat := 4983230072969 + 3 ^ 40 * 3216631 * 2
def baseEnd_3216631 : Nat := 1651677791152509650119489

theorem tailTrace_3216631 : CollatzResearch.WordTrace tailWord_3216631 prefixEnd_3216631 1651677791152509650119489 := by
  unfold tailWord_3216631
  simp only [CollatzResearch.WordTrace]
  refine ⟨117320170809702718683377747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78213447206468479122251831 117320170809702718683377747)
  ·
    refine ⟨175980256214554078025066621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117320170809702718683377747 175980256214554078025066621)
    ·
      refine ⟨65992596080457779259399983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175980256214554078025066621 65992596080457779259399983)
      ·
        refine ⟨98988894120686668889099975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65992596080457779259399983 98988894120686668889099975)
        ·
          refine ⟨148483341181030003333649963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98988894120686668889099975 148483341181030003333649963)
          ·
            refine ⟨222725011771545005000474945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148483341181030003333649963 222725011771545005000474945)
            ·
              refine ⟨167043758828658753750356209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222725011771545005000474945 167043758828658753750356209)
              ·
                refine ⟨125282819121494065312767157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167043758828658753750356209 125282819121494065312767157)
                ·
                  refine ⟨11745264292640068623071921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125282819121494065312767157 11745264292640068623071921)
                  ·
                    refine ⟨8808948219480051467303941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11745264292640068623071921 8808948219480051467303941)
                    ·
                      refine ⟨1651677791152509650119489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8808948219480051467303941 1651677791152509650119489)
                      ·
                        rfl

theorem cell23_3216631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_3216631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216631 prefixEnd_3216631 := by exact prefixLift 3216631
  have htrace : WordTrace (prefixWord ++ tailWord_3216631) baseStart_3216631 baseEnd_3216631 := by
    simpa [prefixWord, tailWord_3216631, baseEnd_3216631] using wordTrace_append hprefix tailTrace_3216631
  have hstable : (prefixWord ++ tailWord_3216631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216631).length < 2 ^ (prefixWord ++ tailWord_3216631).sum := by decide
  have hdescent : baseEnd_3216631 < baseStart_3216631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216652 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 1, 1, 4]
def baseStart_3216652 : Nat := 118140960795 + 3216652 * 2 ^ 59
def prefixEnd_3216652 : Nat := 4983230072969 + 3 ^ 40 * 3216652 * 2
def baseEnd_3216652 : Nat := 1651688574246254067956893

theorem tailTrace_3216652 : CollatzResearch.WordTrace tailWord_3216652 prefixEnd_3216652 1651688574246254067956893 := by
  unfold tailWord_3216652
  simp only [CollatzResearch.WordTrace]
  refine ⟨58660468371313319634946105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78213957828417759513261473 58660468371313319634946105)
  ·
    refine ⟨43995351278484989726209579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58660468371313319634946105 43995351278484989726209579)
    ·
      refine ⟨65993026917727484589314369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43995351278484989726209579 65993026917727484589314369)
      ·
        refine ⟨49494770188295613441985777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65993026917727484589314369 49494770188295613441985777)
        ·
          refine ⟨37121077641221710081489333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49494770188295613441985777 37121077641221710081489333)
          ·
            refine ⟨3480101028864535320139625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37121077641221710081489333 3480101028864535320139625)
            ·
              refine ⟨2610075771648401490104719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480101028864535320139625 2610075771648401490104719)
              ·
                refine ⟨3915113657472602235157079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610075771648401490104719 3915113657472602235157079)
                ·
                  refine ⟨5872670486208903352735619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915113657472602235157079 5872670486208903352735619)
                  ·
                    refine ⟨8809005729313355029103429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5872670486208903352735619 8809005729313355029103429)
                    ·
                      refine ⟨1651688574246254067956893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8809005729313355029103429 1651688574246254067956893)
                      ·
                        rfl

theorem cell23_3216652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_3216652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216652 prefixEnd_3216652 := by exact prefixLift 3216652
  have htrace : WordTrace (prefixWord ++ tailWord_3216652) baseStart_3216652 baseEnd_3216652 := by
    simpa [prefixWord, tailWord_3216652, baseEnd_3216652] using wordTrace_append hprefix tailTrace_3216652
  have hstable : (prefixWord ++ tailWord_3216652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216652).length < 2 ^ (prefixWord ++ tailWord_3216652).sum := by decide
  have hdescent : baseEnd_3216652 < baseStart_3216652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216661 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3216661 : Nat := 118140960795 + 3216661 * 2 ^ 59
def prefixEnd_3216661 : Nat := 4983230072969 + 3 ^ 40 * 3216661 * 2
def baseEnd_3216661 : Nat := 1651693195572144532744351

theorem tailTrace_3216661 : CollatzResearch.WordTrace tailWord_3216661 prefixEnd_3216661 1651693195572144532744351 := by
  unfold tailWord_3216661
  simp only [CollatzResearch.WordTrace]
  refine ⟨117321264999594033806969837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78214176666396022537979891 117321264999594033806969837)
  ·
    refine ⟨43995474374847762677613689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117321264999594033806969837 43995474374847762677613689)
    ·
      refine ⟨32996605781135822008210267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43995474374847762677613689 32996605781135822008210267)
      ·
        refine ⟨49494908671703733012315401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32996605781135822008210267 49494908671703733012315401)
        ·
          refine ⟨37121181503777799759236551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49494908671703733012315401 37121181503777799759236551)
          ·
            refine ⟨55681772255666699638854827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37121181503777799759236551 55681772255666699638854827)
            ·
              refine ⟨83522658383500049458282241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55681772255666699638854827 83522658383500049458282241)
              ·
                refine ⟨62641993787625037093711681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83522658383500049458282241 62641993787625037093711681)
                ·
                  refine ⟨46981495340718777820283761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62641993787625037093711681 46981495340718777820283761)
                  ·
                    refine ⟨35236121505539083365212821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46981495340718777820283761 35236121505539083365212821)
                    ·
                      refine ⟨1651693195572144532744351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35236121505539083365212821 1651693195572144532744351)
                      ·
                        rfl

theorem cell23_3216661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3216661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216661 prefixEnd_3216661 := by exact prefixLift 3216661
  have htrace : WordTrace (prefixWord ++ tailWord_3216661) baseStart_3216661 baseEnd_3216661 := by
    simpa [prefixWord, tailWord_3216661, baseEnd_3216661] using wordTrace_append hprefix tailTrace_3216661
  have hstable : (prefixWord ++ tailWord_3216661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216661).length < 2 ^ (prefixWord ++ tailWord_3216661).sum := by decide
  have hdescent : baseEnd_3216661 < baseStart_3216661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216668 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_3216668 : Nat := 118140960795 + 3216668 * 2 ^ 59
def prefixEnd_3216668 : Nat := 4983230072969 + 3 ^ 40 * 3216668 * 2
def baseEnd_3216668 : Nat := 1651696789936726005356819

theorem tailTrace_3216668 : CollatzResearch.WordTrace tailWord_3216668 prefixEnd_3216668 1651696789936726005356819 := by
  unfold tailWord_3216668
  simp only [CollatzResearch.WordTrace]
  refine ⟨58660760155284337001237329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78214346873712449334983105 58660760155284337001237329)
  ·
    refine ⟨43995570116463252750927997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58660760155284337001237329 43995570116463252750927997)
    ·
      refine ⟨16498338793673719781597999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43995570116463252750927997 16498338793673719781597999)
      ·
        refine ⟨24747508190510579672396999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16498338793673719781597999 24747508190510579672396999)
        ·
          refine ⟨37121262285765869508595499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24747508190510579672396999 37121262285765869508595499)
          ·
            refine ⟨55681893428648804262893249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37121262285765869508595499 55681893428648804262893249)
            ·
              refine ⟨41761420071486603197169937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55681893428648804262893249 41761420071486603197169937)
              ·
                refine ⟨31321065053614952397877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41761420071486603197169937 31321065053614952397877453)
                ·
                  refine ⟨11745399395105607149204045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31321065053614952397877453 11745399395105607149204045)
                  ·
                    refine ⟨4404524773164602680951517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11745399395105607149204045 4404524773164602680951517)
                    ·
                      refine ⟨1651696789936726005356819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404524773164602680951517 1651696789936726005356819)
                      ·
                        rfl

theorem cell23_3216668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_3216668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216668 prefixEnd_3216668 := by exact prefixLift 3216668
  have htrace : WordTrace (prefixWord ++ tailWord_3216668) baseStart_3216668 baseEnd_3216668 := by
    simpa [prefixWord, tailWord_3216668, baseEnd_3216668] using wordTrace_append hprefix tailTrace_3216668
  have hstable : (prefixWord ++ tailWord_3216668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216668).length < 2 ^ (prefixWord ++ tailWord_3216668).sum := by decide
  have hdescent : baseEnd_3216668 < baseStart_3216668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216669 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3216669 : Nat := 118140960795 + 3216669 * 2 ^ 59
def prefixEnd_3216669 : Nat := 4983230072969 + 3 ^ 40 * 3216669 * 2
def baseEnd_3216669 : Nat := 1651697303417380501444315

theorem tailTrace_3216669 : CollatzResearch.WordTrace tailWord_3216669 prefixEnd_3216669 1651697303417380501444315 := by
  unfold tailWord_3216669
  simp only [CollatzResearch.WordTrace]
  refine ⟨117321556783565051173261061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78214371189043367448840707 117321556783565051173261061)
  ·
    refine ⟨21997791896918447094986449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117321556783565051173261061 21997791896918447094986449)
    ·
      refine ⟨16498343922688835321239837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21997791896918447094986449 16498343922688835321239837)
      ·
        refine ⟨6186878971008313245464939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16498343922688835321239837 6186878971008313245464939)
        ·
          refine ⟨9280318456512469868197409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186878971008313245464939 9280318456512469868197409)
          ·
            refine ⟨6960238842384352401148057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9280318456512469868197409 6960238842384352401148057)
            ·
              refine ⟨5220179131788264300861043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960238842384352401148057 5220179131788264300861043)
              ·
                refine ⟨7830268697682396451291565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220179131788264300861043 7830268697682396451291565)
                ·
                  refine ⟨2936350761630898669234337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7830268697682396451291565 2936350761630898669234337)
                  ·
                    refine ⟨2202263071223174001925753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936350761630898669234337 2202263071223174001925753)
                    ·
                      refine ⟨1651697303417380501444315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202263071223174001925753 1651697303417380501444315)
                      ·
                        rfl

theorem cell23_3216669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3216669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216669 prefixEnd_3216669 := by exact prefixLift 3216669
  have htrace : WordTrace (prefixWord ++ tailWord_3216669) baseStart_3216669 baseEnd_3216669 := by
    simpa [prefixWord, tailWord_3216669, baseEnd_3216669] using wordTrace_append hprefix tailTrace_3216669
  have hstable : (prefixWord ++ tailWord_3216669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216669).length < 2 ^ (prefixWord ++ tailWord_3216669).sum := by decide
  have hdescent : baseEnd_3216669 < baseStart_3216669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216682 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3216682 : Nat := 118140960795 + 3216682 * 2 ^ 59
def prefixEnd_3216682 : Nat := 4983230072969 + 3 ^ 40 * 3216682 * 2
def baseEnd_3216682 : Nat := 1651703978665888950581755

theorem tailTrace_3216682 : CollatzResearch.WordTrace tailWord_3216682 prefixEnd_3216682 1651703978665888950581755 := by
  unfold tailWord_3216682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29330507733129488598371075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78214687288345302928989533 29330507733129488598371075)
  ·
    refine ⟨43995761599694232897556613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29330507733129488598371075 43995761599694232897556613)
    ·
      refine ⟨8249205299942668668291865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43995761599694232897556613 8249205299942668668291865)
      ·
        refine ⟨6186903974957001501218899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8249205299942668668291865 6186903974957001501218899)
        ·
          refine ⟨9280355962435502251828349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186903974957001501218899 9280355962435502251828349)
          ·
            refine ⟨3480133485913313344435631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9280355962435502251828349 3480133485913313344435631)
            ·
              refine ⟨5220200228869970016653447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480133485913313344435631 5220200228869970016653447)
              ·
                refine ⟨7830300343304955024980171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220200228869970016653447 7830300343304955024980171)
                ·
                  refine ⟨11745450514957432537470257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7830300343304955024980171 11745450514957432537470257)
                  ·
                    refine ⟨8809087886218074403102693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11745450514957432537470257 8809087886218074403102693)
                    ·
                      refine ⟨1651703978665888950581755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8809087886218074403102693 1651703978665888950581755)
                      ·
                        rfl

theorem cell23_3216682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3216682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216682 prefixEnd_3216682 := by exact prefixLift 3216682
  have htrace : WordTrace (prefixWord ++ tailWord_3216682) baseStart_3216682 baseEnd_3216682 := by
    simpa [prefixWord, tailWord_3216682, baseEnd_3216682] using wordTrace_append hprefix tailTrace_3216682
  have hstable : (prefixWord ++ tailWord_3216682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216682).length < 2 ^ (prefixWord ++ tailWord_3216682).sum := by decide
  have hdescent : baseEnd_3216682 < baseStart_3216682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216728 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3216728 : Nat := 118140960795 + 3216728 * 2 ^ 59
def prefixEnd_3216728 : Nat := 4983230072969 + 3 ^ 40 * 3216728 * 2
def baseEnd_3216728 : Nat := 1651727598775995770606543

theorem tailTrace_3216728 : CollatzResearch.WordTrace tailWord_3216728 prefixEnd_3216728 1651727598775995770606543 := by
  unfold tailWord_3216728
  simp only [CollatzResearch.WordTrace]
  refine ⟨58661854345175652124829419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78215805793567536166439225 58661854345175652124829419)
  ·
    refine ⟨87992781517763478187244129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58661854345175652124829419 87992781517763478187244129)
    ·
      refine ⟨65994586138322608640433097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87992781517763478187244129 65994586138322608640433097)
      ·
        refine ⟨49495939603741956480324823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65994586138322608640433097 49495939603741956480324823)
        ·
          refine ⟨74243909405612934720487235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49495939603741956480324823 74243909405612934720487235)
          ·
            refine ⟨111365864108419402080730853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74243909405612934720487235 111365864108419402080730853)
            ·
              refine ⟨20881099520328637890137035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111365864108419402080730853 20881099520328637890137035)
              ·
                refine ⟨31321649280492956835205553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20881099520328637890137035 31321649280492956835205553)
                ·
                  refine ⟨23491236960369717626404165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31321649280492956835205553 23491236960369717626404165)
                  ·
                    refine ⟨4404606930069322054950781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23491236960369717626404165 4404606930069322054950781)
                    ·
                      refine ⟨1651727598775995770606543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404606930069322054950781 1651727598775995770606543)
                      ·
                        rfl

theorem cell23_3216728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3216728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216728 prefixEnd_3216728 := by exact prefixLift 3216728
  have htrace : WordTrace (prefixWord ++ tailWord_3216728) baseStart_3216728 baseEnd_3216728 := by
    simpa [prefixWord, tailWord_3216728, baseEnd_3216728] using wordTrace_append hprefix tailTrace_3216728
  have hstable : (prefixWord ++ tailWord_3216728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216728).length < 2 ^ (prefixWord ++ tailWord_3216728).sum := by decide
  have hdescent : baseEnd_3216728 < baseStart_3216728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216746 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3216746 : Nat := 118140960795 + 3216746 * 2 ^ 59
def prefixEnd_3216746 : Nat := 4983230072969 + 3 ^ 40 * 3216746 * 2
def baseEnd_3216746 : Nat := 1651736841427776700181461

theorem tailTrace_3216746 : CollatzResearch.WordTrace tailWord_3216746 prefixEnd_3216746 1651736841427776700181461 := by
  unfold tailWord_3216746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29331091301071523330953523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78216243469524062215876061 29331091301071523330953523)
  ·
    refine ⟨43996636951607284996430285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29331091301071523330953523 43996636951607284996430285)
    ·
      refine ⟨16498738856852731873661357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43996636951607284996430285 16498738856852731873661357)
      ·
        refine ⟨6187027071319774452623009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16498738856852731873661357 6187027071319774452623009)
        ·
          refine ⟨4640270303489830839467257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6187027071319774452623009 4640270303489830839467257)
          ·
            refine ⟨3480202727617373129600443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4640270303489830839467257 3480202727617373129600443)
            ·
              refine ⟨5220304091426059694400665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480202727617373129600443 5220304091426059694400665)
              ·
                refine ⟨3915228068569544770800499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5220304091426059694400665 3915228068569544770800499)
                ·
                  refine ⟨5872842102854317156200749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915228068569544770800499 5872842102854317156200749)
                  ·
                    refine ⟨2202315788570368933575281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5872842102854317156200749 2202315788570368933575281)
                    ·
                      refine ⟨1651736841427776700181461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2202315788570368933575281 1651736841427776700181461)
                      ·
                        rfl

theorem cell23_3216746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3216746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216746 prefixEnd_3216746 := by exact prefixLift 3216746
  have htrace : WordTrace (prefixWord ++ tailWord_3216746) baseStart_3216746 baseEnd_3216746 := by
    simpa [prefixWord, tailWord_3216746, baseEnd_3216746] using wordTrace_append hprefix tailTrace_3216746
  have hstable : (prefixWord ++ tailWord_3216746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216746).length < 2 ^ (prefixWord ++ tailWord_3216746).sum := by decide
  have hdescent : baseEnd_3216746 < baseStart_3216746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216765 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 5]
def baseStart_3216765 : Nat := 118140960795 + 3216765 * 2 ^ 59
def prefixEnd_3216765 : Nat := 4983230072969 + 3 ^ 40 * 3216765 * 2
def baseEnd_3216765 : Nat := 183527399728912458427097

theorem tailTrace_3216765 : CollatzResearch.WordTrace tailWord_3216765 prefixEnd_3216765 183527399728912458427097 := by
  unfold tailWord_3216765
  simp only [CollatzResearch.WordTrace]
  refine ⟨117325058191217259568755749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78216705460811506379170499 117325058191217259568755749)
  ·
    refine ⟨21998448410853236169141703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117325058191217259568755749 21998448410853236169141703)
    ·
      refine ⟨32997672616279854253712555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21998448410853236169141703 32997672616279854253712555)
      ·
        refine ⟨49496508924419781380568833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32997672616279854253712555 49496508924419781380568833)
        ·
          refine ⟨37122381693314836035426625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49496508924419781380568833 37122381693314836035426625)
          ·
            refine ⟨27841786269986127026569969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37122381693314836035426625 27841786269986127026569969)
            ·
              refine ⟨20881339702489595269927477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27841786269986127026569969 20881339702489595269927477)
              ·
                refine ⟨1957625597108399556555701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20881339702489595269927477 1957625597108399556555701)
                ·
                  refine ⟨183527399728912458427097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1957625597108399556555701 183527399728912458427097)
                  ·
                    rfl

theorem cell23_3216765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_3216765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216765 prefixEnd_3216765 := by exact prefixLift 3216765
  have htrace : WordTrace (prefixWord ++ tailWord_3216765) baseStart_3216765 baseEnd_3216765 := by
    simpa [prefixWord, tailWord_3216765, baseEnd_3216765] using wordTrace_append hprefix tailTrace_3216765
  have hstable : (prefixWord ++ tailWord_3216765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216765).length < 2 ^ (prefixWord ++ tailWord_3216765).sum := by decide
  have hdescent : baseEnd_3216765 < baseStart_3216765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216792 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3216792 : Nat := 118140960795 + 3216792 * 2 ^ 59
def prefixEnd_3216792 : Nat := 4983230072969 + 3 ^ 40 * 3216792 * 2
def baseEnd_3216792 : Nat := 1651760461537883520206249

theorem tailTrace_3216792 : CollatzResearch.WordTrace tailWord_3216792 prefixEnd_3216792 1651760461537883520206249 := by
  unfold tailWord_3216792
  simp only [CollatzResearch.WordTrace]
  refine ⟨58663021481059721589994315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78217361974746295453325753 58663021481059721589994315)
  ·
    refine ⟨87994532221589582384991473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58663021481059721589994315 87994532221589582384991473)
    ·
      refine ⟨65995899166192186788743605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87994532221589582384991473 65995899166192186788743605)
      ·
        refine ⟨6187115546830517511444713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65995899166192186788743605 6187115546830517511444713)
        ·
          refine ⟨4640336660122888133583535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6187115546830517511444713 4640336660122888133583535)
          ·
            refine ⟨6960504990184332200375303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640336660122888133583535 6960504990184332200375303)
            ·
              refine ⟨10440757485276498300562955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960504990184332200375303 10440757485276498300562955)
              ·
                refine ⟨15661136227914747450844433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10440757485276498300562955 15661136227914747450844433)
                ·
                  refine ⟨11745852170936060588133325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15661136227914747450844433 11745852170936060588133325)
                  ·
                    refine ⟨4404694564101022720549997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11745852170936060588133325 4404694564101022720549997)
                    ·
                      refine ⟨1651760461537883520206249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4404694564101022720549997 1651760461537883520206249)
                      ·
                        rfl

theorem cell23_3216792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3216792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216792 prefixEnd_3216792 := by exact prefixLift 3216792
  have htrace : WordTrace (prefixWord ++ tailWord_3216792) baseStart_3216792 baseEnd_3216792 := by
    simpa [prefixWord, tailWord_3216792, baseEnd_3216792] using wordTrace_append hprefix tailTrace_3216792
  have hstable : (prefixWord ++ tailWord_3216792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216792).length < 2 ^ (prefixWord ++ tailWord_3216792).sum := by decide
  have hdescent : baseEnd_3216792 < baseStart_3216792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216818 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3216818 : Nat := 118140960795 + 3216818 * 2 ^ 59
def prefixEnd_3216818 : Nat := 4983230072969 + 3 ^ 40 * 3216818 * 2
def baseEnd_3216818 : Nat := 1651773812034900418481129

theorem tailTrace_3216818 : CollatzResearch.WordTrace tailWord_3216818 prefixEnd_3216818 1651773812034900418481129 := by
  unfold tailWord_3216818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29331747815006312405108777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78217994173350166413623405 29331747815006312405108777)
  ·
    refine ⟨21998810861254734303831583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29331747815006312405108777 21998810861254734303831583)
    ·
      refine ⟨32998216291882101455747375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21998810861254734303831583 32998216291882101455747375)
      ·
        refine ⟨49497324437823152183621063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32998216291882101455747375 49497324437823152183621063)
        ·
          refine ⟨74245986656734728275431595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49497324437823152183621063 74245986656734728275431595)
          ·
            refine ⟨111368979985102092413147393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74245986656734728275431595 111368979985102092413147393)
            ·
              refine ⟨83526734988826569309860545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111368979985102092413147393 83526734988826569309860545)
              ·
                refine ⟨62645051241619926982395409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83526734988826569309860545 62645051241619926982395409)
                ·
                  refine ⟨46983788431214945236796557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62645051241619926982395409 46983788431214945236796557)
                  ·
                    refine ⟨17618920661705604463798709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46983788431214945236796557 17618920661705604463798709)
                    ·
                      refine ⟨1651773812034900418481129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17618920661705604463798709 1651773812034900418481129)
                      ·
                        rfl

theorem cell23_3216818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3216818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3216818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3216818 prefixEnd_3216818 := by exact prefixLift 3216818
  have htrace : WordTrace (prefixWord ++ tailWord_3216818) baseStart_3216818 baseEnd_3216818 := by
    simpa [prefixWord, tailWord_3216818, baseEnd_3216818] using wordTrace_append hprefix tailTrace_3216818
  have hstable : (prefixWord ++ tailWord_3216818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216818).length < 2 ^ (prefixWord ++ tailWord_3216818).sum := by decide
  have hdescent : baseEnd_3216818 < baseStart_3216818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
