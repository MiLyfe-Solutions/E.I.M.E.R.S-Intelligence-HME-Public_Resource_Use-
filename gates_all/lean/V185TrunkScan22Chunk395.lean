import V185TrunkScan22Chunk394

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3523970 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3523970 : Nat := 118140960795 + 3523970 * 2 ^ 59
def prefixEnd_3523970 : Nat := 4983230072969 + 3 ^ 40 * 3523970 * 2
def baseEnd_3523970 : Nat := 1206326948016455123245709

theorem tailTrace_3523970 : CollatzResearch.WordTrace tailWord_3523970 prefixEnd_3523970 1206326948016455123245709 := by
  unfold tailWord_3523970
  simp only [CollatzResearch.WordTrace]
  refine ⟨32132436260816502751422341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85686496695510674003792909 32132436260816502751422341)
  ·
    refine ⟨6024831798903094265891689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32132436260816502751422341 6024831798903094265891689)
    ·
      refine ⟨4518623849177320699418767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6024831798903094265891689 4518623849177320699418767)
      ·
        refine ⟨6777935773765981049128151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518623849177320699418767 6777935773765981049128151)
        ·
          refine ⟨10166903660648971573692227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777935773765981049128151 10166903660648971573692227)
          ·
            refine ⟨15250355490973457360538341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10166903660648971573692227 15250355490973457360538341)
            ·
              refine ⟨2859441654557523255100939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15250355490973457360538341 2859441654557523255100939)
              ·
                refine ⟨4289162481836284882651409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859441654557523255100939 4289162481836284882651409)
                ·
                  refine ⟨3216871861377213661988557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289162481836284882651409 3216871861377213661988557)
                  ·
                    refine ⟨1206326948016455123245709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216871861377213661988557 1206326948016455123245709)
                    ·
                      rfl

theorem cell22_3523970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3523970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523970 prefixEnd_3523970 := by exact prefixLift 3523970
  have htrace : WordTrace (prefixWord ++ tailWord_3523970) baseStart_3523970 baseEnd_3523970 := by
    simpa [prefixWord, tailWord_3523970, baseEnd_3523970] using wordTrace_append hprefix tailTrace_3523970
  have hstable : (prefixWord ++ tailWord_3523970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523970).length < 2 ^ (prefixWord ++ tailWord_3523970).sum := by decide
  have hdescent : baseEnd_3523970 < baseStart_3523970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524058 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_3524058 : Nat := 118140960795 + 3524058 * 2 ^ 59
def prefixEnd_3524058 : Nat := 4983230072969 + 3 ^ 40 * 3524058 * 2
def baseEnd_3524058 : Nat := 1206357072214852227045439

theorem tailTrace_3524058 : CollatzResearch.WordTrace tailWord_3524058 prefixEnd_3524058 1206357072214852227045439 := by
  unfold tailWord_3524058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32133238666736800508723207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85688636444631468023261885 32133238666736800508723207)
  ·
    refine ⟨48199858000105200763084811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32133238666736800508723207 48199858000105200763084811)
    ·
      refine ⟨72299787000157801144627217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48199858000105200763084811 72299787000157801144627217)
      ·
        refine ⟨54224840250118350858470413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72299787000157801144627217 54224840250118350858470413)
        ·
          refine ⟨20334315093794381571926405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54224840250118350858470413 20334315093794381571926405)
          ·
            refine ⟨3812684080086446544736201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20334315093794381571926405 3812684080086446544736201)
            ·
              refine ⟨2859513060064834908552151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812684080086446544736201 2859513060064834908552151)
              ·
                refine ⟨4289269590097252362828227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859513060064834908552151 4289269590097252362828227)
                ·
                  refine ⟨6433904385145878544242341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289269590097252362828227 6433904385145878544242341)
                  ·
                    refine ⟨1206357072214852227045439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433904385145878544242341 1206357072214852227045439)
                    ·
                      rfl

theorem cell22_3524058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_3524058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524058 prefixEnd_3524058 := by exact prefixLift 3524058
  have htrace : WordTrace (prefixWord ++ tailWord_3524058) baseStart_3524058 baseEnd_3524058 := by
    simpa [prefixWord, tailWord_3524058, baseEnd_3524058] using wordTrace_append hprefix tailTrace_3524058
  have hstable : (prefixWord ++ tailWord_3524058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524058).length < 2 ^ (prefixWord ++ tailWord_3524058).sum := by decide
  have hdescent : baseEnd_3524058 < baseStart_3524058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524071 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3524071 : Nat := 118140960795 + 3524071 * 2 ^ 59
def prefixEnd_3524071 : Nat := 4983230072969 + 3 ^ 40 * 3524071 * 2
def baseEnd_3524071 : Nat := 1206361522380524526470399

theorem tailTrace_3524071 : CollatzResearch.WordTrace tailWord_3524071 prefixEnd_3524071 1206361522380524526470399 := by
  unfold tailWord_3524071
  simp only [CollatzResearch.WordTrace]
  refine ⟨128533428815900105255116067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85688952543933403503410711 128533428815900105255116067)
  ·
    refine ⟨192800143223850157882674101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128533428815900105255116067 192800143223850157882674101)
    ·
      refine ⟨18075013427235952301500697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192800143223850157882674101 18075013427235952301500697)
      ·
        refine ⟨13556260070426964226125523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18075013427235952301500697 13556260070426964226125523)
        ·
          refine ⟨20334390105640446339188285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13556260070426964226125523 20334390105640446339188285)
          ·
            refine ⟨7625396289615167377195607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20334390105640446339188285 7625396289615167377195607)
            ·
              refine ⟨11438094434422751065793411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625396289615167377195607 11438094434422751065793411)
              ·
                refine ⟨17157141651634126598690117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438094434422751065793411 17157141651634126598690117)
                ·
                  refine ⟨3216964059681398737254397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17157141651634126598690117 3216964059681398737254397)
                  ·
                    refine ⟨1206361522380524526470399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216964059681398737254397 1206361522380524526470399)
                    ·
                      rfl

theorem cell22_3524071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3524071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524071 prefixEnd_3524071 := by exact prefixLift 3524071
  have htrace : WordTrace (prefixWord ++ tailWord_3524071) baseStart_3524071 baseEnd_3524071 := by
    simpa [prefixWord, tailWord_3524071, baseEnd_3524071] using wordTrace_append hprefix tailTrace_3524071
  have hstable : (prefixWord ++ tailWord_3524071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524071).length < 2 ^ (prefixWord ++ tailWord_3524071).sum := by decide
  have hdescent : baseEnd_3524071 < baseStart_3524071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524088 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 2, 3]
def baseStart_3524088 : Nat := 118140960795 + 3524088 * 2 ^ 59
def prefixEnd_3524088 : Nat := 4983230072969 + 3 ^ 40 * 3524088 * 2
def baseEnd_3524088 : Nat := 1206367341827942148795347

theorem tailTrace_3524088 : CollatzResearch.WordTrace tailWord_3524088 prefixEnd_3524088 1206367341827942148795347 := by
  unfold tailWord_3524088
  simp only [CollatzResearch.WordTrace]
  refine ⟨64267024428419258579242459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85689365904559011438989945 64267024428419258579242459)
  ·
    refine ⟨96400536642628887868863689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64267024428419258579242459 96400536642628887868863689)
    ·
      refine ⟨72300402481971665901647767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96400536642628887868863689 72300402481971665901647767)
      ·
        refine ⟨108450603722957498852471651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72300402481971665901647767 108450603722957498852471651)
        ·
          refine ⟨162675905584436248278707477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108450603722957498852471651 162675905584436248278707477)
          ·
            refine ⟨7625433074270449138064413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162675905584436248278707477 7625433074270449138064413)
            ·
              refine ⟨2859537402851418426774155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7625433074270449138064413 2859537402851418426774155)
              ·
                refine ⟨4289306104277127640161233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859537402851418426774155 4289306104277127640161233)
                ·
                  refine ⟨3216979578207845730120925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289306104277127640161233 3216979578207845730120925)
                  ·
                    refine ⟨1206367341827942148795347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216979578207845730120925 1206367341827942148795347)
                    ·
                      rfl

theorem cell22_3524088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_3524088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524088 prefixEnd_3524088 := by exact prefixLift 3524088
  have htrace : WordTrace (prefixWord ++ tailWord_3524088) baseStart_3524088 baseEnd_3524088 := by
    simpa [prefixWord, tailWord_3524088, baseEnd_3524088] using wordTrace_append hprefix tailTrace_3524088
  have hstable : (prefixWord ++ tailWord_3524088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524088).length < 2 ^ (prefixWord ++ tailWord_3524088).sum := by decide
  have hdescent : baseEnd_3524088 < baseStart_3524088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524099 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 5, 3]
def baseStart_3524099 : Nat := 118140960795 + 3524099 * 2 ^ 59
def prefixEnd_3524099 : Nat := 4983230072969 + 3 ^ 40 * 3524099 * 2
def baseEnd_3524099 : Nat := 1206371107352741786770313

theorem tailTrace_3524099 : CollatzResearch.WordTrace tailWord_3524099 prefixEnd_3524099 1206371107352741786770313 := by
  unfold tailWord_3524099
  simp only [CollatzResearch.WordTrace]
  refine ⟨128534450059798666037135351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85689633373199110691423567 128534450059798666037135351)
  ·
    refine ⟨192801675089697999055703027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128534450059798666037135351 192801675089697999055703027)
    ·
      refine ⟨289202512634546998583554541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192801675089697999055703027 289202512634546998583554541)
      ·
        refine ⟨108450942237955124468832953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289202512634546998583554541 108450942237955124468832953)
        ·
          refine ⟨81338206678466343351624715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108450942237955124468832953 81338206678466343351624715)
          ·
            refine ⟨122007310017699515027437073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81338206678466343351624715 122007310017699515027437073)
            ·
              refine ⟨91505482513274636270577805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122007310017699515027437073 91505482513274636270577805)
              ·
                refine ⟨34314555942477988601466677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91505482513274636270577805 34314555942477988601466677)
                ·
                  refine ⟨3216989619607311431387501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34314555942477988601466677 3216989619607311431387501)
                  ·
                    refine ⟨1206371107352741786770313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216989619607311431387501 1206371107352741786770313)
                    ·
                      rfl

theorem cell22_3524099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 3].length) (baseStart_3524099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524099 prefixEnd_3524099 := by exact prefixLift 3524099
  have htrace : WordTrace (prefixWord ++ tailWord_3524099) baseStart_3524099 baseEnd_3524099 := by
    simpa [prefixWord, tailWord_3524099, baseEnd_3524099] using wordTrace_append hprefix tailTrace_3524099
  have hstable : (prefixWord ++ tailWord_3524099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524099).length < 2 ^ (prefixWord ++ tailWord_3524099).sum := by decide
  have hdescent : baseEnd_3524099 < baseStart_3524099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524129 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 7]
def baseStart_3524129 : Nat := 118140960795 + 3524129 * 2 ^ 59
def prefixEnd_3524129 : Nat := 4983230072969 + 3 ^ 40 * 3524129 * 2
def baseEnd_3524129 : Nat := 402127125655277236173407

theorem tailTrace_3524129 : CollatzResearch.WordTrace tailWord_3524129 prefixEnd_3524129 402127125655277236173407 := by
  unfold tailWord_3524129
  simp only [CollatzResearch.WordTrace]
  refine ⟨128535544249689981160727441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85690362833126654107151627 128535544249689981160727441)
  ·
    refine ⟨96401658187267485870545581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128535544249689981160727441 96401658187267485870545581)
    ·
      refine ⟨36150621820225307201454593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96401658187267485870545581 36150621820225307201454593)
      ·
        refine ⟨27112966365168980401090945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36150621820225307201454593 27112966365168980401090945)
        ·
          refine ⟨20334724773876735300818209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27112966365168980401090945 20334724773876735300818209)
          ·
            refine ⟨15251043580407551475613657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20334724773876735300818209 15251043580407551475613657)
            ·
              refine ⟨11438282685305663606710243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15251043580407551475613657 11438282685305663606710243)
              ·
                refine ⟨17157424027958495410065365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438282685305663606710243 17157424027958495410065365)
                ·
                  refine ⟨402127125655277236173407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17157424027958495410065365 402127125655277236173407)
                  ·
                    rfl

theorem cell22_3524129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_3524129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524129 prefixEnd_3524129 := by exact prefixLift 3524129
  have htrace : WordTrace (prefixWord ++ tailWord_3524129) baseStart_3524129 baseEnd_3524129 := by
    simpa [prefixWord, tailWord_3524129, baseEnd_3524129] using wordTrace_append hprefix tailTrace_3524129
  have hstable : (prefixWord ++ tailWord_3524129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524129).length < 2 ^ (prefixWord ++ tailWord_3524129).sum := by decide
  have hdescent : baseEnd_3524129 < baseStart_3524129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524204 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_3524204 : Nat := 118140960795 + 3524204 * 2 ^ 59
def prefixEnd_3524204 : Nat := 4983230072969 + 3 ^ 40 * 3524204 * 2
def baseEnd_3524204 : Nat := 1206407050998556512894991

theorem tailTrace_3524204 : CollatzResearch.WordTrace tailWord_3524204 prefixEnd_3524204 1206407050998556512894991 := by
  unfold tailWord_3524204
  simp only [CollatzResearch.WordTrace]
  refine ⟨64269139862209134484853833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85692186482945512646471777 64269139862209134484853833)
  ·
    refine ⟨48201854896656850863640375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64269139862209134484853833 48201854896656850863640375)
    ·
      refine ⟨72302782344985276295460563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48201854896656850863640375 72302782344985276295460563)
      ·
        refine ⟨108454173517477914443190845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72302782344985276295460563 108454173517477914443190845)
        ·
          refine ⟨40670315069054217916196567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108454173517477914443190845 40670315069054217916196567)
          ·
            refine ⟨61005472603581326874294851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40670315069054217916196567 61005472603581326874294851)
            ·
              refine ⟨91508208905371990311442277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61005472603581326874294851 91508208905371990311442277)
              ·
                refine ⟨17157789169757248183395427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91508208905371990311442277 17157789169757248183395427)
                ·
                  refine ⟨25736683754635872275093141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17157789169757248183395427 25736683754635872275093141)
                  ·
                    refine ⟨1206407050998556512894991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25736683754635872275093141 1206407050998556512894991)
                    ·
                      rfl

theorem cell22_3524204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_3524204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524204 prefixEnd_3524204 := by exact prefixLift 3524204
  have htrace : WordTrace (prefixWord ++ tailWord_3524204) baseStart_3524204 baseEnd_3524204 := by
    simpa [prefixWord, tailWord_3524204, baseEnd_3524204] using wordTrace_append hprefix tailTrace_3524204
  have hstable : (prefixWord ++ tailWord_3524204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524204).length < 2 ^ (prefixWord ++ tailWord_3524204).sum := by decide
  have hdescent : baseEnd_3524204 < baseStart_3524204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524221 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3524221 : Nat := 118140960795 + 3524221 * 2 ^ 59
def prefixEnd_3524221 : Nat := 4983230072969 + 3 ^ 40 * 3524221 * 2
def baseEnd_3524221 : Nat := 1206412870445974135219939

theorem tailTrace_3524221 : CollatzResearch.WordTrace tailWord_3524221 prefixEnd_3524221 1206412870445974135219939 := by
  unfold tailWord_3524221
  simp only [CollatzResearch.WordTrace]
  refine ⟨128538899765356680873076517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85692599843571120582051011 128538899765356680873076517)
  ·
    refine ⟨24101043706004377663701847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128538899765356680873076517 24101043706004377663701847)
    ·
      refine ⟨36151565559006566495552771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24101043706004377663701847 36151565559006566495552771)
      ·
        refine ⟨54227348338509849743329157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36151565559006566495552771 54227348338509849743329157)
        ·
          refine ⟨10167627813470596826874217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54227348338509849743329157 10167627813470596826874217)
          ·
            refine ⟨7625720860102947620155663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10167627813470596826874217 7625720860102947620155663)
            ·
              refine ⟨11438581290154421430233495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625720860102947620155663 11438581290154421430233495)
              ·
                refine ⟨17157871935231632145350243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438581290154421430233495 17157871935231632145350243)
                ·
                  refine ⟨25736807902847448218025365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17157871935231632145350243 25736807902847448218025365)
                  ·
                    refine ⟨1206412870445974135219939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25736807902847448218025365 1206412870445974135219939)
                    ·
                      rfl

theorem cell22_3524221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3524221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524221 prefixEnd_3524221 := by exact prefixLift 3524221
  have htrace : WordTrace (prefixWord ++ tailWord_3524221) baseStart_3524221 baseEnd_3524221 := by
    simpa [prefixWord, tailWord_3524221, baseEnd_3524221] using wordTrace_append hprefix tailTrace_3524221
  have hstable : (prefixWord ++ tailWord_3524221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524221).length < 2 ^ (prefixWord ++ tailWord_3524221).sum := by decide
  have hdescent : baseEnd_3524221 < baseStart_3524221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524249 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_3524249 : Nat := 118140960795 + 3524249 * 2 ^ 59
def prefixEnd_3524249 : Nat := 4983230072969 + 3 ^ 40 * 3524249 * 2
def baseEnd_3524249 : Nat := 1206422455418191395519853

theorem tailTrace_3524249 : CollatzResearch.WordTrace tailWord_3524249 prefixEnd_3524249 1206422455418191395519853 := by
  unfold tailWord_3524249
  simp only [CollatzResearch.WordTrace]
  refine ⟨128539921009255241655095801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85693280672836827770063867 128539921009255241655095801)
  ·
    refine ⟨96404940756941431241321851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128539921009255241655095801 96404940756941431241321851)
    ·
      refine ⟨144607411135412146861982777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96404940756941431241321851 144607411135412146861982777)
      ·
        refine ⟨108455558351559110146487083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144607411135412146861982777 108455558351559110146487083)
        ·
          refine ⟨162683337527338665219730625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108455558351559110146487083 162683337527338665219730625)
          ·
            refine ⟨122012503145503998914797969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162683337527338665219730625 122012503145503998914797969)
            ·
              refine ⟨91509377359127999186098477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122012503145503998914797969 91509377359127999186098477)
              ·
                refine ⟨34316016509672999694786929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91509377359127999186098477 34316016509672999694786929)
                ·
                  refine ⟨25737012382254749771090197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34316016509672999694786929 25737012382254749771090197)
                  ·
                    refine ⟨1206422455418191395519853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25737012382254749771090197 1206422455418191395519853)
                    ·
                      rfl

theorem cell22_3524249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_3524249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524249 prefixEnd_3524249 := by exact prefixLift 3524249
  have htrace : WordTrace (prefixWord ++ tailWord_3524249) baseStart_3524249 baseEnd_3524249 := by
    simpa [prefixWord, tailWord_3524249, baseEnd_3524249] using wordTrace_append hprefix tailTrace_3524249
  have hstable : (prefixWord ++ tailWord_3524249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524249).length < 2 ^ (prefixWord ++ tailWord_3524249).sum := by decide
  have hdescent : baseEnd_3524249 < baseStart_3524249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524302 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3524302 : Nat := 118140960795 + 3524302 * 2 ^ 59
def prefixEnd_3524302 : Nat := 4983230072969 + 3 ^ 40 * 3524302 * 2
def baseEnd_3524302 : Nat := 1206440598401316923944691

theorem tailTrace_3524302 : CollatzResearch.WordTrace tailWord_3524302 prefixEnd_3524302 1206440598401316923944691 := by
  unfold tailWord_3524302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16067731759757903963346895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85694569385375487804516773 16067731759757903963346895)
  ·
    refine ⟨24101597639636855945020343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16067731759757903963346895 24101597639636855945020343)
    ·
      refine ⟨36152396459455283917530515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24101597639636855945020343 36152396459455283917530515)
      ·
        refine ⟨54228594689182925876295773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36152396459455283917530515 54228594689182925876295773)
        ·
          refine ⟨20335723008443597203610915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54228594689182925876295773 20335723008443597203610915)
          ·
            refine ⟨30503584512665395805416373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20335723008443597203610915 30503584512665395805416373)
            ·
              refine ⟨2859711048062380856757785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30503584512665395805416373 2859711048062380856757785)
              ·
                refine ⟨2144783286046785642568339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859711048062380856757785 2144783286046785642568339)
                ·
                  refine ⟨3217174929070178463852509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144783286046785642568339 3217174929070178463852509)
                  ·
                    refine ⟨1206440598401316923944691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217174929070178463852509 1206440598401316923944691)
                    ·
                      rfl

theorem cell22_3524302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3524302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524302 prefixEnd_3524302 := by exact prefixLift 3524302
  have htrace : WordTrace (prefixWord ++ tailWord_3524302) baseStart_3524302 baseEnd_3524302 := by
    simpa [prefixWord, tailWord_3524302, baseEnd_3524302] using wordTrace_append hprefix tailTrace_3524302
  have hstable : (prefixWord ++ tailWord_3524302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524302).length < 2 ^ (prefixWord ++ tailWord_3524302).sum := by decide
  have hdescent : baseEnd_3524302 < baseStart_3524302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524311 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3524311 : Nat := 118140960795 + 3524311 * 2 ^ 59
def prefixEnd_3524311 : Nat := 4983230072969 + 3 ^ 40 * 3524311 * 2
def baseEnd_3524311 : Nat := 1206443679285243900469663

theorem tailTrace_3524311 : CollatzResearch.WordTrace tailWord_3524311 prefixEnd_3524311 1206443679285243900469663 := by
  unfold tailWord_3524311
  simp only [CollatzResearch.WordTrace]
  refine ⟨128542182335030626243852787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85694788223353750829235191 128542182335030626243852787)
  ·
    refine ⟨192813273502545939365779181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128542182335030626243852787 192813273502545939365779181)
    ·
      refine ⟨72304977563454727262167193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192813273502545939365779181 72304977563454727262167193)
      ·
        refine ⟨54228733172591045446625395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72304977563454727262167193 54228733172591045446625395)
        ·
          refine ⟨81343099758886568169938093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54228733172591045446625395 81343099758886568169938093)
          ·
            refine ⟨30503662409582463063726785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81343099758886568169938093 30503662409582463063726785)
            ·
              refine ⟨22877746807186847297795089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30503662409582463063726785 22877746807186847297795089)
              ·
                refine ⟨17158310105390135473346317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22877746807186847297795089 17158310105390135473346317)
                ·
                  refine ⟨6434366289521300802504869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17158310105390135473346317 6434366289521300802504869)
                  ·
                    refine ⟨1206443679285243900469663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6434366289521300802504869 1206443679285243900469663)
                    ·
                      rfl

theorem cell22_3524311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3524311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524311 prefixEnd_3524311 := by exact prefixLift 3524311
  have htrace : WordTrace (prefixWord ++ tailWord_3524311) baseStart_3524311 baseEnd_3524311 := by
    simpa [prefixWord, tailWord_3524311, baseEnd_3524311] using wordTrace_append hprefix tailTrace_3524311
  have hstable : (prefixWord ++ tailWord_3524311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524311).length < 2 ^ (prefixWord ++ tailWord_3524311).sum := by decide
  have hdescent : baseEnd_3524311 < baseStart_3524311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524328 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3524328 : Nat := 118140960795 + 3524328 * 2 ^ 59
def prefixEnd_3524328 : Nat := 4983230072969 + 3 ^ 40 * 3524328 * 2
def baseEnd_3524328 : Nat := 1206449498732661522794611

theorem tailTrace_3524328 : CollatzResearch.WordTrace tailWord_3524328 prefixEnd_3524328 1206449498732661522794611 := by
  unfold tailWord_3524328
  simp only [CollatzResearch.WordTrace]
  refine ⟨64271401187984519073610819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85695201583979358764814425 64271401187984519073610819)
  ·
    refine ⟨96407101781976778610416229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64271401187984519073610819 96407101781976778610416229)
    ·
      refine ⟨18076331584120645989453043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96407101781976778610416229 18076331584120645989453043)
      ·
        refine ⟨27114497376180968984179565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18076331584120645989453043 27114497376180968984179565)
        ·
          refine ⟨10167936516067863369067337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27114497376180968984179565 10167936516067863369067337)
          ·
            refine ⟨7625952387050897526800503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10167936516067863369067337 7625952387050897526800503)
            ·
              refine ⟨11438928580576346290200755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625952387050897526800503 11438928580576346290200755)
              ·
                refine ⟨17158392870864519435301133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438928580576346290200755 17158392870864519435301133)
                ·
                  refine ⟨6434397326574194788237925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17158392870864519435301133 6434397326574194788237925)
                  ·
                    refine ⟨1206449498732661522794611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6434397326574194788237925 1206449498732661522794611)
                    ·
                      rfl

theorem cell22_3524328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3524328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524328 prefixEnd_3524328 := by exact prefixLift 3524328
  have htrace : WordTrace (prefixWord ++ tailWord_3524328) baseStart_3524328 baseEnd_3524328 := by
    simpa [prefixWord, tailWord_3524328, baseEnd_3524328] using wordTrace_append hprefix tailTrace_3524328
  have hstable : (prefixWord ++ tailWord_3524328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524328).length < 2 ^ (prefixWord ++ tailWord_3524328).sum := by decide
  have hdescent : baseEnd_3524328 < baseStart_3524328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524375 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 2, 3]
def baseStart_3524375 : Nat := 118140960795 + 3524375 * 2 ^ 59
def prefixEnd_3524375 : Nat := 4983230072969 + 3 ^ 40 * 3524375 * 2
def baseEnd_3524375 : Nat := 1206465587793169066869467

theorem tailTrace_3524375 : CollatzResearch.WordTrace tailWord_3524375 prefixEnd_3524375 1206465587793169066869467 := by
  unfold tailWord_3524375
  simp only [CollatzResearch.WordTrace]
  refine ⟨128544516606798765174182579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85696344404532510116121719 128544516606798765174182579)
  ·
    refine ⟨192816774910198147761273869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128544516606798765174182579 192816774910198147761273869)
    ·
      refine ⟨72306290591324305410477701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192816774910198147761273869 72306290591324305410477701)
      ·
        refine ⟨13557429485873307264464569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72306290591324305410477701 13557429485873307264464569)
        ·
          refine ⟨10168072114404980448348427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13557429485873307264464569 10168072114404980448348427)
          ·
            refine ⟨15252108171607470672522641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10168072114404980448348427 15252108171607470672522641)
            ·
              refine ⟨11439081128705603004391981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15252108171607470672522641 11439081128705603004391981)
              ·
                refine ⟨4289655423264601126646993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11439081128705603004391981 4289655423264601126646993)
                ·
                  refine ⟨3217241567448450844985245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289655423264601126646993 3217241567448450844985245)
                  ·
                    refine ⟨1206465587793169066869467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217241567448450844985245 1206465587793169066869467)
                    ·
                      rfl

theorem cell22_3524375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_3524375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524375 prefixEnd_3524375 := by exact prefixLift 3524375
  have htrace : WordTrace (prefixWord ++ tailWord_3524375) baseStart_3524375 baseEnd_3524375 := by
    simpa [prefixWord, tailWord_3524375, baseEnd_3524375] using wordTrace_append hprefix tailTrace_3524375
  have hstable : (prefixWord ++ tailWord_3524375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524375).length < 2 ^ (prefixWord ++ tailWord_3524375).sum := by decide
  have hdescent : baseEnd_3524375 < baseStart_3524375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524409 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_3524409 : Nat := 118140960795 + 3524409 * 2 ^ 59
def prefixEnd_3524409 : Nat := 4983230072969 + 3 ^ 40 * 3524409 * 2
def baseEnd_3524409 : Nat := 1206477226688004311519363

theorem tailTrace_3524409 : CollatzResearch.WordTrace tailWord_3524409 prefixEnd_3524409 1206477226688004311519363 := by
  unfold tailWord_3524409
  simp only [CollatzResearch.WordTrace]
  refine ⟨128545756688675588980920281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85697171125783725987280187 128545756688675588980920281)
  ·
    refine ⟨96409317516506691735690211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128545756688675588980920281 96409317516506691735690211)
    ·
      refine ⟨144613976274760037603535317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96409317516506691735690211 144613976274760037603535317)
      ·
        refine ⟨3389390068939688381332859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 144613976274760037603535317 3389390068939688381332859)
        ·
          refine ⟨5084085103409532571999289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389390068939688381332859 5084085103409532571999289)
          ·
            refine ⟨3813063827557149428999467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5084085103409532571999289 3813063827557149428999467)
            ·
              refine ⟨5719595741335724143499201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813063827557149428999467 5719595741335724143499201)
              ·
                refine ⟨4289696806001793107624401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5719595741335724143499201 4289696806001793107624401)
                ·
                  refine ⟨3217272604501344830718301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289696806001793107624401 3217272604501344830718301)
                  ·
                    refine ⟨1206477226688004311519363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217272604501344830718301 1206477226688004311519363)
                    ·
                      rfl

theorem cell22_3524409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_3524409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524409 prefixEnd_3524409 := by exact prefixLift 3524409
  have htrace : WordTrace (prefixWord ++ tailWord_3524409) baseStart_3524409 baseEnd_3524409 := by
    simpa [prefixWord, tailWord_3524409, baseEnd_3524409] using wordTrace_append hprefix tailTrace_3524409
  have hstable : (prefixWord ++ tailWord_3524409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524409).length < 2 ^ (prefixWord ++ tailWord_3524409).sum := by decide
  have hdescent : baseEnd_3524409 < baseStart_3524409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524514 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3524514 : Nat := 118140960795 + 3524514 * 2 ^ 59
def prefixEnd_3524514 : Nat := 4983230072969 + 3 ^ 40 * 3524514 * 2
def baseEnd_3524514 : Nat := 1206513170333819037644041

theorem tailTrace_3524514 : CollatzResearch.WordTrace tailWord_3524514 prefixEnd_3524514 1206513170333819037644041 := by
  unfold tailWord_3524514
  simp only [CollatzResearch.WordTrace]
  refine ⟨32137396588323797978373149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85699724235530127942328397 32137396588323797978373149)
  ·
    refine ⟨12051523720621424241889931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32137396588323797978373149 12051523720621424241889931)
    ·
      refine ⟨18077285580932136362834897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12051523720621424241889931 18077285580932136362834897)
      ·
        refine ⟨13557964185699102272126173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18077285580932136362834897 13557964185699102272126173)
        ·
          refine ⟨5084236569637163352047315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13557964185699102272126173 5084236569637163352047315)
          ·
            refine ⟨7626354854455745028070973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084236569637163352047315 7626354854455745028070973)
            ·
              refine ⟨2859883070420904385526615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7626354854455745028070973 2859883070420904385526615)
              ·
                refine ⟨4289824605631356578289923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859883070420904385526615 4289824605631356578289923)
                ·
                  refine ⟨6434736908447034867434885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289824605631356578289923 6434736908447034867434885)
                  ·
                    refine ⟨1206513170333819037644041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6434736908447034867434885 1206513170333819037644041)
                    ·
                      rfl

theorem cell22_3524514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3524514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524514 prefixEnd_3524514 := by exact prefixLift 3524514
  have htrace : WordTrace (prefixWord ++ tailWord_3524514) baseStart_3524514 baseEnd_3524514 := by
    simpa [prefixWord, tailWord_3524514, baseEnd_3524514] using wordTrace_append hprefix tailTrace_3524514
  have hstable : (prefixWord ++ tailWord_3524514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524514).length < 2 ^ (prefixWord ++ tailWord_3524514).sum := by decide
  have hdescent : baseEnd_3524514 < baseStart_3524514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524529 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 4]
def baseStart_3524529 : Nat := 118140960795 + 3524529 * 2 ^ 59
def prefixEnd_3524529 : Nat := 4983230072969 + 3 ^ 40 * 3524529 * 2
def baseEnd_3524529 : Nat := 402172768380121332839665

theorem tailTrace_3524529 : CollatzResearch.WordTrace tailWord_3524529 prefixEnd_3524529 402172768380121332839665 := by
  unfold tailWord_3524529
  simp only [CollatzResearch.WordTrace]
  refine ⟨128550133448240849475288641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85700088965493899650192427 128550133448240849475288641)
  ·
    refine ⟨96412600086180637106466481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128550133448240849475288641 96412600086180637106466481)
    ·
      refine ⟨72309450064635477829849861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96412600086180637106466481 72309450064635477829849861)
      ·
        refine ⟨13558021887119152093096849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72309450064635477829849861 13558021887119152093096849)
        ·
          refine ⟨10168516415339364069822637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13558021887119152093096849 10168516415339364069822637)
          ·
            refine ⟨3813193655752261526183489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10168516415339364069822637 3813193655752261526183489)
            ·
              refine ⟨2859895241814196144637617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3813193655752261526183489 2859895241814196144637617)
              ·
                refine ⟨2144921431360647108478213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859895241814196144637617 2144921431360647108478213)
                ·
                  refine ⟨402172768380121332839665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144921431360647108478213 402172768380121332839665)
                  ·
                    rfl

theorem cell22_3524529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_3524529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524529 prefixEnd_3524529 := by exact prefixLift 3524529
  have htrace : WordTrace (prefixWord ++ tailWord_3524529) baseStart_3524529 baseEnd_3524529 := by
    simpa [prefixWord, tailWord_3524529, baseEnd_3524529] using wordTrace_append hprefix tailTrace_3524529
  have hstable : (prefixWord ++ tailWord_3524529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524529).length < 2 ^ (prefixWord ++ tailWord_3524529).sum := by decide
  have hdescent : baseEnd_3524529 < baseStart_3524529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524555 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 3, 3]
def baseStart_3524555 : Nat := 118140960795 + 3524555 * 2 ^ 59
def prefixEnd_3524555 : Nat := 4983230072969 + 3 ^ 40 * 3524555 * 2
def baseEnd_3524555 : Nat := 1206527205471708597368915

theorem tailTrace_3524555 : CollatzResearch.WordTrace tailWord_3524555 prefixEnd_3524555 1206527205471708597368915 := by
  unfold tailWord_3524555
  simp only [CollatzResearch.WordTrace]
  refine ⟨128551081746146655915735119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85700721164097770610490079 128551081746146655915735119)
  ·
    refine ⟨192826622619219983873602679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128551081746146655915735119 192826622619219983873602679)
    ·
      refine ⟨289239933928829975810404019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192826622619219983873602679 289239933928829975810404019)
      ·
        refine ⟨433859900893244963715606029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289239933928829975810404019 433859900893244963715606029)
        ·
          refine ⟨162697462834966861393352261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433859900893244963715606029 162697462834966861393352261)
          ·
            refine ⟨30505774281556286511253549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162697462834966861393352261 30505774281556286511253549)
            ·
              refine ⟨11439665355583607441720081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30505774281556286511253549 11439665355583607441720081)
              ·
                refine ⟨8579749016687705581290061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11439665355583607441720081 8579749016687705581290061)
                ·
                  refine ⟨3217405881257889592983773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8579749016687705581290061 3217405881257889592983773)
                  ·
                    refine ⟨1206527205471708597368915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217405881257889592983773 1206527205471708597368915)
                    ·
                      rfl

theorem cell22_3524555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 3].length) (baseStart_3524555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524555 prefixEnd_3524555 := by exact prefixLift 3524555
  have htrace : WordTrace (prefixWord ++ tailWord_3524555) baseStart_3524555 baseEnd_3524555 := by
    simpa [prefixWord, tailWord_3524555, baseEnd_3524555] using wordTrace_append hprefix tailTrace_3524555
  have hstable : (prefixWord ++ tailWord_3524555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524555).length < 2 ^ (prefixWord ++ tailWord_3524555).sum := by decide
  have hdescent : baseEnd_3524555 < baseStart_3524555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524568 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_3524568 : Nat := 118140960795 + 3524568 * 2 ^ 59
def prefixEnd_3524568 : Nat := 4983230072969 + 3 ^ 40 * 3524568 * 2
def baseEnd_3524568 : Nat := 402177218545793632264625

theorem tailTrace_3524568 : CollatzResearch.WordTrace tailWord_3524568 prefixEnd_3524568 402177218545793632264625 := by
  unfold tailWord_3524568
  simp only [CollatzResearch.WordTrace]
  refine ⟨64275777947549779567979179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85701037263399706090638905 64275777947549779567979179)
  ·
    refine ⟨96413666921324669351968769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64275777947549779567979179 96413666921324669351968769)
    ·
      refine ⟨72310250190993502013976577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96413666921324669351968769 72310250190993502013976577)
      ·
        refine ⟨54232687643245126510482433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72310250190993502013976577 54232687643245126510482433)
        ·
          refine ⟨40674515732433844882861825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54232687643245126510482433 40674515732433844882861825)
          ·
            refine ⟨30505886799325383662146369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40674515732433844882861825 30505886799325383662146369)
            ·
              refine ⟨22879415099494037746609777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30505886799325383662146369 22879415099494037746609777)
              ·
                refine ⟨17159561324620528309957333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22879415099494037746609777 17159561324620528309957333)
                ·
                  refine ⟨402177218545793632264625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17159561324620528309957333 402177218545793632264625)
                  ·
                    rfl

theorem cell22_3524568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_3524568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524568 prefixEnd_3524568 := by exact prefixLift 3524568
  have htrace : WordTrace (prefixWord ++ tailWord_3524568) baseStart_3524568 baseEnd_3524568 := by
    simpa [prefixWord, tailWord_3524568, baseEnd_3524568] using wordTrace_append hprefix tailTrace_3524568
  have hstable : (prefixWord ++ tailWord_3524568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524568).length < 2 ^ (prefixWord ++ tailWord_3524568).sum := by decide
  have hdescent : baseEnd_3524568 < baseStart_3524568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524578 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3524578 : Nat := 118140960795 + 3524578 * 2 ^ 59
def prefixEnd_3524578 : Nat := 4983230072969 + 3 ^ 40 * 3524578 * 2
def baseEnd_3524578 : Nat := 1206535078841744204043845

theorem tailTrace_3524578 : CollatzResearch.WordTrace tailWord_3524578 prefixEnd_3524578 1206535078841744204043845 := by
  unfold tailWord_3524578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32137980156265832710955597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85701280416708887229214925 32137980156265832710955597)
  ·
    refine ⟨12051742558599687266608349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32137980156265832710955597 12051742558599687266608349)
    ·
      refine ⟨4519403459474882724978131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12051742558599687266608349 4519403459474882724978131)
      ·
        refine ⟨6779105189212324087467197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519403459474882724978131 6779105189212324087467197)
        ·
          refine ⟨2542164445954621532800199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6779105189212324087467197 2542164445954621532800199)
          ·
            refine ⟨3813246668931932299200299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542164445954621532800199 3813246668931932299200299)
            ·
              refine ⟨5719870003397898448800449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813246668931932299200299 5719870003397898448800449)
              ·
                refine ⟨4289902502548423836600337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5719870003397898448800449 4289902502548423836600337)
                ·
                  refine ⟨3217426876911317877450253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289902502548423836600337 3217426876911317877450253)
                  ·
                    refine ⟨1206535078841744204043845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217426876911317877450253 1206535078841744204043845)
                    ·
                      rfl

theorem cell22_3524578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3524578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524578 prefixEnd_3524578 := by exact prefixLift 3524578
  have htrace : WordTrace (prefixWord ++ tailWord_3524578) baseStart_3524578 baseEnd_3524578 := by
    simpa [prefixWord, tailWord_3524578, baseEnd_3524578] using wordTrace_append hprefix tailTrace_3524578
  have hstable : (prefixWord ++ tailWord_3524578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524578).length < 2 ^ (prefixWord ++ tailWord_3524578).sum := by decide
  have hdescent : baseEnd_3524578 < baseStart_3524578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524662 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3524662 : Nat := 118140960795 + 3524662 * 2 ^ 59
def prefixEnd_3524662 : Nat := 4983230072969 + 3 ^ 40 * 3524662 * 2
def baseEnd_3524662 : Nat := 1206563833758395984943587

theorem tailTrace_3524662 : CollatzResearch.WordTrace tailWord_3524662 prefixEnd_3524662 1206563833758395984943587 := by
  unfold tailWord_3524662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034686522297438324367515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85703322904506008793253493 8034686522297438324367515)
  ·
    refine ⟨12052029783446157486551273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8034686522297438324367515 12052029783446157486551273)
    ·
      refine ⟨9039022337584618114913455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12052029783446157486551273 9039022337584618114913455)
      ·
        refine ⟨13558533506376927172370183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039022337584618114913455 13558533506376927172370183)
        ·
          refine ⟨20337800259565390758555275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13558533506376927172370183 20337800259565390758555275)
          ·
            refine ⟨30506700389348086137832913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20337800259565390758555275 30506700389348086137832913)
            ·
              refine ⟨22880025292011064603374685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30506700389348086137832913 22880025292011064603374685)
              ·
                refine ⟨8580009484504149226265507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22880025292011064603374685 8580009484504149226265507)
                ·
                  refine ⟨12870014226756223839398261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8580009484504149226265507 12870014226756223839398261)
                  ·
                    refine ⟨1206563833758395984943587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12870014226756223839398261 1206563833758395984943587)
                    ·
                      rfl

theorem cell22_3524662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3524662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524662 prefixEnd_3524662 := by exact prefixLift 3524662
  have htrace : WordTrace (prefixWord ++ tailWord_3524662) baseStart_3524662 baseEnd_3524662 := by
    simpa [prefixWord, tailWord_3524662, baseEnd_3524662] using wordTrace_append hprefix tailTrace_3524662
  have hstable : (prefixWord ++ tailWord_3524662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524662).length < 2 ^ (prefixWord ++ tailWord_3524662).sum := by decide
  have hdescent : baseEnd_3524662 < baseStart_3524662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524741 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_3524741 : Nat := 118140960795 + 3524741 * 2 ^ 59
def prefixEnd_3524741 : Nat := 4983230072969 + 3 ^ 40 * 3524741 * 2
def baseEnd_3524741 : Nat := 1206590877072866112218345

theorem tailTrace_3524741 : CollatzResearch.WordTrace tailWord_3524741 prefixEnd_3524741 1206590877072866112218345 := by
  unfold tailWord_3524741
  simp only [CollatzResearch.WordTrace]
  refine ⟨128557865723472809682006077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85705243815648539788004051 128557865723472809682006077)
  ·
    refine ⟨48209199646302303630752279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128557865723472809682006077 48209199646302303630752279)
    ·
      refine ⟨72313799469453455446128419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48209199646302303630752279 72313799469453455446128419)
      ·
        refine ⟨108470699204180183169192629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72313799469453455446128419 108470699204180183169192629)
        ·
          refine ⟨10169128050391892172111809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108470699204180183169192629 10169128050391892172111809)
          ·
            refine ⟨7626846037793919129083857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10169128050391892172111809 7626846037793919129083857)
            ·
              refine ⟨5720134528345439346812893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7626846037793919129083857 5720134528345439346812893)
              ·
                refine ⟨2145050448129539755054835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5720134528345439346812893 2145050448129539755054835)
                ·
                  refine ⟨3217575672194309632582253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145050448129539755054835 3217575672194309632582253)
                  ·
                    refine ⟨1206590877072866112218345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217575672194309632582253 1206590877072866112218345)
                    ·
                      rfl

theorem cell22_3524741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_3524741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524741 prefixEnd_3524741 := by exact prefixLift 3524741
  have htrace : WordTrace (prefixWord ++ tailWord_3524741) baseStart_3524741 baseEnd_3524741 := by
    simpa [prefixWord, tailWord_3524741, baseEnd_3524741] using wordTrace_append hprefix tailTrace_3524741
  have hstable : (prefixWord ++ tailWord_3524741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524741).length < 2 ^ (prefixWord ++ tailWord_3524741).sum := by decide
  have hdescent : baseEnd_3524741 < baseStart_3524741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524795 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_3524795 : Nat := 118140960795 + 3524795 * 2 ^ 59
def prefixEnd_3524795 : Nat := 4983230072969 + 3 ^ 40 * 3524795 * 2
def baseEnd_3524795 : Nat := 1206609362376427971368179

theorem tailTrace_3524795 : CollatzResearch.WordTrace tailWord_3524795 prefixEnd_3524795 1206609362376427971368179 := by
  unfold tailWord_3524795
  simp only [CollatzResearch.WordTrace]
  refine ⟨128559835265277176904471839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85706556843518117936314559 128559835265277176904471839)
  ·
    refine ⟨192839752897915765356707759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128559835265277176904471839 192839752897915765356707759)
    ·
      refine ⟨289259629346873648035061639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192839752897915765356707759 289259629346873648035061639)
      ·
        refine ⟨433889444020310472052592459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289259629346873648035061639 433889444020310472052592459)
        ·
          refine ⟨650834166030465708078888689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433889444020310472052592459 650834166030465708078888689)
          ·
            refine ⟨488125624522849281059166517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650834166030465708078888689 488125624522849281059166517)
            ·
              refine ⟨45761777299017120099296861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 488125624522849281059166517 45761777299017120099296861)
              ·
                refine ⟨17160666487131420037236323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45761777299017120099296861 17160666487131420037236323)
                ·
                  refine ⟨25740999730697130055854485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17160666487131420037236323 25740999730697130055854485)
                  ·
                    refine ⟨1206609362376427971368179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25740999730697130055854485 1206609362376427971368179)
                    ·
                      rfl

theorem cell22_3524795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_3524795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524795 prefixEnd_3524795 := by exact prefixLift 3524795
  have htrace : WordTrace (prefixWord ++ tailWord_3524795) baseStart_3524795 baseEnd_3524795 := by
    simpa [prefixWord, tailWord_3524795, baseEnd_3524795] using wordTrace_append hprefix tailTrace_3524795
  have hstable : (prefixWord ++ tailWord_3524795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524795).length < 2 ^ (prefixWord ++ tailWord_3524795).sum := by decide
  have hdescent : baseEnd_3524795 < baseStart_3524795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524814 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_3524814 : Nat := 118140960795 + 3524814 * 2 ^ 59
def prefixEnd_3524814 : Nat := 4983230072969 + 3 ^ 40 * 3524814 * 2
def baseEnd_3524814 : Nat := 1206615866464718255143121

theorem tailTrace_3524814 : CollatzResearch.WordTrace tailWord_3524814 prefixEnd_3524814 1206615866464718255143121 := by
  unfold tailWord_3524814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16070066031526042893676687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85707018834805562099608997 16070066031526042893676687)
  ·
    refine ⟨24105099047289064340515031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16070066031526042893676687 24105099047289064340515031)
    ·
      refine ⟨36157648570933596510772547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24105099047289064340515031 36157648570933596510772547)
      ·
        refine ⟨54236472856400394766158821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36157648570933596510772547 54236472856400394766158821)
        ·
          refine ⟨10169338660575074018654779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54236472856400394766158821 10169338660575074018654779)
          ·
            refine ⟨15254007990862611027982169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169338660575074018654779 15254007990862611027982169)
            ·
              refine ⟨11440505993146958270986627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15254007990862611027982169 11440505993146958270986627)
              ·
                refine ⟨17160758989720437406479941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440505993146958270986627 17160758989720437406479941)
                ·
                  refine ⟨3217642310572582013714989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17160758989720437406479941 3217642310572582013714989)
                  ·
                    refine ⟨1206615866464718255143121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217642310572582013714989 1206615866464718255143121)
                    ·
                      rfl

theorem cell22_3524814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_3524814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524814 prefixEnd_3524814 := by exact prefixLift 3524814
  have htrace : WordTrace (prefixWord ++ tailWord_3524814) baseStart_3524814 baseEnd_3524814 := by
    simpa [prefixWord, tailWord_3524814, baseEnd_3524814] using wordTrace_append hprefix tailTrace_3524814
  have hstable : (prefixWord ++ tailWord_3524814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524814).length < 2 ^ (prefixWord ++ tailWord_3524814).sum := by decide
  have hdescent : baseEnd_3524814 < baseStart_3524814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524876 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_3524876 : Nat := 118140960795 + 3524876 * 2 ^ 59
def prefixEnd_3524876 : Nat := 4983230072969 + 3 ^ 40 * 3524876 * 2
def baseEnd_3524876 : Nat := 1206637090331770760092931

theorem tailTrace_3524876 : CollatzResearch.WordTrace tailWord_3524876 prefixEnd_3524876 1206637090331770760092931 := by
  unfold tailWord_3524876
  simp only [CollatzResearch.WordTrace]
  refine ⟨64281394788991863869085241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85708526385322485158780321 64281394788991863869085241)
  ·
    refine ⟨48211046091743897901813931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64281394788991863869085241 48211046091743897901813931)
    ·
      refine ⟨72316569137615846852720897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48211046091743897901813931 72316569137615846852720897)
      ·
        refine ⟨54237426853211885139540673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72316569137615846852720897 54237426853211885139540673)
        ·
          refine ⟨40678070139908913854655505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54237426853211885139540673 40678070139908913854655505)
          ·
            refine ⟨30508552604931685390991629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40678070139908913854655505 30508552604931685390991629)
            ·
              refine ⟨11440707226849382021621861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30508552604931685390991629 11440707226849382021621861)
              ·
                refine ⟨2145132605034259129054099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11440707226849382021621861 2145132605034259129054099)
                ·
                  refine ⟨3217698907551388693581149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145132605034259129054099 3217698907551388693581149)
                  ·
                    refine ⟨1206637090331770760092931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217698907551388693581149 1206637090331770760092931)
                    ·
                      rfl

theorem cell22_3524876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_3524876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524876 prefixEnd_3524876 := by exact prefixLift 3524876
  have htrace : WordTrace (prefixWord ++ tailWord_3524876) baseStart_3524876 baseEnd_3524876 := by
    simpa [prefixWord, tailWord_3524876, baseEnd_3524876] using wordTrace_append hprefix tailTrace_3524876
  have hstable : (prefixWord ++ tailWord_3524876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524876).length < 2 ^ (prefixWord ++ tailWord_3524876).sum := by decide
  have hdescent : baseEnd_3524876 < baseStart_3524876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524887 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3524887 : Nat := 118140960795 + 3524887 * 2 ^ 59
def prefixEnd_3524887 : Nat := 4983230072969 + 3 ^ 40 * 3524887 * 2
def baseEnd_3524887 : Nat := 1206640855856570398067897

theorem tailTrace_3524887 : CollatzResearch.WordTrace tailWord_3524887 prefixEnd_3524887 1206640855856570398067897 := by
  unfold tailWord_3524887
  simp only [CollatzResearch.WordTrace]
  refine ⟨128563190780943876616820915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85708793853962584411213943 128563190780943876616820915)
  ·
    refine ⟨192844786171415814925231373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128563190780943876616820915 192844786171415814925231373)
    ·
      refine ⟨72316794814280930596961765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192844786171415814925231373 72316794814280930596961765)
      ·
        refine ⟨13559399027677674486930331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72316794814280930596961765 13559399027677674486930331)
        ·
          refine ⟨20339098541516511730395497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13559399027677674486930331 20339098541516511730395497)
          ·
            refine ⟨15254323906137383797796623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20339098541516511730395497 15254323906137383797796623)
            ·
              refine ⟨22881485859206075696694935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15254323906137383797796623 22881485859206075696694935)
              ·
                refine ⟨34322228788809113545042403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22881485859206075696694935 34322228788809113545042403)
                ·
                  refine ⟨51483343183213670317563605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34322228788809113545042403 51483343183213670317563605)
                  ·
                    refine ⟨1206640855856570398067897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51483343183213670317563605 1206640855856570398067897)
                    ·
                      rfl

theorem cell22_3524887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3524887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524887 prefixEnd_3524887 := by exact prefixLift 3524887
  have htrace : WordTrace (prefixWord ++ tailWord_3524887) baseStart_3524887 baseEnd_3524887 := by
    simpa [prefixWord, tailWord_3524887, baseEnd_3524887] using wordTrace_append hprefix tailTrace_3524887
  have hstable : (prefixWord ++ tailWord_3524887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524887).length < 2 ^ (prefixWord ++ tailWord_3524887).sum := by decide
  have hdescent : baseEnd_3524887 < baseStart_3524887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524917 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 8]
def baseStart_3524917 : Nat := 118140960795 + 3524917 * 2 ^ 59
def prefixEnd_3524917 : Nat := 4983230072969 + 3 ^ 40 * 3524917 * 2
def baseEnd_3524917 : Nat := 402217041823220106605935

theorem tailTrace_3524917 : CollatzResearch.WordTrace tailWord_3524917 prefixEnd_3524917 402217041823220106605935 := by
  unfold tailWord_3524917
  simp only [CollatzResearch.WordTrace]
  refine ⟨128564284970835191740413005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85709523313890127826942003 128564284970835191740413005)
  ·
    refine ⟨48211606864063196902654877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128564284970835191740413005 48211606864063196902654877)
    ·
      refine ⟨18079352574023698838495579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48211606864063196902654877 18079352574023698838495579)
      ·
        refine ⟨27119028861035548257743369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18079352574023698838495579 27119028861035548257743369)
        ·
          refine ⟨20339271645776661193307527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27119028861035548257743369 20339271645776661193307527)
          ·
            refine ⟨30508907468664991789961291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20339271645776661193307527 30508907468664991789961291)
            ·
              refine ⟨45763361202997487684941937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30508907468664991789961291 45763361202997487684941937)
              ·
                refine ⟨34322520902248115763706453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45763361202997487684941937 34322520902248115763706453)
                ·
                  refine ⟨402217041823220106605935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34322520902248115763706453 402217041823220106605935)
                  ·
                    rfl

theorem cell22_3524917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_3524917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524917 prefixEnd_3524917 := by exact prefixLift 3524917
  have htrace : WordTrace (prefixWord ++ tailWord_3524917) baseStart_3524917 baseEnd_3524917 := by
    simpa [prefixWord, tailWord_3524917, baseEnd_3524917] using wordTrace_append hprefix tailTrace_3524917
  have hstable : (prefixWord ++ tailWord_3524917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524917).length < 2 ^ (prefixWord ++ tailWord_3524917).sum := by decide
  have hdescent : baseEnd_3524917 < baseStart_3524917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524947 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 6, 4]
def baseStart_3524947 : Nat := 118140960795 + 3524947 * 2 ^ 59
def prefixEnd_3524947 : Nat := 4983230072969 + 3 ^ 40 * 3524947 * 2
def baseEnd_3524947 : Nat := 1206661395082750241567713

theorem tailTrace_3524947 : CollatzResearch.WordTrace tailWord_3524947 prefixEnd_3524947 1206661395082750241567713 := by
  unfold tailWord_3524947
  simp only [CollatzResearch.WordTrace]
  refine ⟨128565379160726506864005095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85710252773817671242670063 128565379160726506864005095)
  ·
    refine ⟨192848068741089760296007643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128565379160726506864005095 192848068741089760296007643)
    ·
      refine ⟨289272103111634640444011465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192848068741089760296007643 289272103111634640444011465)
      ·
        refine ⟨216954077333725980333008599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289272103111634640444011465 216954077333725980333008599)
        ·
          refine ⟨325431116000588970499512899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216954077333725980333008599 325431116000588970499512899)
          ·
            refine ⟨488146674000883455749269349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325431116000588970499512899 488146674000883455749269349)
            ·
              refine ⟨91527501375165647952988003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 488146674000883455749269349 91527501375165647952988003)
              ·
                refine ⟨137291252062748471929482005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91527501375165647952988003 137291252062748471929482005)
                ·
                  refine ⟨6435527440441334621694469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137291252062748471929482005 6435527440441334621694469)
                  ·
                    refine ⟨1206661395082750241567713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435527440441334621694469 1206661395082750241567713)
                    ·
                      rfl

theorem cell22_3524947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_3524947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524947 prefixEnd_3524947 := by exact prefixLift 3524947
  have htrace : WordTrace (prefixWord ++ tailWord_3524947) baseStart_3524947 baseEnd_3524947 := by
    simpa [prefixWord, tailWord_3524947, baseEnd_3524947] using wordTrace_append hprefix tailTrace_3524947
  have hstable : (prefixWord ++ tailWord_3524947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524947).length < 2 ^ (prefixWord ++ tailWord_3524947).sum := by decide
  have hdescent : baseEnd_3524947 < baseStart_3524947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524964 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_3524964 : Nat := 118140960795 + 3524964 * 2 ^ 59
def prefixEnd_3524964 : Nat := 4983230072969 + 3 ^ 40 * 3524964 * 2
def baseEnd_3524964 : Nat := 1206667214530167863892661

theorem tailTrace_3524964 : CollatzResearch.WordTrace tailWord_3524964 prefixEnd_3524964 1206667214530167863892661 := by
  unfold tailWord_3524964
  simp only [CollatzResearch.WordTrace]
  refine ⟨64282999600832459383686973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85710666134443279178249297 64282999600832459383686973)
  ·
    refine ⟨24106124850312172268882615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64282999600832459383686973 24106124850312172268882615)
    ·
      refine ⟨36159187275468258403323923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24106124850312172268882615 36159187275468258403323923)
      ·
        refine ⟨54238780913202387604985885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36159187275468258403323923 54238780913202387604985885)
        ·
          refine ⟨20339542842450895351869707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54238780913202387604985885 20339542842450895351869707)
          ·
            refine ⟨30509314263676343027804561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20339542842450895351869707 30509314263676343027804561)
            ·
              refine ⟨22881985697757257270853421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30509314263676343027804561 22881985697757257270853421)
              ·
                refine ⟨8580744636658971476570033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22881985697757257270853421 8580744636658971476570033)
                ·
                  refine ⟨6435558477494228607427525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8580744636658971476570033 6435558477494228607427525)
                  ·
                    refine ⟨1206667214530167863892661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435558477494228607427525 1206667214530167863892661)
                    ·
                      rfl

theorem cell22_3524964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_3524964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524964 prefixEnd_3524964 := by exact prefixLift 3524964
  have htrace : WordTrace (prefixWord ++ tailWord_3524964) baseStart_3524964 baseEnd_3524964 := by
    simpa [prefixWord, tailWord_3524964, baseEnd_3524964] using wordTrace_append hprefix tailTrace_3524964
  have hstable : (prefixWord ++ tailWord_3524964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524964).length < 2 ^ (prefixWord ++ tailWord_3524964).sum := by decide
  have hdescent : baseEnd_3524964 < baseStart_3524964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524968 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 4]
def baseStart_3524968 : Nat := 118140960795 + 3524968 * 2 ^ 59
def prefixEnd_3524968 : Nat := 4983230072969 + 3 ^ 40 * 3524968 * 2
def baseEnd_3524968 : Nat := 402222861270637728930883

theorem tailTrace_3524968 : CollatzResearch.WordTrace tailWord_3524968 prefixEnd_3524968 402222861270637728930883 := by
  unfold tailWord_3524968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64283072546825213725259779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85710763395766951633679705 64283072546825213725259779)
  ·
    refine ⟨96424608820237820587889669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64283072546825213725259779 96424608820237820587889669)
    ·
      refine ⟨18079614153794591360229313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96424608820237820587889669 18079614153794591360229313)
      ·
        refine ⟨13559710615345943520171985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18079614153794591360229313 13559710615345943520171985)
        ·
          refine ⟨10169782961509457640128989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13559710615345943520171985 10169782961509457640128989)
          ·
            refine ⟨3813668610566046615048371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10169782961509457640128989 3813668610566046615048371)
            ·
              refine ⟨5720502915849069922572557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813668610566046615048371 5720502915849069922572557)
              ·
                refine ⟨2145188593443401220964709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5720502915849069922572557 2145188593443401220964709)
                ·
                  refine ⟨402222861270637728930883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2145188593443401220964709 402222861270637728930883)
                  ·
                    rfl

theorem cell22_3524968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_3524968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524968 prefixEnd_3524968 := by exact prefixLift 3524968
  have htrace : WordTrace (prefixWord ++ tailWord_3524968) baseStart_3524968 baseEnd_3524968 := by
    simpa [prefixWord, tailWord_3524968, baseEnd_3524968] using wordTrace_append hprefix tailTrace_3524968
  have hstable : (prefixWord ++ tailWord_3524968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524968).length < 2 ^ (prefixWord ++ tailWord_3524968).sum := by decide
  have hdescent : baseEnd_3524968 < baseStart_3524968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524981 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3524981 : Nat := 118140960795 + 3524981 * 2 ^ 59
def prefixEnd_3524981 : Nat := 4983230072969 + 3 ^ 40 * 3524981 * 2
def baseEnd_3524981 : Nat := 1206673033977585486217609

theorem tailTrace_3524981 : CollatzResearch.WordTrace tailWord_3524981 prefixEnd_3524981 1206673033977585486217609 := by
  unfold tailWord_3524981
  simp only [CollatzResearch.WordTrace]
  refine ⟨128566619242603330670742797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85711079495068887113828531 128566619242603330670742797)
  ·
    refine ⟨48212482215976249001528549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128566619242603330670742797 48212482215976249001528549)
    ·
      refine ⟨9039840415495546687786603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48212482215976249001528549 9039840415495546687786603)
      ·
        refine ⟨13559760623243320031679905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039840415495546687786603 13559760623243320031679905)
        ·
          refine ⟨10169820467432490023759929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13559760623243320031679905 10169820467432490023759929)
          ·
            refine ⟨7627365350574367517819947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10169820467432490023759929 7627365350574367517819947)
            ·
              refine ⟨11441048025861551276729921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7627365350574367517819947 11441048025861551276729921)
              ·
                refine ⟨8580786019396163457547441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11441048025861551276729921 8580786019396163457547441)
                ·
                  refine ⟨6435589514547122593160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8580786019396163457547441 6435589514547122593160581)
                  ·
                    refine ⟨1206673033977585486217609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435589514547122593160581 1206673033977585486217609)
                    ·
                      rfl

theorem cell22_3524981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3524981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3524981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3524981 prefixEnd_3524981 := by exact prefixLift 3524981
  have htrace : WordTrace (prefixWord ++ tailWord_3524981) baseStart_3524981 baseEnd_3524981 := by
    simpa [prefixWord, tailWord_3524981, baseEnd_3524981] using wordTrace_append hprefix tailTrace_3524981
  have hstable : (prefixWord ++ tailWord_3524981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524981).length < 2 ^ (prefixWord ++ tailWord_3524981).sum := by decide
  have hdescent : baseEnd_3524981 < baseStart_3524981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525041 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 5]
def baseStart_3525041 : Nat := 118140960795 + 3525041 * 2 ^ 59
def prefixEnd_3525041 : Nat := 4983230072969 + 3 ^ 40 * 3525041 * 2
def baseEnd_3525041 : Nat := 402231191067921776572475

theorem tailTrace_3525041 : CollatzResearch.WordTrace tailWord_3525041 prefixEnd_3525041 402231191067921776572475 := by
  unfold tailWord_3525041
  simp only [CollatzResearch.WordTrace]
  refine ⟨128568807622385960917926977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85712538414923973945284651 128568807622385960917926977)
  ·
    refine ⟨96426605716789470688445233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128568807622385960917926977 96426605716789470688445233)
    ·
      refine ⟨72319954287592103016333925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96426605716789470688445233 72319954287592103016333925)
      ·
        refine ⟨13559991428923519315562611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72319954287592103016333925 13559991428923519315562611)
        ·
          refine ⟨20339987143385278973343917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13559991428923519315562611 20339987143385278973343917)
          ·
            refine ⟨7627495178769479615003969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20339987143385278973343917 7627495178769479615003969)
            ·
              refine ⟨5720621384077109711252977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627495178769479615003969 5720621384077109711252977)
              ·
                refine ⟨4290466038057832283439733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720621384077109711252977 4290466038057832283439733)
                ·
                  refine ⟨402231191067921776572475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4290466038057832283439733 402231191067921776572475)
                  ·
                    rfl

theorem cell22_3525041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_3525041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525041 prefixEnd_3525041 := by exact prefixLift 3525041
  have htrace : WordTrace (prefixWord ++ tailWord_3525041) baseStart_3525041 baseEnd_3525041 := by
    simpa [prefixWord, tailWord_3525041, baseEnd_3525041] using wordTrace_append hprefix tailTrace_3525041
  have hstable : (prefixWord ++ tailWord_3525041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525041).length < 2 ^ (prefixWord ++ tailWord_3525041).sum := by decide
  have hdescent : baseEnd_3525041 < baseStart_3525041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525045 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3525045 : Nat := 118140960795 + 3525045 * 2 ^ 59
def prefixEnd_3525045 : Nat := 4983230072969 + 3 ^ 40 * 3525045 * 2
def baseEnd_3525045 : Nat := 1206694942485510652617413

theorem tailTrace_3525045 : CollatzResearch.WordTrace tailWord_3525045 prefixEnd_3525045 1206694942485510652617413 := by
  unfold tailWord_3525045
  simp only [CollatzResearch.WordTrace]
  refine ⟨128568953514371469601072589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85712635676247646400715059 128568953514371469601072589)
  ·
    refine ⟨48213357567889301100402221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128568953514371469601072589 48213357567889301100402221)
    ·
      refine ⟨18080009087958487912650833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48213357567889301100402221 18080009087958487912650833)
      ·
        refine ⟨13560006815968865934488125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18080009087958487912650833 13560006815968865934488125)
        ·
          refine ⟨5085002555988324725433047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13560006815968865934488125 5085002555988324725433047)
          ·
            refine ⟨7627503833982487088149571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085002555988324725433047 7627503833982487088149571)
            ·
              refine ⟨11441255750973730632224357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7627503833982487088149571 11441255750973730632224357)
              ·
                refine ⟨2145235453307574493542067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11441255750973730632224357 2145235453307574493542067)
                ·
                  refine ⟨3217853179961361740313101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145235453307574493542067 3217853179961361740313101)
                  ·
                    refine ⟨1206694942485510652617413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217853179961361740313101 1206694942485510652617413)
                    ·
                      rfl

theorem cell22_3525045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3525045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525045 prefixEnd_3525045 := by exact prefixLift 3525045
  have htrace : WordTrace (prefixWord ++ tailWord_3525045) baseStart_3525045 baseEnd_3525045 := by
    simpa [prefixWord, tailWord_3525045, baseEnd_3525045] using wordTrace_append hprefix tailTrace_3525045
  have hstable : (prefixWord ++ tailWord_3525045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525045).length < 2 ^ (prefixWord ++ tailWord_3525045).sum := by decide
  have hdescent : baseEnd_3525045 < baseStart_3525045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525099 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 4, 4]
def baseStart_3525099 : Nat := 118140960795 + 3525099 * 2 ^ 59
def prefixEnd_3525099 : Nat := 4983230072969 + 3 ^ 40 * 3525099 * 2
def baseEnd_3525099 : Nat := 1206713427789072511767247

theorem tailTrace_3525099 : CollatzResearch.WordTrace tailWord_3525099 prefixEnd_3525099 1206713427789072511767247 := by
  unfold tailWord_3525099
  simp only [CollatzResearch.WordTrace]
  refine ⟨128570923056175836823538351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85713948704117224549025567 128570923056175836823538351)
  ·
    refine ⟨192856384584263755235307527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128570923056175836823538351 192856384584263755235307527)
    ·
      refine ⟨289284576876395632852961291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192856384584263755235307527 289284576876395632852961291)
      ·
        refine ⟨433926865314593449279441937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289284576876395632852961291 433926865314593449279441937)
        ·
          refine ⟨325445148985945086959581453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433926865314593449279441937 325445148985945086959581453)
          ·
            refine ⟨122041930869729407609843045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325445148985945086959581453 122041930869729407609843045)
            ·
              refine ⟨22882862038074263926845571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122041930869729407609843045 22882862038074263926845571)
              ·
                refine ⟨34324293057111395890268357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22882862038074263926845571 34324293057111395890268357)
                ·
                  refine ⟨6435804948208386729425317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34324293057111395890268357 6435804948208386729425317)
                  ·
                    refine ⟨1206713427789072511767247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435804948208386729425317 1206713427789072511767247)
                    ·
                      rfl

theorem cell22_3525099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_3525099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525099 prefixEnd_3525099 := by exact prefixLift 3525099
  have htrace : WordTrace (prefixWord ++ tailWord_3525099) baseStart_3525099 baseEnd_3525099 := by
    simpa [prefixWord, tailWord_3525099, baseEnd_3525099] using wordTrace_append hprefix tailTrace_3525099
  have hstable : (prefixWord ++ tailWord_3525099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525099).length < 2 ^ (prefixWord ++ tailWord_3525099).sum := by decide
  have hdescent : baseEnd_3525099 < baseStart_3525099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525131 : List Nat := [1, 1, 1, 1, 7, 1, 4, 6]
def baseStart_3525131 : Nat := 118140960795 + 3525131 * 2 ^ 59
def prefixEnd_3525131 : Nat := 4983230072969 + 3 ^ 40 * 3525131 * 2
def baseEnd_3525131 : Nat := 134080486893670566107461

theorem tailTrace_3525131 : CollatzResearch.WordTrace tailWord_3525131 prefixEnd_3525131 134080486893670566107461 := by
  unfold tailWord_3525131
  simp only [CollatzResearch.WordTrace]
  refine ⟨128572090192059906288703247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85714726794706604192468831 128572090192059906288703247)
  ·
    refine ⟨192858135288089859433054871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128572090192059906288703247 192858135288089859433054871)
    ·
      refine ⟨289287202932134789149582307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192858135288089859433054871 289287202932134789149582307)
      ·
        refine ⟨433930804398202183724373461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289287202932134789149582307 433930804398202183724373461)
        ·
          refine ⟨10170253228082863681040003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 433930804398202183724373461 10170253228082863681040003)
          ·
            refine ⟨15255379842124295521560005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170253228082863681040003 15255379842124295521560005)
            ·
              refine ⟨2860383720398305410292501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15255379842124295521560005 2860383720398305410292501)
              ·
                refine ⟨134080486893670566107461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2860383720398305410292501 134080486893670566107461)
                ·
                  rfl

theorem cell22_3525131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 6].length) (baseStart_3525131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525131 prefixEnd_3525131 := by exact prefixLift 3525131
  have htrace : WordTrace (prefixWord ++ tailWord_3525131) baseStart_3525131 baseEnd_3525131 := by
    simpa [prefixWord, tailWord_3525131, baseEnd_3525131] using wordTrace_append hprefix tailTrace_3525131
  have hstable : (prefixWord ++ tailWord_3525131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525131).length < 2 ^ (prefixWord ++ tailWord_3525131).sum := by decide
  have hdescent : baseEnd_3525131 < baseStart_3525131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525146 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_3525146 : Nat := 118140960795 + 3525146 * 2 ^ 59
def prefixEnd_3525146 : Nat := 4983230072969 + 3 ^ 40 * 3525146 * 2
def baseEnd_3525146 : Nat := 1206729516849580055842103

theorem tailTrace_3525146 : CollatzResearch.WordTrace tailWord_3525146 prefixEnd_3525146 1206729516849580055842103 := by
  unfold tailWord_3525146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32143159321751390962624823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85715091524670375900332861 32143159321751390962624823)
  ·
    refine ⟨48214738982627086443937235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32143159321751390962624823 48214738982627086443937235)
    ·
      refine ⟨72322108473940629665905853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48214738982627086443937235 72322108473940629665905853)
      ·
        refine ⟨27120790677727736124714695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72322108473940629665905853 27120790677727736124714695)
        ·
          refine ⟨40681186016591604187072043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27120790677727736124714695 40681186016591604187072043)
          ·
            refine ⟨61021779024887406280608065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40681186016591604187072043 61021779024887406280608065)
            ·
              refine ⟨45766334268665554710456049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61021779024887406280608065 45766334268665554710456049)
              ·
                refine ⟨34324750701499166032842037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45766334268665554710456049 34324750701499166032842037)
                ·
                  refine ⟨3217945378265546815578941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34324750701499166032842037 3217945378265546815578941)
                  ·
                    refine ⟨1206729516849580055842103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217945378265546815578941 1206729516849580055842103)
                    ·
                      rfl

theorem cell22_3525146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_3525146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525146 prefixEnd_3525146 := by exact prefixLift 3525146
  have htrace : WordTrace (prefixWord ++ tailWord_3525146) baseStart_3525146 baseEnd_3525146 := by
    simpa [prefixWord, tailWord_3525146, baseEnd_3525146] using wordTrace_append hprefix tailTrace_3525146
  have hstable : (prefixWord ++ tailWord_3525146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525146).length < 2 ^ (prefixWord ++ tailWord_3525146).sum := by decide
  have hdescent : baseEnd_3525146 < baseStart_3525146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525163 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 1, 3]
def baseStart_3525163 : Nat := 118140960795 + 3525163 * 2 ^ 59
def prefixEnd_3525163 : Nat := 4983230072969 + 3 ^ 40 * 3525163 * 2
def baseEnd_3525163 : Nat := 1206735336296997678167051

theorem tailTrace_3525163 : CollatzResearch.WordTrace tailWord_3525163 prefixEnd_3525163 1206735336296997678167051 := by
  unfold tailWord_3525163
  simp only [CollatzResearch.WordTrace]
  refine ⟨128573257327943975753868143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85715504885295983835912095 128573257327943975753868143)
  ·
    refine ⟨192859885991915963630802215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128573257327943975753868143 192859885991915963630802215)
    ·
      refine ⟨289289828987873945446203323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192859885991915963630802215 289289828987873945446203323)
      ·
        refine ⟨433934743481810918169304985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289289828987873945446203323 433934743481810918169304985)
        ·
          refine ⟨325451057611358188626978739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433934743481810918169304985 325451057611358188626978739)
          ·
            refine ⟨488176586417037282940468109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325451057611358188626978739 488176586417037282940468109)
            ·
              refine ⟨183066219906388981102675541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488176586417037282940468109 183066219906388981102675541)
              ·
                refine ⟨2145307264527995872296979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 183066219906388981102675541 2145307264527995872296979)
                ·
                  refine ⟨3217960896791993808445469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145307264527995872296979 3217960896791993808445469)
                  ·
                    refine ⟨1206735336296997678167051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217960896791993808445469 1206735336296997678167051)
                    ·
                      rfl

theorem cell22_3525163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 3].length) (baseStart_3525163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525163 prefixEnd_3525163 := by exact prefixLift 3525163
  have htrace : WordTrace (prefixWord ++ tailWord_3525163) baseStart_3525163 baseEnd_3525163 := by
    simpa [prefixWord, tailWord_3525163, baseEnd_3525163] using wordTrace_append hprefix tailTrace_3525163
  have hstable : (prefixWord ++ tailWord_3525163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525163).length < 2 ^ (prefixWord ++ tailWord_3525163).sum := by decide
  have hdescent : baseEnd_3525163 < baseStart_3525163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525176 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_3525176 : Nat := 118140960795 + 3525176 * 2 ^ 59
def prefixEnd_3525176 : Nat := 4983230072969 + 3 ^ 40 * 3525176 * 2
def baseEnd_3525176 : Nat := 402246595487556659197337

theorem tailTrace_3525176 : CollatzResearch.WordTrace tailWord_3525176 prefixEnd_3525176 402246595487556659197337 := by
  unfold tailWord_3525176
  simp only [CollatzResearch.WordTrace]
  refine ⟨64286865738448439487045691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85715820984597919316060921 64286865738448439487045691)
  ·
    refine ⟨96430298607672659230568537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64286865738448439487045691 96430298607672659230568537)
    ·
      refine ⟨72322723955754494422926403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96430298607672659230568537 72322723955754494422926403)
      ·
        refine ⟨108484085933631741634389605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72322723955754494422926403 108484085933631741634389605)
        ·
          refine ⟨20340766112555951556448051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108484085933631741634389605 20340766112555951556448051)
          ·
            refine ⟨30511149168833927334672077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20340766112555951556448051 30511149168833927334672077)
            ·
              refine ⟨11441680938312722750502029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30511149168833927334672077 11441680938312722750502029)
              ·
                refine ⟨4290630351867271031438261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11441680938312722750502029 4290630351867271031438261)
                ·
                  refine ⟨402246595487556659197337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4290630351867271031438261 402246595487556659197337)
                  ·
                    rfl

theorem cell22_3525176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_3525176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525176 prefixEnd_3525176 := by exact prefixLift 3525176
  have htrace : WordTrace (prefixWord ++ tailWord_3525176) baseStart_3525176 baseEnd_3525176 := by
    simpa [prefixWord, tailWord_3525176, baseEnd_3525176] using wordTrace_append hprefix tailTrace_3525176
  have hstable : (prefixWord ++ tailWord_3525176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525176).length < 2 ^ (prefixWord ++ tailWord_3525176).sum := by decide
  have hdescent : baseEnd_3525176 < baseStart_3525176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525287 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3525287 : Nat := 118140960795 + 3525287 * 2 ^ 59
def prefixEnd_3525287 : Nat := 4983230072969 + 3 ^ 40 * 3525287 * 2
def baseEnd_3525287 : Nat := 1206777784031102688066671

theorem tailTrace_3525287 : CollatzResearch.WordTrace tailWord_3525287 prefixEnd_3525287 1206777784031102688066671 := by
  unfold tailWord_3525287
  simp only [CollatzResearch.WordTrace]
  refine ⟨128577779979494744931382115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85718519986329829954254743 128577779979494744931382115)
  ·
    refine ⟨192866669969242117397073173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128577779979494744931382115 192866669969242117397073173)
    ·
      refine ⟨9040625154808224252987805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192866669969242117397073173 9040625154808224252987805)
      ·
        refine ⟨3390234433053084094870427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9040625154808224252987805 3390234433053084094870427)
        ·
          refine ⟨5085351649579626142305641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390234433053084094870427 5085351649579626142305641)
          ·
            refine ⟨3814013737184719606729231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5085351649579626142305641 3814013737184719606729231)
            ·
              refine ⟨5721020605777079410093847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814013737184719606729231 5721020605777079410093847)
              ·
                refine ⟨8581530908665619115140771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721020605777079410093847 8581530908665619115140771)
                ·
                  refine ⟨12872296362998428672711157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581530908665619115140771 12872296362998428672711157)
                  ·
                    refine ⟨1206777784031102688066671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12872296362998428672711157 1206777784031102688066671)
                    ·
                      rfl

theorem cell22_3525287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3525287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525287 prefixEnd_3525287 := by exact prefixLift 3525287
  have htrace : WordTrace (prefixWord ++ tailWord_3525287) baseStart_3525287 baseEnd_3525287 := by
    simpa [prefixWord, tailWord_3525287, baseEnd_3525287] using wordTrace_append hprefix tailTrace_3525287
  have hstable : (prefixWord ++ tailWord_3525287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525287).length < 2 ^ (prefixWord ++ tailWord_3525287).sum := by decide
  have hdescent : baseEnd_3525287 < baseStart_3525287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525311 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 7]
def baseStart_3525311 : Nat := 118140960795 + 3525311 * 2 ^ 59
def prefixEnd_3525311 : Nat := 4983230072969 + 3 ^ 40 * 3525311 * 2
def baseEnd_3525311 : Nat := 402261999907191541822199

theorem tailTrace_3525311 : CollatzResearch.WordTrace tailWord_3525311 prefixEnd_3525311 402261999907191541822199 := by
  unfold tailWord_3525311
  simp only [CollatzResearch.WordTrace]
  refine ⟨128578655331407797030255787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85719103554271864686837191 128578655331407797030255787)
  ·
    refine ⟨192867982997111695545383681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128578655331407797030255787 192867982997111695545383681)
    ·
      refine ⟨144650987247833771659037761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192867982997111695545383681 144650987247833771659037761)
      ·
        refine ⟨108488240435875328744278321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144650987247833771659037761 108488240435875328744278321)
        ·
          refine ⟨81366180326906496558208741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108488240435875328744278321 81366180326906496558208741)
          ·
            refine ⟨15256158811294968104664139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81366180326906496558208741 15256158811294968104664139)
            ·
              refine ⟨22884238216942452156996209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15256158811294968104664139 22884238216942452156996209)
              ·
                refine ⟨17163178662706839117747157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22884238216942452156996209 17163178662706839117747157)
                ·
                  refine ⟨402261999907191541822199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17163178662706839117747157 402261999907191541822199)
                  ·
                    rfl

theorem cell22_3525311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_3525311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525311 prefixEnd_3525311 := by exact prefixLift 3525311
  have htrace : WordTrace (prefixWord ++ tailWord_3525311) baseStart_3525311 baseEnd_3525311 := by
    simpa [prefixWord, tailWord_3525311, baseEnd_3525311] using wordTrace_append hprefix tailTrace_3525311
  have hstable : (prefixWord ++ tailWord_3525311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525311).length < 2 ^ (prefixWord ++ tailWord_3525311).sum := by decide
  have hdescent : baseEnd_3525311 < baseStart_3525311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525345 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 5]
def baseStart_3525345 : Nat := 118140960795 + 3525345 * 2 ^ 59
def prefixEnd_3525345 : Nat := 4983230072969 + 3 ^ 40 * 3525345 * 2
def baseEnd_3525345 : Nat := 402265879538803290038831

theorem tailTrace_3525345 : CollatzResearch.WordTrace tailWord_3525345 prefixEnd_3525345 402265879538803290038831 := by
  unfold tailWord_3525345
  simp only [CollatzResearch.WordTrace]
  refine ⟨128579895413284620836993489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85719930275523080557995659 128579895413284620836993489)
  ·
    refine ⟨96434921559963465627745117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128579895413284620836993489 96434921559963465627745117)
    ·
      refine ⟨36163095584986299610404419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96434921559963465627745117 36163095584986299610404419)
      ·
        refine ⟨54244643377479449415606629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36163095584986299610404419 54244643377479449415606629)
        ·
          refine ⟨10170870633277396765426243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54244643377479449415606629 10170870633277396765426243)
          ·
            refine ⟨15256305949916095148139365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170870633277396765426243 15256305949916095148139365)
            ·
              refine ⟨2860557365609267840276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15256305949916095148139365 2860557365609267840276131)
              ·
                refine ⟨4290836048413901760414197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860557365609267840276131 4290836048413901760414197)
                ·
                  refine ⟨402265879538803290038831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4290836048413901760414197 402265879538803290038831)
                  ·
                    rfl

theorem cell22_3525345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_3525345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525345 prefixEnd_3525345 := by exact prefixLift 3525345
  have htrace : WordTrace (prefixWord ++ tailWord_3525345) baseStart_3525345 baseEnd_3525345 := by
    simpa [prefixWord, tailWord_3525345, baseEnd_3525345] using wordTrace_append hprefix tailTrace_3525345
  have hstable : (prefixWord ++ tailWord_3525345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525345).length < 2 ^ (prefixWord ++ tailWord_3525345).sum := by decide
  have hdescent : baseEnd_3525345 < baseStart_3525345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525356 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_3525356 : Nat := 118140960795 + 3525356 * 2 ^ 59
def prefixEnd_3525356 : Nat := 4983230072969 + 3 ^ 40 * 3525356 * 2
def baseEnd_3525356 : Nat := 402267134713736502697153

theorem tailTrace_3525356 : CollatzResearch.WordTrace tailWord_3525356 prefixEnd_3525356 402267134713736502697153 := by
  unfold tailWord_3525356
  simp only [CollatzResearch.WordTrace]
  refine ⟨64290148308122384857821961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85720197744163179810429281 64290148308122384857821961)
  ·
    refine ⟨48217611231091788643366471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64290148308122384857821961 48217611231091788643366471)
    ·
      refine ⟨72326416846637682965049707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48217611231091788643366471 72326416846637682965049707)
      ·
        refine ⟨108489625269956524447574561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72326416846637682965049707 108489625269956524447574561)
        ·
          refine ⟨81367218952467393335680921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108489625269956524447574561 81367218952467393335680921)
          ·
            refine ⟨61025414214350545001760691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81367218952467393335680921 61025414214350545001760691)
            ·
              refine ⟨91538121321525817502641037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61025414214350545001760691 91538121321525817502641037)
              ·
                refine ⟨34326795495572181563490389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91538121321525817502641037 34326795495572181563490389)
                ·
                  refine ⟨402267134713736502697153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34326795495572181563490389 402267134713736502697153)
                  ·
                    rfl

theorem cell22_3525356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_3525356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525356 prefixEnd_3525356 := by exact prefixLift 3525356
  have htrace : WordTrace (prefixWord ++ tailWord_3525356) baseStart_3525356 baseEnd_3525356 := by
    simpa [prefixWord, tailWord_3525356, baseEnd_3525356] using wordTrace_append hprefix tailTrace_3525356
  have hstable : (prefixWord ++ tailWord_3525356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525356).length < 2 ^ (prefixWord ++ tailWord_3525356).sum := by decide
  have hdescent : baseEnd_3525356 < baseStart_3525356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525401 : List Nat := [1, 2, 1, 2, 1, 1, 1, 13]
def baseStart_3525401 : Nat := 118140960795 + 3525401 * 2 ^ 59
def prefixEnd_3525401 : Nat := 4983230072969 + 3 ^ 40 * 3525401 * 2
def baseEnd_3525401 : Nat := 134090756506760487857369

theorem tailTrace_3525401 : CollatzResearch.WordTrace tailWord_3525401 prefixEnd_3525401 134090756506760487857369 := by
  unfold tailWord_3525401
  simp only [CollatzResearch.WordTrace]
  refine ⟨128581937901081742401032057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85721291934054494934021371 128581937901081742401032057)
  ·
    refine ⟨96436453425811306800774043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128581937901081742401032057 96436453425811306800774043)
    ·
      refine ⟨144654680138716960201161065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96436453425811306800774043 144654680138716960201161065)
      ·
        refine ⟨108491010104037720150870799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144654680138716960201161065 108491010104037720150870799)
        ·
          refine ⟨162736515156056580226306199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108491010104037720150870799 162736515156056580226306199)
          ·
            refine ⟨244104772734084870339459299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162736515156056580226306199 244104772734084870339459299)
            ·
              refine ⟨366157159101127305509188949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244104772734084870339459299 366157159101127305509188949)
              ·
                refine ⟨134090756506760487857369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 366157159101127305509188949 134090756506760487857369)
                ·
                  rfl

theorem cell22_3525401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 13].length) (baseStart_3525401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525401 prefixEnd_3525401 := by exact prefixLift 3525401
  have htrace : WordTrace (prefixWord ++ tailWord_3525401) baseStart_3525401 baseEnd_3525401 := by
    simpa [prefixWord, tailWord_3525401, baseEnd_3525401] using wordTrace_append hprefix tailTrace_3525401
  have hstable : (prefixWord ++ tailWord_3525401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525401).length < 2 ^ (prefixWord ++ tailWord_3525401).sum := by decide
  have hdescent : baseEnd_3525401 < baseStart_3525401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525514 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_3525514 : Nat := 118140960795 + 3525514 * 2 ^ 59
def prefixEnd_3525514 : Nat := 4983230072969 + 3 ^ 40 * 3525514 * 2
def baseEnd_3525514 : Nat := 402285163590049920880325

theorem tailTrace_3525514 : CollatzResearch.WordTrace tailWord_3525514 prefixEnd_3525514 402285163590049920880325 := by
  unfold tailWord_3525514
  simp only [CollatzResearch.WordTrace]
  refine ⟨32146514837418090674973899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85724039566448241799930397 32146514837418090674973899)
  ·
    refine ⟨48219772256127136012460849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32146514837418090674973899 48219772256127136012460849)
    ·
      refine ⟨36164829192095352009345637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48219772256127136012460849 36164829192095352009345637)
      ·
        refine ⟨6780905473517878501752307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36164829192095352009345637 6780905473517878501752307)
        ·
          refine ⟨10171358210276817752628461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6780905473517878501752307 10171358210276817752628461)
          ·
            refine ⟨3814259328853806657235673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10171358210276817752628461 3814259328853806657235673)
            ·
              refine ⟨2860694496640354992926755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3814259328853806657235673 2860694496640354992926755)
              ·
                refine ⟨4291041744960532489390133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860694496640354992926755 4291041744960532489390133)
                ·
                  refine ⟨402285163590049920880325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291041744960532489390133 402285163590049920880325)
                  ·
                    rfl

theorem cell22_3525514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_3525514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525514 prefixEnd_3525514 := by exact prefixLift 3525514
  have htrace : WordTrace (prefixWord ++ tailWord_3525514) baseStart_3525514 baseEnd_3525514 := by
    simpa [prefixWord, tailWord_3525514, baseEnd_3525514] using wordTrace_append hprefix tailTrace_3525514
  have hstable : (prefixWord ++ tailWord_3525514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525514).length < 2 ^ (prefixWord ++ tailWord_3525514).sum := by decide
  have hdescent : baseEnd_3525514 < baseStart_3525514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525540 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_3525540 : Nat := 118140960795 + 3525540 * 2 ^ 59
def prefixEnd_3525540 : Nat := 4983230072969 + 3 ^ 40 * 3525540 * 2
def baseEnd_3525540 : Nat := 1206864391101494361490895

theorem tailTrace_3525540 : CollatzResearch.WordTrace tailWord_3525540 prefixEnd_3525540 1206864391101494361490895 := by
  unfold tailWord_3525540
  simp only [CollatzResearch.WordTrace]
  refine ⟨64293503823789084570171037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85724671765052112760228049 64293503823789084570171037)
  ·
    refine ⟨24110063933920906713814139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64293503823789084570171037 24110063933920906713814139)
    ·
      refine ⟨36165095900881360070721209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24110063933920906713814139 36165095900881360070721209)
      ·
        refine ⟨27123821925661020053040907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36165095900881360070721209 27123821925661020053040907)
        ·
          refine ⟨40685732888491530079561361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27123821925661020053040907 40685732888491530079561361)
          ·
            refine ⟨30514299666368647559671021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40685732888491530079561361 30514299666368647559671021)
            ·
              refine ⟨11442862374888242834876633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30514299666368647559671021 11442862374888242834876633)
              ·
                refine ⟨8582146781166182126157475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11442862374888242834876633 8582146781166182126157475)
                ·
                  refine ⟨12873220171749273189236213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8582146781166182126157475 12873220171749273189236213)
                  ·
                    refine ⟨1206864391101494361490895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12873220171749273189236213 1206864391101494361490895)
                    ·
                      rfl

theorem cell22_3525540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_3525540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525540 prefixEnd_3525540 := by exact prefixLift 3525540
  have htrace : WordTrace (prefixWord ++ tailWord_3525540) baseStart_3525540 baseEnd_3525540 := by
    simpa [prefixWord, tailWord_3525540, baseEnd_3525540] using wordTrace_append hprefix tailTrace_3525540
  have hstable : (prefixWord ++ tailWord_3525540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525540).length < 2 ^ (prefixWord ++ tailWord_3525540).sum := by decide
  have hdescent : baseEnd_3525540 < baseStart_3525540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525553 : List Nat := [1, 2, 2, 4, 13]
def baseStart_3525553 : Nat := 118140960795 + 3525553 * 2 ^ 59
def prefixEnd_3525553 : Nat := 4983230072969 + 3 ^ 40 * 3525553 * 2
def baseEnd_3525553 : Nat := 4966538441428669386485

theorem tailTrace_3525553 : CollatzResearch.WordTrace tailWord_3525553 prefixEnd_3525553 4966538441428669386485 := by
  unfold tailWord_3525553
  simp only [CollatzResearch.WordTrace]
  refine ⟨128587481796531072360565313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85724987864354048240376875 128587481796531072360565313)
  ·
    refine ⟨96440611347398304270423985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128587481796531072360565313 96440611347398304270423985)
    ·
      refine ⟨72330458510548728202817989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96440611347398304270423985 72330458510548728202817989)
      ·
        refine ⟨13561960970727886538028373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72330458510548728202817989 13561960970727886538028373)
        ·
          refine ⟨4966538441428669386485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13561960970727886538028373 4966538441428669386485)
          ·
            rfl

theorem cell22_3525553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 13].length) (baseStart_3525553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525553 prefixEnd_3525553 := by exact prefixLift 3525553
  have htrace : WordTrace (prefixWord ++ tailWord_3525553) baseStart_3525553 baseEnd_3525553 := by
    simpa [prefixWord, tailWord_3525553, baseEnd_3525553] using wordTrace_append hprefix tailTrace_3525553
  have hstable : (prefixWord ++ tailWord_3525553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525553).length < 2 ^ (prefixWord ++ tailWord_3525553).sum := by decide
  have hdescent : baseEnd_3525553 < baseStart_3525553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525589 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3525589 : Nat := 118140960795 + 3525589 * 2 ^ 59
def prefixEnd_3525589 : Nat := 4983230072969 + 3 ^ 40 * 3525589 * 2
def baseEnd_3525589 : Nat := 1206881164802874567015745

theorem tailTrace_3525589 : CollatzResearch.WordTrace tailWord_3525589 prefixEnd_3525589 1206881164802874567015745 := by
  unfold tailWord_3525589
  simp only [CollatzResearch.WordTrace]
  refine ⟨128588794824400650508875821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85725863216267100339250547 128588794824400650508875821)
  ·
    refine ⟨48220798059150243940828433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128588794824400650508875821 48220798059150243940828433)
    ·
      refine ⟨36165598544362682955621325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48220798059150243940828433 36165598544362682955621325)
      ·
        refine ⟨13562099454136006108357997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36165598544362682955621325 13562099454136006108357997)
        ·
          refine ⟨5085787295301002290634249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13562099454136006108357997 5085787295301002290634249)
          ·
            refine ⟨3814340471475751717975687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5085787295301002290634249 3814340471475751717975687)
            ·
              refine ⟨5721510707213627576963531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814340471475751717975687 5721510707213627576963531)
              ·
                refine ⟨8582266060820441365445297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721510707213627576963531 8582266060820441365445297)
                ·
                  refine ⟨6436699545615331024083973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8582266060820441365445297 6436699545615331024083973)
                  ·
                    refine ⟨1206881164802874567015745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6436699545615331024083973 1206881164802874567015745)
                    ·
                      rfl

theorem cell22_3525589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3525589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525589 prefixEnd_3525589 := by exact prefixLift 3525589
  have htrace : WordTrace (prefixWord ++ tailWord_3525589) baseStart_3525589 baseEnd_3525589 := by
    simpa [prefixWord, tailWord_3525589, baseEnd_3525589] using wordTrace_append hprefix tailTrace_3525589
  have hstable : (prefixWord ++ tailWord_3525589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525589).length < 2 ^ (prefixWord ++ tailWord_3525589).sum := by decide
  have hdescent : baseEnd_3525589 < baseStart_3525589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525615 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 7]
def baseStart_3525615 : Nat := 118140960795 + 3525615 * 2 ^ 59
def prefixEnd_3525615 : Nat := 4983230072969 + 3 ^ 40 * 3525615 * 2
def baseEnd_3525615 : Nat := 402296688378073055288555

theorem tailTrace_3525615 : CollatzResearch.WordTrace tailWord_3525615 prefixEnd_3525615 402296688378073055288555 := by
  unfold tailWord_3525615
  simp only [CollatzResearch.WordTrace]
  refine ⟨128589743122306456949322299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85726495414870971299548199 128589743122306456949322299)
  ·
    refine ⟨192884614683459685423983449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128589743122306456949322299 192884614683459685423983449)
    ·
      refine ⟨144663461012594764067987587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192884614683459685423983449 144663461012594764067987587)
      ·
        refine ⟨216995191518892146101981381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144663461012594764067987587 216995191518892146101981381)
        ·
          refine ⟨40686598409792277394121509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216995191518892146101981381 40686598409792277394121509)
          ·
            refine ⟨7628737201836052011397783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40686598409792277394121509 7628737201836052011397783)
            ·
              refine ⟨11443105802754078017096675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628737201836052011397783 11443105802754078017096675)
              ·
                refine ⟨17164658704131117025645013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11443105802754078017096675 17164658704131117025645013)
                ·
                  refine ⟨402296688378073055288555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17164658704131117025645013 402296688378073055288555)
                  ·
                    rfl

theorem cell22_3525615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 7].length) (baseStart_3525615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525615 prefixEnd_3525615 := by exact prefixLift 3525615
  have htrace : WordTrace (prefixWord ++ tailWord_3525615) baseStart_3525615 baseEnd_3525615 := by
    simpa [prefixWord, tailWord_3525615, baseEnd_3525615] using wordTrace_append hprefix tailTrace_3525615
  have hstable : (prefixWord ++ tailWord_3525615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525615).length < 2 ^ (prefixWord ++ tailWord_3525615).sum := by decide
  have hdescent : baseEnd_3525615 < baseStart_3525615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525690 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_3525690 : Nat := 118140960795 + 3525690 * 2 ^ 59
def prefixEnd_3525690 : Nat := 4983230072969 + 3 ^ 40 * 3525690 * 2
def baseEnd_3525690 : Nat := 1206915739166943970240435

theorem tailTrace_3525690 : CollatzResearch.WordTrace tailWord_3525690 prefixEnd_3525690 1206915739166943970240435 := by
  unfold tailWord_3525690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32148119649258686189575631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85728319064689829838868349 32148119649258686189575631)
  ·
    refine ⟨48222179473888029284363447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32148119649258686189575631 48222179473888029284363447)
    ·
      refine ⟨72333269210832043926545171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48222179473888029284363447 72333269210832043926545171)
      ·
        refine ⟨108499903816248065889817757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72333269210832043926545171 108499903816248065889817757)
        ·
          refine ⟨40687463931093024708681659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108499903816248065889817757 40687463931093024708681659)
          ·
            refine ⟨61031195896639537063022489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40687463931093024708681659 61031195896639537063022489)
            ·
              refine ⟨45773396922479652797266867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61031195896639537063022489 45773396922479652797266867)
              ·
                refine ⟨68660095383719479195900301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45773396922479652797266867 68660095383719479195900301)
                ·
                  refine ⟨25747535768894804698462613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68660095383719479195900301 25747535768894804698462613)
                  ·
                    refine ⟨1206915739166943970240435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25747535768894804698462613 1206915739166943970240435)
                    ·
                      rfl

theorem cell22_3525690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_3525690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525690 prefixEnd_3525690 := by exact prefixLift 3525690
  have htrace : WordTrace (prefixWord ++ tailWord_3525690) baseStart_3525690 baseEnd_3525690 := by
    simpa [prefixWord, tailWord_3525690, baseEnd_3525690] using wordTrace_append hprefix tailTrace_3525690
  have hstable : (prefixWord ++ tailWord_3525690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525690).length < 2 ^ (prefixWord ++ tailWord_3525690).sum := by decide
  have hdescent : baseEnd_3525690 < baseStart_3525690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525709 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3525709 : Nat := 118140960795 + 3525709 * 2 ^ 59
def prefixEnd_3525709 : Nat := 4983230072969 + 3 ^ 40 * 3525709 * 2
def baseEnd_3525709 : Nat := 1206922243255234254015377

theorem tailTrace_3525709 : CollatzResearch.WordTrace tailWord_3525709 prefixEnd_3525709 1206922243255234254015377 := by
  unfold tailWord_3525709
  simp only [CollatzResearch.WordTrace]
  refine ⟨128593171583965911003244181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85728781055977274002162787 128593171583965911003244181)
  ·
    refine ⟨6027804917998402078277071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128593171583965911003244181 6027804917998402078277071)
    ·
      refine ⟨9041707376997603117415607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6027804917998402078277071 9041707376997603117415607)
      ·
        refine ⟨13562561065496404676123411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041707376997603117415607 13562561065496404676123411)
        ·
          refine ⟨20343841598244607014185117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13562561065496404676123411 20343841598244607014185117)
          ·
            refine ⟨7628940599341727630319419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20343841598244607014185117 7628940599341727630319419)
            ·
              refine ⟨11443410899012591445479129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628940599341727630319419 11443410899012591445479129)
              ·
                refine ⟨8582558174259443584109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11443410899012591445479129 8582558174259443584109347)
                ·
                  refine ⟨12873837261389165376164021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8582558174259443584109347 12873837261389165376164021)
                  ·
                    refine ⟨1206922243255234254015377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12873837261389165376164021 1206922243255234254015377)
                    ·
                      rfl

theorem cell22_3525709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3525709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525709 prefixEnd_3525709 := by exact prefixLift 3525709
  have htrace : WordTrace (prefixWord ++ tailWord_3525709) baseStart_3525709 baseEnd_3525709 := by
    simpa [prefixWord, tailWord_3525709, baseEnd_3525709] using wordTrace_append hprefix tailTrace_3525709
  have hstable : (prefixWord ++ tailWord_3525709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525709).length < 2 ^ (prefixWord ++ tailWord_3525709).sum := by decide
  have hdescent : baseEnd_3525709 < baseStart_3525709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525758 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3525758 : Nat := 118140960795 + 3525758 * 2 ^ 59
def prefixEnd_3525758 : Nat := 4983230072969 + 3 ^ 40 * 3525758 * 2
def baseEnd_3525758 : Nat := 1206939016956614459540227

theorem tailTrace_3525758 : CollatzResearch.WordTrace tailWord_3525758 prefixEnd_3525758 1206939016956614459540227 := by
  unfold tailWord_3525758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074369845098549046472241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85729972507192261581185285 16074369845098549046472241)
  ·
    refine ⟨12055777383823911784854181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16074369845098549046472241 12055777383823911784854181)
    ·
      refine ⟨2260458259466983459660159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12055777383823911784854181 2260458259466983459660159)
      ·
        refine ⟨3390687389200475189490239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260458259466983459660159 3390687389200475189490239)
        ·
          refine ⟨5086031083800712784235359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390687389200475189490239 5086031083800712784235359)
          ·
            refine ⟨7629046625701069176353039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086031083800712784235359 7629046625701069176353039)
            ·
              refine ⟨11443569938551603764529559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629046625701069176353039 11443569938551603764529559)
              ·
                refine ⟨17165354907827405646794339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11443569938551603764529559 17165354907827405646794339)
                ·
                  refine ⟨25748032361741108470191509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17165354907827405646794339 25748032361741108470191509)
                  ·
                    refine ⟨1206939016956614459540227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25748032361741108470191509 1206939016956614459540227)
                    ·
                      rfl

theorem cell22_3525758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3525758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525758 prefixEnd_3525758 := by exact prefixLift 3525758
  have htrace : WordTrace (prefixWord ++ tailWord_3525758) baseStart_3525758 baseEnd_3525758 := by
    simpa [prefixWord, tailWord_3525758, baseEnd_3525758] using wordTrace_append hprefix tailTrace_3525758
  have hstable : (prefixWord ++ tailWord_3525758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525758).length < 2 ^ (prefixWord ++ tailWord_3525758).sum := by decide
  have hdescent : baseEnd_3525758 < baseStart_3525758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525784 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_3525784 : Nat := 118140960795 + 3525784 * 2 ^ 59
def prefixEnd_3525784 : Nat := 4983230072969 + 3 ^ 40 * 3525784 * 2
def baseEnd_3525784 : Nat := 402315972429319686130049

theorem tailTrace_3525784 : CollatzResearch.WordTrace tailWord_3525784 prefixEnd_3525784 402315972429319686130049 := by
  unfold tailWord_3525784
  simp only [CollatzResearch.WordTrace]
  refine ⟨64297953529347099406112203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85730604705796132541482937 64297953529347099406112203)
  ·
    refine ⟨96446930294020649109168305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64297953529347099406112203 96446930294020649109168305)
    ·
      refine ⟨72335197720515486831876229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96446930294020649109168305 72335197720515486831876229)
      ·
        refine ⟨13562849572596653780976793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72335197720515486831876229 13562849572596653780976793)
        ·
          refine ⟨10172137179447490335732595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13562849572596653780976793 10172137179447490335732595)
          ·
            refine ⟨15258205769171235503598893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172137179447490335732595 15258205769171235503598893)
            ·
              refine ⟨5721827163439213313849585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15258205769171235503598893 5721827163439213313849585)
              ·
                refine ⟨4291370372579409985387189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5721827163439213313849585 4291370372579409985387189)
                ·
                  refine ⟨402315972429319686130049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291370372579409985387189 402315972429319686130049)
                  ·
                    rfl

theorem cell22_3525784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_3525784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525784 prefixEnd_3525784 := by exact prefixLift 3525784
  have htrace : WordTrace (prefixWord ++ tailWord_3525784) baseStart_3525784 baseEnd_3525784 := by
    simpa [prefixWord, tailWord_3525784, baseEnd_3525784] using wordTrace_append hprefix tailTrace_3525784
  have hstable : (prefixWord ++ tailWord_3525784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525784).length < 2 ^ (prefixWord ++ tailWord_3525784).sum := by decide
  have hdescent : baseEnd_3525784 < baseStart_3525784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525799 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3525799 : Nat := 118140960795 + 3525799 * 2 ^ 59
def prefixEnd_3525799 : Nat := 4983230072969 + 3 ^ 40 * 3525799 * 2
def baseEnd_3525799 : Nat := 1206953052094504019265101

theorem tailTrace_3525799 : CollatzResearch.WordTrace tailWord_3525799 prefixEnd_3525799 1206953052094504019265101 := by
  unfold tailWord_3525799
  simp only [CollatzResearch.WordTrace]
  refine ⟨128596454153639856374020451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85730969435759904249346967 128596454153639856374020451)
  ·
    refine ⟨192894681230459784561030677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128596454153639856374020451 192894681230459784561030677)
    ·
      refine ⟨9041938182677802401298313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192894681230459784561030677 9041938182677802401298313)
      ·
        refine ⟨6781453637008351800973735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9041938182677802401298313 6781453637008351800973735)
        ·
          refine ⟨10172180455512527701460603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781453637008351800973735 10172180455512527701460603)
          ·
            refine ⟨15258270683268791552190905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172180455512527701460603 15258270683268791552190905)
            ·
              refine ⟨11443703012451593664143179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15258270683268791552190905 11443703012451593664143179)
              ·
                refine ⟨17165554518677390496214769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11443703012451593664143179 17165554518677390496214769)
                ·
                  refine ⟨12874165889008042872161077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17165554518677390496214769 12874165889008042872161077)
                  ·
                    refine ⟨1206953052094504019265101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12874165889008042872161077 1206953052094504019265101)
                    ·
                      rfl

theorem cell22_3525799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3525799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525799 prefixEnd_3525799 := by exact prefixLift 3525799
  have htrace : WordTrace (prefixWord ++ tailWord_3525799) baseStart_3525799 baseEnd_3525799 := by
    simpa [prefixWord, tailWord_3525799, baseEnd_3525799] using wordTrace_append hprefix tailTrace_3525799
  have hstable : (prefixWord ++ tailWord_3525799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525799).length < 2 ^ (prefixWord ++ tailWord_3525799).sum := by decide
  have hdescent : baseEnd_3525799 < baseStart_3525799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525857 : List Nat := [1, 2, 3, 1, 3, 2, 1, 9]
def baseStart_3525857 : Nat := 118140960795 + 3525857 * 2 ^ 59
def prefixEnd_3525857 : Nat := 4983230072969 + 3 ^ 40 * 3525857 * 2
def baseEnd_3525857 : Nat := 134108100742201244590547

theorem tailTrace_3525857 : CollatzResearch.WordTrace tailWord_3525857 prefixEnd_3525857 134108100742201244590547 := by
  unfold tailWord_3525857
  simp only [CollatzResearch.WordTrace]
  refine ⟨128598569587429732279631825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85732379724953154853087883 128598569587429732279631825)
  ·
    refine ⟨96448927190572299209723869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128598569587429732279631825 96448927190572299209723869)
    ·
      refine ⟨36168347696464612203646451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96448927190572299209723869 36168347696464612203646451)
      ·
        refine ⟨54252521544696918305469677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36168347696464612203646451 54252521544696918305469677)
        ·
          refine ⟨20344695579261344364551129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54252521544696918305469677 20344695579261344364551129)
          ·
            refine ⟨15258521684446008273413347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20344695579261344364551129 15258521684446008273413347)
            ·
              refine ⟨22887782526669012410120021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15258521684446008273413347 22887782526669012410120021)
              ·
                refine ⟨134108100742201244590547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22887782526669012410120021 134108100742201244590547)
                ·
                  rfl

theorem cell22_3525857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 9].length) (baseStart_3525857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525857 prefixEnd_3525857 := by exact prefixLift 3525857
  have htrace : WordTrace (prefixWord ++ tailWord_3525857) baseStart_3525857 baseEnd_3525857 := by
    simpa [prefixWord, tailWord_3525857, baseEnd_3525857] using wordTrace_append hprefix tailTrace_3525857
  have hstable : (prefixWord ++ tailWord_3525857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525857).length < 2 ^ (prefixWord ++ tailWord_3525857).sum := by decide
  have hdescent : baseEnd_3525857 < baseStart_3525857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525940 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3525940 : Nat := 118140960795 + 3525940 * 2 ^ 59
def prefixEnd_3525940 : Nat := 4983230072969 + 3 ^ 40 * 3525940 * 2
def baseEnd_3525940 : Nat := 1207001319276026651489669

theorem tailTrace_3525940 : CollatzResearch.WordTrace tailWord_3525940 prefixEnd_3525940 1207001319276026651489669 := by
  unfold tailWord_3525940
  simp only [CollatzResearch.WordTrace]
  refine ⟨64300798423064518727451637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85734397897419358303268849 64300798423064518727451637)
  ·
    refine ⟨6028199852162298630698591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64300798423064518727451637 6028199852162298630698591)
    ·
      refine ⟨9042299778243447946047887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6028199852162298630698591 9042299778243447946047887)
      ·
        refine ⟨13563449667365171919071831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9042299778243447946047887 13563449667365171919071831)
        ·
          refine ⟨20345174501047757878607747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13563449667365171919071831 20345174501047757878607747)
          ·
            refine ⟨30517761751571636817911621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20345174501047757878607747 30517761751571636817911621)
            ·
              refine ⟨5722080328419681903358429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30517761751571636817911621 5722080328419681903358429)
              ·
                refine ⟨2145780123157380713759411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5722080328419681903358429 2145780123157380713759411)
                ·
                  refine ⟨3218670184736071070639117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145780123157380713759411 3218670184736071070639117)
                  ·
                    refine ⟨1207001319276026651489669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3218670184736071070639117 1207001319276026651489669)
                    ·
                      rfl

theorem cell22_3525940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3525940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525940 prefixEnd_3525940 := by exact prefixLift 3525940
  have htrace : WordTrace (prefixWord ++ tailWord_3525940) baseStart_3525940 baseEnd_3525940 := by
    simpa [prefixWord, tailWord_3525940, baseEnd_3525940] using wordTrace_append hprefix tailTrace_3525940
  have hstable : (prefixWord ++ tailWord_3525940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525940).length < 2 ^ (prefixWord ++ tailWord_3525940).sum := by decide
  have hdescent : baseEnd_3525940 < baseStart_3525940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525953 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 5]
def baseStart_3525953 : Nat := 118140960795 + 3525953 * 2 ^ 59
def prefixEnd_3525953 : Nat := 4983230072969 + 3 ^ 40 * 3525953 * 2
def baseEnd_3525953 : Nat := 402335256480566316971543

theorem tailTrace_3525953 : CollatzResearch.WordTrace tailWord_3525953 prefixEnd_3525953 402335256480566316971543 := by
  unfold tailWord_3525953
  simp only [CollatzResearch.WordTrace]
  refine ⟨128602070995081940675126513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85734713996721293783417675 128602070995081940675126513)
  ·
    refine ⟨96451553246311455506344885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128602070995081940675126513 96451553246311455506344885)
    ·
      refine ⟨9042333116841698953719833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96451553246311455506344885 9042333116841698953719833)
      ·
        refine ⟨6781749837631274215289875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042333116841698953719833 6781749837631274215289875)
        ·
          refine ⟨10172624756446911322934813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781749837631274215289875 10172624756446911322934813)
          ·
            refine ⟨3814734283667591746100555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10172624756446911322934813 3814734283667591746100555)
            ·
              refine ⟨5722101425501387619150833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814734283667591746100555 5722101425501387619150833)
              ·
                refine ⟨4291576069126040714363125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5722101425501387619150833 4291576069126040714363125)
                ·
                  refine ⟨402335256480566316971543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291576069126040714363125 402335256480566316971543)
                  ·
                    rfl

theorem cell22_3525953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_3525953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525953 prefixEnd_3525953 := by exact prefixLift 3525953
  have htrace : WordTrace (prefixWord ++ tailWord_3525953) baseStart_3525953 baseEnd_3525953 := by
    simpa [prefixWord, tailWord_3525953, baseEnd_3525953] using wordTrace_append hprefix tailTrace_3525953
  have hstable : (prefixWord ++ tailWord_3525953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525953).length < 2 ^ (prefixWord ++ tailWord_3525953).sum := by decide
  have hdescent : baseEnd_3525953 < baseStart_3525953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525964 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_3525964 : Nat := 118140960795 + 3525964 * 2 ^ 59
def prefixEnd_3525964 : Nat := 4983230072969 + 3 ^ 40 * 3525964 * 2
def baseEnd_3525964 : Nat := 402336511655499529629865

theorem tailTrace_3525964 : CollatzResearch.WordTrace tailWord_3525964 prefixEnd_3525964 402336511655499529629865 := by
  unfold tailWord_3525964
  simp only [CollatzResearch.WordTrace]
  refine ⟨64301236099021044776888473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85734981465361393035851297 64301236099021044776888473)
  ·
    refine ⟨48225927074265783582666355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64301236099021044776888473 48225927074265783582666355)
    ·
      refine ⟨72338890611398675373999533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48225927074265783582666355 72338890611398675373999533)
      ·
        refine ⟨27127083979274503265249825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72338890611398675373999533 27127083979274503265249825)
        ·
          refine ⟨20345312984455877448937369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27127083979274503265249825 20345312984455877448937369)
          ·
            refine ⟨15258984738341908086703027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20345312984455877448937369 15258984738341908086703027)
            ·
              refine ⟨22888477107512862130054541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15258984738341908086703027 22888477107512862130054541)
              ·
                refine ⟨8583178915317323298770453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22888477107512862130054541 8583178915317323298770453)
                ·
                  refine ⟨402336511655499529629865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8583178915317323298770453 402336511655499529629865)
                  ·
                    rfl

theorem cell22_3525964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_3525964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525964 prefixEnd_3525964 := by exact prefixLift 3525964
  have htrace : WordTrace (prefixWord ++ tailWord_3525964) baseStart_3525964 baseEnd_3525964 := by
    simpa [prefixWord, tailWord_3525964, baseEnd_3525964] using wordTrace_append hprefix tailTrace_3525964
  have hstable : (prefixWord ++ tailWord_3525964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525964).length < 2 ^ (prefixWord ++ tailWord_3525964).sum := by decide
  have hdescent : baseEnd_3525964 < baseStart_3525964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3525996 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_3525996 : Nat := 118140960795 + 3525996 * 2 ^ 59
def prefixEnd_3525996 : Nat := 4983230072969 + 3 ^ 40 * 3525996 * 2
def baseEnd_3525996 : Nat := 1207020489220461172089497

theorem tailTrace_3525996 : CollatzResearch.WordTrace tailWord_3525996 prefixEnd_3525996 1207020489220461172089497 := by
  unfold tailWord_3525996
  simp only [CollatzResearch.WordTrace]
  refine ⟨64301819666963079509470921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85735759555950772679294561 64301819666963079509470921)
  ·
    refine ⟨48226364750222309632103191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64301819666963079509470921 48226364750222309632103191)
    ·
      refine ⟨72339547125333464448154787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48226364750222309632103191 72339547125333464448154787)
      ·
        refine ⟨108509320688000196672232181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72339547125333464448154787 108509320688000196672232181)
        ·
          refine ⟨10172748814500018438021767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108509320688000196672232181 10172748814500018438021767)
          ·
            refine ⟨15259123221750027657032651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172748814500018438021767 15259123221750027657032651)
            ·
              refine ⟨22888684832625041485548977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259123221750027657032651 22888684832625041485548977)
              ·
                refine ⟨17166513624468781114161733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22888684832625041485548977 17166513624468781114161733)
                ·
                  refine ⟨3218721304587896458905325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17166513624468781114161733 3218721304587896458905325)
                  ·
                    refine ⟨1207020489220461172089497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3218721304587896458905325 1207020489220461172089497)
                    ·
                      rfl

theorem cell22_3525996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_3525996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3525996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3525996 prefixEnd_3525996 := by exact prefixLift 3525996
  have htrace : WordTrace (prefixWord ++ tailWord_3525996) baseStart_3525996 baseEnd_3525996 := by
    simpa [prefixWord, tailWord_3525996, baseEnd_3525996] using wordTrace_append hprefix tailTrace_3525996
  have hstable : (prefixWord ++ tailWord_3525996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3525996).length < 2 ^ (prefixWord ++ tailWord_3525996).sum := by decide
  have hdescent : baseEnd_3525996 < baseStart_3525996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3525996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526030 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3526030 : Nat := 118140960795 + 3526030 * 2 ^ 59
def prefixEnd_3526030 : Nat := 4983230072969 + 3 ^ 40 * 3526030 * 2
def baseEnd_3526030 : Nat := 1207032128115296416739393

theorem tailTrace_3526030 : CollatzResearch.WordTrace tailWord_3526030 prefixEnd_3526030 1207032128115296416739393 := by
  unfold tailWord_3526030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075609926975372853209943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85736586277201988550453029 16075609926975372853209943)
  ·
    refine ⟨24113414890463059279814915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16075609926975372853209943 24113414890463059279814915)
    ·
      refine ⟨36170122335694588919722373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24113414890463059279814915 36170122335694588919722373)
      ·
        refine ⟨6781897937942735422447945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36170122335694588919722373 6781897937942735422447945)
        ·
          refine ⟨5086423453457051566835959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6781897937942735422447945 5086423453457051566835959)
          ·
            refine ⟨7629635180185577350253939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086423453457051566835959 7629635180185577350253939)
            ·
              refine ⟨11444452770278366025380909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629635180185577350253939 11444452770278366025380909)
              ·
                refine ⟨4291669788854387259517841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11444452770278366025380909 4291669788854387259517841)
                ·
                  refine ⟨3218752341640790444638381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4291669788854387259517841 3218752341640790444638381)
                  ·
                    refine ⟨1207032128115296416739393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3218752341640790444638381 1207032128115296416739393)
                    ·
                      rfl

theorem cell22_3526030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3526030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526030 prefixEnd_3526030 := by exact prefixLift 3526030
  have htrace : WordTrace (prefixWord ++ tailWord_3526030) baseStart_3526030 baseEnd_3526030 := by
    simpa [prefixWord, tailWord_3526030, baseEnd_3526030] using wordTrace_append hprefix tailTrace_3526030
  have hstable : (prefixWord ++ tailWord_3526030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526030).length < 2 ^ (prefixWord ++ tailWord_3526030).sum := by decide
  have hdescent : baseEnd_3526030 < baseStart_3526030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526071 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 5]
def baseStart_3526071 : Nat := 118140960795 + 3526071 * 2 ^ 59
def prefixEnd_3526071 : Nat := 4983230072969 + 3 ^ 40 * 3526071 * 2
def baseEnd_3526071 : Nat := 402348721084395325488089

theorem tailTrace_3526071 : CollatzResearch.WordTrace tailWord_3526071 prefixEnd_3526071 402348721084395325488089 := by
  unfold tailWord_3526071
  simp only [CollatzResearch.WordTrace]
  refine ⟨128606374808654446827922067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85737583205769631218614711 128606374808654446827922067)
  ·
    refine ⟨192909562212981670241883101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128606374808654446827922067 192909562212981670241883101)
    ·
      refine ⟨72341085829868126340706163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192909562212981670241883101 72341085829868126340706163)
      ·
        refine ⟨108511628744802189511059245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72341085829868126340706163 108511628744802189511059245)
        ·
          refine ⟨40691860779300821066647217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108511628744802189511059245 40691860779300821066647217)
          ·
            refine ⟨30518895584475615799985413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40691860779300821066647217 30518895584475615799985413)
            ·
              refine ⟨5722292922089177962497265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30518895584475615799985413 5722292922089177962497265)
              ·
                refine ⟨4291719691566883471872949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5722292922089177962497265 4291719691566883471872949)
                ·
                  refine ⟨402348721084395325488089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291719691566883471872949 402348721084395325488089)
                  ·
                    rfl

theorem cell22_3526071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 5].length) (baseStart_3526071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526071 prefixEnd_3526071 := by exact prefixLift 3526071
  have htrace : WordTrace (prefixWord ++ tailWord_3526071) baseStart_3526071 baseEnd_3526071 := by
    simpa [prefixWord, tailWord_3526071, baseEnd_3526071] using wordTrace_append hprefix tailTrace_3526071
  have hstable : (prefixWord ++ tailWord_3526071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526071).length < 2 ^ (prefixWord ++ tailWord_3526071).sum := by decide
  have hdescent : baseEnd_3526071 < baseStart_3526071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526101 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3526101 : Nat := 118140960795 + 3526101 * 2 ^ 59
def prefixEnd_3526101 : Nat := 4983230072969 + 3 ^ 40 * 3526101 * 2
def baseEnd_3526101 : Nat := 1207056432866275898214175

theorem tailTrace_3526101 : CollatzResearch.WordTrace tailWord_3526101 prefixEnd_3526101 1207056432866275898214175 := by
  unfold tailWord_3526101
  simp only [CollatzResearch.WordTrace]
  refine ⟨128607468998545761951514157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85738312665697174634342771 128607468998545761951514157)
  ·
    refine ⟨48227800874454660731817809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128607468998545761951514157 48227800874454660731817809)
    ·
      refine ⟨36170850655840995548863357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48227800874454660731817809 36170850655840995548863357)
      ·
        refine ⟨13564068995940373330823759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36170850655840995548863357 13564068995940373330823759)
        ·
          refine ⟨20346103493910559996235639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13564068995940373330823759 20346103493910559996235639)
          ·
            refine ⟨30519155240865839994353459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20346103493910559996235639 30519155240865839994353459)
            ·
              refine ⟨45778732861298759991530189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30519155240865839994353459 45778732861298759991530189)
              ·
                refine ⟨17167024822987034996823821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45778732861298759991530189 17167024822987034996823821)
                ·
                  refine ⟨6437634308620138123808933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17167024822987034996823821 6437634308620138123808933)
                  ·
                    refine ⟨1207056432866275898214175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6437634308620138123808933 1207056432866275898214175)
                    ·
                      rfl

theorem cell22_3526101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3526101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526101 prefixEnd_3526101 := by exact prefixLift 3526101
  have htrace : WordTrace (prefixWord ++ tailWord_3526101) baseStart_3526101 baseEnd_3526101 := by
    simpa [prefixWord, tailWord_3526101, baseEnd_3526101] using wordTrace_append hprefix tailTrace_3526101
  have hstable : (prefixWord ++ tailWord_3526101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526101).length < 2 ^ (prefixWord ++ tailWord_3526101).sum := by decide
  have hdescent : baseEnd_3526101 < baseStart_3526101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526133 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 6]
def baseStart_3526133 : Nat := 118140960795 + 3526133 * 2 ^ 59
def prefixEnd_3526133 : Nat := 4983230072969 + 3 ^ 40 * 3526133 * 2
def baseEnd_3526133 : Nat := 402355795706746160471359

theorem tailTrace_3526133 : CollatzResearch.WordTrace tailWord_3526133 prefixEnd_3526133 402355795706746160471359 := by
  unfold tailWord_3526133
  simp only [CollatzResearch.WordTrace]
  refine ⟨128608636134429831416679053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85739090756286554277786035 128608636134429831416679053)
  ·
    refine ⟨48228238550411186781254645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128608636134429831416679053 48228238550411186781254645)
    ·
      refine ⟨4521397364101048760742623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48228238550411186781254645 4521397364101048760742623)
      ·
        refine ⟨6782096046151573141113935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521397364101048760742623 6782096046151573141113935)
        ·
          refine ⟨10173144069227359711670903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782096046151573141113935 10173144069227359711670903)
          ·
            refine ⟨15259716103841039567506355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10173144069227359711670903 15259716103841039567506355)
            ·
              refine ⟨22889574155761559351259533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259716103841039567506355 22889574155761559351259533)
              ·
                refine ⟨8583590308410584756722325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22889574155761559351259533 8583590308410584756722325)
                ·
                  refine ⟨402355795706746160471359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8583590308410584756722325 402355795706746160471359)
                  ·
                    rfl

theorem cell22_3526133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_3526133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526133 prefixEnd_3526133 := by exact prefixLift 3526133
  have htrace : WordTrace (prefixWord ++ tailWord_3526133) baseStart_3526133 baseEnd_3526133 := by
    simpa [prefixWord, tailWord_3526133, baseEnd_3526133] using wordTrace_append hprefix tailTrace_3526133
  have hstable : (prefixWord ++ tailWord_3526133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526133).length < 2 ^ (prefixWord ++ tailWord_3526133).sum := by decide
  have hdescent : baseEnd_3526133 < baseStart_3526133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526244 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_3526244 : Nat := 118140960795 + 3526244 * 2 ^ 59
def prefixEnd_3526244 : Nat := 4983230072969 + 3 ^ 40 * 3526244 * 2
def baseEnd_3526244 : Nat := 1207105384688671191888737

theorem tailTrace_3526244 : CollatzResearch.WordTrace tailWord_3526244 prefixEnd_3526244 1207105384688671191888737 := by
  unfold tailWord_3526244
  simp only [CollatzResearch.WordTrace]
  refine ⟨64306342318513848686984893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85741789758018464915979857 64306342318513848686984893)
  ·
    refine ⟨24114878369442693257619335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64306342318513848686984893 24114878369442693257619335)
    ·
      refine ⟨36172317554164039886429003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24114878369442693257619335 36172317554164039886429003)
      ·
        refine ⟨54258476331246059829643505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36172317554164039886429003 54258476331246059829643505)
        ·
          refine ⟨40693857248434544872232629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54258476331246059829643505 40693857248434544872232629)
          ·
            refine ⟨3815049117040738581771809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40693857248434544872232629 3815049117040738581771809)
            ·
              refine ⟨2861286837780553936328857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815049117040738581771809 2861286837780553936328857)
              ·
                refine ⟨2145965128335415452246643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861286837780553936328857 2145965128335415452246643)
                ·
                  refine ⟨3218947692503123178369965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145965128335415452246643 3218947692503123178369965)
                  ·
                    refine ⟨1207105384688671191888737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3218947692503123178369965 1207105384688671191888737)
                    ·
                      rfl

theorem cell22_3526244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_3526244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526244 prefixEnd_3526244 := by exact prefixLift 3526244
  have htrace : WordTrace (prefixWord ++ tailWord_3526244) baseStart_3526244 baseEnd_3526244 := by
    simpa [prefixWord, tailWord_3526244, baseEnd_3526244] using wordTrace_append hprefix tailTrace_3526244
  have hstable : (prefixWord ++ tailWord_3526244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526244).length < 2 ^ (prefixWord ++ tailWord_3526244).sum := by decide
  have hdescent : baseEnd_3526244 < baseStart_3526244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526283 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 4, 3]
def baseStart_3526283 : Nat := 118140960795 + 3526283 * 2 ^ 59
def prefixEnd_3526283 : Nat := 4983230072969 + 3 ^ 40 * 3526283 * 2
def baseEnd_3526283 : Nat := 1207118735185688090163617

theorem tailTrace_3526283 : CollatzResearch.WordTrace tailWord_3526283 prefixEnd_3526283 1207118735185688090163617 := by
  unfold tailWord_3526283
  simp only [CollatzResearch.WordTrace]
  refine ⟨128614107083886407034639503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85742738055924271356426335 128614107083886407034639503)
  ·
    refine ⟨192921160625829610551959255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128614107083886407034639503 192921160625829610551959255)
    ·
      refine ⟨289381740938744415827938883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192921160625829610551959255 289381740938744415827938883)
      ·
        refine ⟨434072611408116623741908325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289381740938744415827938883 434072611408116623741908325)
        ·
          refine ⟨81388614639021866951607811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434072611408116623741908325 81388614639021866951607811)
          ·
            refine ⟨122082921958532800427411717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81388614639021866951607811 122082921958532800427411717)
            ·
              refine ⟨22890547867224900080139697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122082921958532800427411717 22890547867224900080139697)
              ·
                refine ⟨17167910900418675060104773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22890547867224900080139697 17167910900418675060104773)
                ·
                  refine ⟨3218983293828501573769645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17167910900418675060104773 3218983293828501573769645)
                  ·
                    refine ⟨1207118735185688090163617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3218983293828501573769645 1207118735185688090163617)
                    ·
                      rfl

theorem cell22_3526283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 3].length) (baseStart_3526283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526283 prefixEnd_3526283 := by exact prefixLift 3526283
  have htrace : WordTrace (prefixWord ++ tailWord_3526283) baseStart_3526283 baseEnd_3526283 := by
    simpa [prefixWord, tailWord_3526283, baseEnd_3526283] using wordTrace_append hprefix tailTrace_3526283
  have hstable : (prefixWord ++ tailWord_3526283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526283).length < 2 ^ (prefixWord ++ tailWord_3526283).sum := by decide
  have hdescent : baseEnd_3526283 < baseStart_3526283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526302 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3526302 : Nat := 118140960795 + 3526302 * 2 ^ 59
def prefixEnd_3526302 : Nat := 4983230072969 + 3 ^ 40 * 3526302 * 2
def baseEnd_3526302 : Nat := 402375079757992791312853

theorem tailTrace_3526302 : CollatzResearch.WordTrace tailWord_3526302 prefixEnd_3526302 402375079757992791312853 := by
  unfold tailWord_3526302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16076850008852196659947645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85743200047211715519720773 16076850008852196659947645)
  ·
    refine ⟨6028818753319573747480367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16076850008852196659947645 6028818753319573747480367)
    ·
      refine ⟨9043228129979360621220551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6028818753319573747480367 9043228129979360621220551)
      ·
        refine ⟨13564842194969040931830827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9043228129979360621220551 13564842194969040931830827)
        ·
          refine ⟨20347263292453561397746241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13564842194969040931830827 20347263292453561397746241)
          ·
            refine ⟨15260447469340171048309681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20347263292453561397746241 15260447469340171048309681)
            ·
              refine ⟨11445335602005128286232261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15260447469340171048309681 11445335602005128286232261)
              ·
                refine ⟨2146000425375961553668549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11445335602005128286232261 2146000425375961553668549)
                ·
                  refine ⟨402375079757992791312853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146000425375961553668549 402375079757992791312853)
                  ·
                    rfl

theorem cell22_3526302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3526302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526302 prefixEnd_3526302 := by exact prefixLift 3526302
  have htrace : WordTrace (prefixWord ++ tailWord_3526302) baseStart_3526302 baseEnd_3526302 := by
    simpa [prefixWord, tailWord_3526302, baseEnd_3526302] using wordTrace_append hprefix tailTrace_3526302
  have hstable : (prefixWord ++ tailWord_3526302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526302).length < 2 ^ (prefixWord ++ tailWord_3526302).sum := by decide
  have hdescent : baseEnd_3526302 < baseStart_3526302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526330 : List Nat := [3, 1, 1, 1, 2, 6, 2, 6]
def baseStart_3526330 : Nat := 118140960795 + 3526330 * 2 ^ 59
def prefixEnd_3526330 : Nat := 4983230072969 + 3 ^ 40 * 3526330 * 2
def baseEnd_3526330 : Nat := 134126091582910626026497

theorem tailTrace_3526330 : CollatzResearch.WordTrace tailWord_3526330 prefixEnd_3526330 134126091582910626026497 := by
  unfold tailWord_3526330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32153955328679033515400111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85743880876477422707733629 32153955328679033515400111)
  ·
    refine ⟨48230932993018550273100167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32153955328679033515400111 48230932993018550273100167)
    ·
      refine ⟨72346399489527825409650251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48230932993018550273100167 72346399489527825409650251)
      ·
        refine ⟨108519599234291738114475377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72346399489527825409650251 108519599234291738114475377)
        ·
          refine ⟨81389699425718803585856533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108519599234291738114475377 81389699425718803585856533)
          ·
            refine ⟨3815142160580568918087025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81389699425718803585856533 3815142160580568918087025)
            ·
              refine ⟨2861356620435426688565269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815142160580568918087025 2861356620435426688565269)
              ·
                refine ⟨134126091582910626026497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2861356620435426688565269 134126091582910626026497)
                ·
                  rfl

theorem cell22_3526330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_3526330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526330 prefixEnd_3526330 := by exact prefixLift 3526330
  have htrace : WordTrace (prefixWord ++ tailWord_3526330) baseStart_3526330 baseEnd_3526330 := by
    simpa [prefixWord, tailWord_3526330, baseEnd_3526330] using wordTrace_append hprefix tailTrace_3526330
  have hstable : (prefixWord ++ tailWord_3526330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526330).length < 2 ^ (prefixWord ++ tailWord_3526330).sum := by decide
  have hdescent : baseEnd_3526330 < baseStart_3526330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526362 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_3526362 : Nat := 118140960795 + 3526362 * 2 ^ 59
def prefixEnd_3526362 : Nat := 4983230072969 + 3 ^ 40 * 3526362 * 2
def baseEnd_3526362 : Nat := 1207145778500158217438375

theorem tailTrace_3526362 : CollatzResearch.WordTrace tailWord_3526362 prefixEnd_3526362 1207145778500158217438375 := by
  unfold tailWord_3526362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32154247112650050881691335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85744658967066802351176893 32154247112650050881691335)
  ·
    refine ⟨48231370668975076322537003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32154247112650050881691335 48231370668975076322537003)
    ·
      refine ⟨72347056003462614483805505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48231370668975076322537003 72347056003462614483805505)
      ·
        refine ⟨54260292002596960862854129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72347056003462614483805505 54260292002596960862854129)
        ·
          refine ⟨40695219001947720647140597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54260292002596960862854129 40695219001947720647140597)
          ·
            refine ⟨3815176781432598810669431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40695219001947720647140597 3815176781432598810669431)
            ·
              refine ⟨5722765172148898216004147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815176781432598810669431 5722765172148898216004147)
              ·
                refine ⟨8584147758223347324006221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722765172148898216004147 8584147758223347324006221)
                ·
                  refine ⟨3219055409333755246502333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8584147758223347324006221 3219055409333755246502333)
                  ·
                    refine ⟨1207145778500158217438375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219055409333755246502333 1207145778500158217438375)
                    ·
                      rfl

theorem cell22_3526362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_3526362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526362 prefixEnd_3526362 := by exact prefixLift 3526362
  have htrace : WordTrace (prefixWord ++ tailWord_3526362) baseStart_3526362 baseEnd_3526362 := by
    simpa [prefixWord, tailWord_3526362, baseEnd_3526362] using wordTrace_append hprefix tailTrace_3526362
  have hstable : (prefixWord ++ tailWord_3526362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526362).length < 2 ^ (prefixWord ++ tailWord_3526362).sum := by decide
  have hdescent : baseEnd_3526362 < baseStart_3526362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526373 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3526373 : Nat := 118140960795 + 3526373 * 2 ^ 59
def prefixEnd_3526373 : Nat := 4983230072969 + 3 ^ 40 * 3526373 * 2
def baseEnd_3526373 : Nat := 1207149544024957855413341

theorem tailTrace_3526373 : CollatzResearch.WordTrace tailWord_3526373 prefixEnd_3526373 1207149544024957855413341 := by
  unfold tailWord_3526373
  simp only [CollatzResearch.WordTrace]
  refine ⟨128617389653560352405415773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85744926435706901603610515 128617389653560352405415773)
  ·
    refine ⟨48231521120085132152030915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128617389653560352405415773 48231521120085132152030915)
    ·
      refine ⟨72347281680127698228046373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48231521120085132152030915 72347281680127698228046373)
      ·
        refine ⟨13565115315023943417758695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72347281680127698228046373 13565115315023943417758695)
        ·
          refine ⟨20347672972535915126638043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13565115315023943417758695 20347672972535915126638043)
          ·
            refine ⟨30521509458803872689957065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20347672972535915126638043 30521509458803872689957065)
            ·
              refine ⟨22891132094102904517467799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30521509458803872689957065 22891132094102904517467799)
              ·
                refine ⟨34336698141154356776201699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22891132094102904517467799 34336698141154356776201699)
                ·
                  refine ⟨51505047211731535164302549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34336698141154356776201699 51505047211731535164302549)
                  ·
                    refine ⟨1207149544024957855413341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51505047211731535164302549 1207149544024957855413341)
                    ·
                      rfl

theorem cell22_3526373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3526373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526373 prefixEnd_3526373 := by exact prefixLift 3526373
  have htrace : WordTrace (prefixWord ++ tailWord_3526373) baseStart_3526373 baseEnd_3526373 := by
    simpa [prefixWord, tailWord_3526373, baseEnd_3526373] using wordTrace_append hprefix tailTrace_3526373
  have hstable : (prefixWord ++ tailWord_3526373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526373).length < 2 ^ (prefixWord ++ tailWord_3526373).sum := by decide
  have hdescent : baseEnd_3526373 < baseStart_3526373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526450 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3526450 : Nat := 118140960795 + 3526450 * 2 ^ 59
def prefixEnd_3526450 : Nat := 4983230072969 + 3 ^ 40 * 3526450 * 2
def baseEnd_3526450 : Nat := 1207175902698555321238105

theorem tailTrace_3526450 : CollatzResearch.WordTrace tailWord_3526450 prefixEnd_3526450 1207175902698555321238105 := by
  unfold tailWord_3526450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32155049518570348638992201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85746798716187596370645869 32155049518570348638992201)
  ·
    refine ⟨24116287138927761479244151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32155049518570348638992201 24116287138927761479244151)
    ·
      refine ⟨36174430708391642218866227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24116287138927761479244151 36174430708391642218866227)
      ·
        refine ⟨54261646062587463328299341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36174430708391642218866227 54261646062587463328299341)
        ·
          refine ⟨20348117273470298748112253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54261646062587463328299341 20348117273470298748112253)
          ·
            refine ⟨7630543977551362030542095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20348117273470298748112253 7630543977551362030542095)
            ·
              refine ⟨11445815966327043045813143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630543977551362030542095 11445815966327043045813143)
              ·
                refine ⟨17168723949490564568719715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11445815966327043045813143 17168723949490564568719715)
                ·
                  refine ⟨25753085924235846853079573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17168723949490564568719715 25753085924235846853079573)
                  ·
                    refine ⟨1207175902698555321238105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25753085924235846853079573 1207175902698555321238105)
                    ·
                      rfl

theorem cell22_3526450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3526450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526450 prefixEnd_3526450 := by exact prefixLift 3526450
  have htrace : WordTrace (prefixWord ++ tailWord_3526450) baseStart_3526450 baseEnd_3526450 := by
    simpa [prefixWord, tailWord_3526450, baseEnd_3526450] using wordTrace_append hprefix tailTrace_3526450
  have hstable : (prefixWord ++ tailWord_3526450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526450).length < 2 ^ (prefixWord ++ tailWord_3526450).sum := by decide
  have hdescent : baseEnd_3526450 < baseStart_3526450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526452 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3526452 : Nat := 118140960795 + 3526452 * 2 ^ 59
def prefixEnd_3526452 : Nat := 4983230072969 + 3 ^ 40 * 3526452 * 2
def baseEnd_3526452 : Nat := 1207176587339427982688099

theorem tailTrace_3526452 : CollatzResearch.WordTrace tailWord_3526452 prefixEnd_3526452 1207176587339427982688099 := by
  unfold tailWord_3526452
  simp only [CollatzResearch.WordTrace]
  refine ⟨64310135510137074448770805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85746847346849432598361073 64310135510137074448770805)
  ·
    refine ⟨6029075204075350729572263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64310135510137074448770805 6029075204075350729572263)
    ·
      refine ⟨9043612806113026094358395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6029075204075350729572263 9043612806113026094358395)
      ·
        refine ⟨13565419209169539141537593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9043612806113026094358395 13565419209169539141537593)
        ·
          refine ⟨10174064406877154356153195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13565419209169539141537593 10174064406877154356153195)
          ·
            refine ⟨15261096610315731534229793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174064406877154356153195 15261096610315731534229793)
            ·
              refine ⟨11445822457736798650672345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15261096610315731534229793 11445822457736798650672345)
              ·
                refine ⟨8584366843302598988004259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11445822457736798650672345 8584366843302598988004259)
                ·
                  refine ⟨12876550264953898482006389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584366843302598988004259 12876550264953898482006389)
                  ·
                    refine ⟨1207176587339427982688099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12876550264953898482006389 1207176587339427982688099)
                    ·
                      rfl

theorem cell22_3526452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3526452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526452 prefixEnd_3526452 := by exact prefixLift 3526452
  have htrace : WordTrace (prefixWord ++ tailWord_3526452) baseStart_3526452 baseEnd_3526452 := by
    simpa [prefixWord, tailWord_3526452, baseEnd_3526452] using wordTrace_append hprefix tailTrace_3526452
  have hstable : (prefixWord ++ tailWord_3526452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526452).length < 2 ^ (prefixWord ++ tailWord_3526452).sum := by decide
  have hdescent : baseEnd_3526452 < baseStart_3526452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526454 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_3526454 : Nat := 118140960795 + 3526454 * 2 ^ 59
def prefixEnd_3526454 : Nat := 4983230072969 + 3 ^ 40 * 3526454 * 2
def baseEnd_3526454 : Nat := 402392423993433548046031

theorem tailTrace_3526454 : CollatzResearch.WordTrace tailWord_3526454 prefixEnd_3526454 402392423993433548046031 := by
  unfold tailWord_3526454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038771497891681452444651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85746895977511268826076277 8038771497891681452444651)
  ·
    refine ⟨12058157246837522178666977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038771497891681452444651 12058157246837522178666977)
    ·
      refine ⟨9043617935128141634000233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12058157246837522178666977 9043617935128141634000233)
      ·
        refine ⟨6782713451346106225500175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9043617935128141634000233 6782713451346106225500175)
        ·
          refine ⟨10174070177019159338250263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782713451346106225500175 10174070177019159338250263)
          ·
            refine ⟨15261105265528739007375395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174070177019159338250263 15261105265528739007375395)
            ·
              refine ⟨22891657898293108511063093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15261105265528739007375395 22891657898293108511063093)
              ·
                refine ⟨2146092927964978922912165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22891657898293108511063093 2146092927964978922912165)
                ·
                  refine ⟨402392423993433548046031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146092927964978922912165 402392423993433548046031)
                  ·
                    rfl

theorem cell22_3526454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_3526454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526454 prefixEnd_3526454 := by exact prefixLift 3526454
  have htrace : WordTrace (prefixWord ++ tailWord_3526454) baseStart_3526454 baseEnd_3526454 := by
    simpa [prefixWord, tailWord_3526454, baseEnd_3526454] using wordTrace_append hprefix tailTrace_3526454
  have hstable : (prefixWord ++ tailWord_3526454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526454).length < 2 ^ (prefixWord ++ tailWord_3526454).sum := by decide
  have hdescent : baseEnd_3526454 < baseStart_3526454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526499 : List Nat := [1, 1, 1, 5, 5, 1, 2, 6]
def baseStart_3526499 : Nat := 118140960795 + 3526499 * 2 ^ 59
def prefixEnd_3526499 : Nat := 4983230072969 + 3 ^ 40 * 3526499 * 2
def baseEnd_3526499 : Nat := 134132519599992836306995

theorem tailTrace_3526499 : CollatzResearch.WordTrace tailWord_3526499 prefixEnd_3526499 134132519599992836306995 := by
  unfold tailWord_3526499
  simp only [CollatzResearch.WordTrace]
  refine ⟨128621985251103875924502551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85747990167402583949668367 128621985251103875924502551)
  ·
    refine ⟨192932977876655813886753827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128621985251103875924502551 192932977876655813886753827)
    ·
      refine ⟨289399466814983720830130741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192932977876655813886753827 289399466814983720830130741)
      ·
        refine ⟨27131200013904723827824757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289399466814983720830130741 27131200013904723827824757)
        ·
          refine ⟨2543550001303567858858571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27131200013904723827824757 2543550001303567858858571)
          ·
            refine ⟨3815325001955351788287857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543550001303567858858571 3815325001955351788287857)
            ·
              refine ⟨2861493751466513841215893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815325001955351788287857 2861493751466513841215893)
              ·
                refine ⟨134132519599992836306995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2861493751466513841215893 134132519599992836306995)
                ·
                  rfl

theorem cell22_3526499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 6].length) (baseStart_3526499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526499 prefixEnd_3526499 := by exact prefixLift 3526499
  have htrace : WordTrace (prefixWord ++ tailWord_3526499) baseStart_3526499 baseEnd_3526499 := by
    simpa [prefixWord, tailWord_3526499, baseEnd_3526499] using wordTrace_append hprefix tailTrace_3526499
  have hstable : (prefixWord ++ tailWord_3526499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526499).length < 2 ^ (prefixWord ++ tailWord_3526499).sum := by decide
  have hdescent : baseEnd_3526499 < baseStart_3526499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526531 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 1, 3]
def baseStart_3526531 : Nat := 118140960795 + 3526531 * 2 ^ 59
def prefixEnd_3526531 : Nat := 4983230072969 + 3 ^ 40 * 3526531 * 2
def baseEnd_3526531 : Nat := 1207203630653898109962857

theorem tailTrace_3526531 : CollatzResearch.WordTrace tailWord_3526531 prefixEnd_3526531 1207203630653898109962857 := by
  unfold tailWord_3526531
  simp only [CollatzResearch.WordTrace]
  refine ⟨128623152386987945389667447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85748768257991963593111631 128623152386987945389667447)
  ·
    refine ⟨192934728580481918084501171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128623152386987945389667447 192934728580481918084501171)
    ·
      refine ⟨289402092870722877126751757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192934728580481918084501171 289402092870722877126751757)
      ·
        refine ⟨108525784826521078922531909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289402092870722877126751757 108525784826521078922531909)
        ·
          refine ⟨20348584654972702297974733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108525784826521078922531909 20348584654972702297974733)
          ·
            refine ⟨7630719245614763361740525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20348584654972702297974733 7630719245614763361740525)
            ·
              refine ⟨2861519717105536260652697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7630719245614763361740525 2861519717105536260652697)
              ·
                refine ⟨2146139787829152195489523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861519717105536260652697 2146139787829152195489523)
                ·
                  refine ⟨3219209681743728293234285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146139787829152195489523 3219209681743728293234285)
                  ·
                    refine ⟨1207203630653898109962857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219209681743728293234285 1207203630653898109962857)
                    ·
                      rfl

theorem cell22_3526531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 3].length) (baseStart_3526531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526531 prefixEnd_3526531 := by exact prefixLift 3526531
  have htrace : WordTrace (prefixWord ++ tailWord_3526531) baseStart_3526531 baseEnd_3526531 := by
    simpa [prefixWord, tailWord_3526531, baseEnd_3526531] using wordTrace_append hprefix tailTrace_3526531
  have hstable : (prefixWord ++ tailWord_3526531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526531).length < 2 ^ (prefixWord ++ tailWord_3526531).sum := by decide
  have hdescent : baseEnd_3526531 < baseStart_3526531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526540 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_3526540 : Nat := 118140960795 + 3526540 * 2 ^ 59
def prefixEnd_3526540 : Nat := 4983230072969 + 3 ^ 40 * 3526540 * 2
def baseEnd_3526540 : Nat := 1207206711537825086487829

theorem tailTrace_3526540 : CollatzResearch.WordTrace tailWord_3526540 prefixEnd_3526540 1207206711537825086487829 := by
  unfold tailWord_3526540
  simp only [CollatzResearch.WordTrace]
  refine ⟨64311740321977669963372537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85748987095970226617830049 64311740321977669963372537)
  ·
    refine ⟨48233805241483252472529403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64311740321977669963372537 48233805241483252472529403)
    ·
      refine ⟨72350707862224878708794105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48233805241483252472529403 72350707862224878708794105)
      ·
        refine ⟨54263030896668659031595579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72350707862224878708794105 54263030896668659031595579)
        ·
          refine ⟨81394546345002988547393369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54263030896668659031595579 81394546345002988547393369)
          ·
            refine ⟨61045909758752241410545027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81394546345002988547393369 61045909758752241410545027)
            ·
              refine ⟨91568864638128362115817541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61045909758752241410545027 91568864638128362115817541)
              ·
                refine ⟨17169162119649067896715789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91568864638128362115817541 17169162119649067896715789)
                ·
                  refine ⟨6438435794868400461268421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17169162119649067896715789 6438435794868400461268421)
                  ·
                    refine ⟨1207206711537825086487829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6438435794868400461268421 1207206711537825086487829)
                    ·
                      rfl

theorem cell22_3526540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_3526540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526540 prefixEnd_3526540 := by exact prefixLift 3526540
  have htrace : WordTrace (prefixWord ++ tailWord_3526540) baseStart_3526540 baseEnd_3526540 := by
    simpa [prefixWord, tailWord_3526540, baseEnd_3526540] using wordTrace_append hprefix tailTrace_3526540
  have hstable : (prefixWord ++ tailWord_3526540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526540).length < 2 ^ (prefixWord ++ tailWord_3526540).sum := by decide
  have hdescent : baseEnd_3526540 < baseStart_3526540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526557 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3526557 : Nat := 118140960795 + 3526557 * 2 ^ 59
def prefixEnd_3526557 : Nat := 4983230072969 + 3 ^ 40 * 3526557 * 2
def baseEnd_3526557 : Nat := 1207212530985242708812777

theorem tailTrace_3526557 : CollatzResearch.WordTrace tailWord_3526557 prefixEnd_3526557 1207212530985242708812777 := by
  unfold tailWord_3526557
  simp only [CollatzResearch.WordTrace]
  refine ⟨128624100684893751830113925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85749400456595834553409283 128624100684893751830113925)
  ·
    refine ⟨24117018878417578468146361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128624100684893751830113925 24117018878417578468146361)
    ·
      refine ⟨18087764158813183851109771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24117018878417578468146361 18087764158813183851109771)
      ·
        refine ⟨27131646238219775776664657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18087764158813183851109771 27131646238219775776664657)
        ·
          refine ⟨20348734678664831832498493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27131646238219775776664657 20348734678664831832498493)
          ·
            refine ⟨7630775504499311937186935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20348734678664831832498493 7630775504499311937186935)
            ·
              refine ⟨11446163256748967905780403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630775504499311937186935 11446163256748967905780403)
              ·
                refine ⟨17169244885123451858670605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446163256748967905780403 17169244885123451858670605)
                ·
                  refine ⟨6438466831921294447001477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17169244885123451858670605 6438466831921294447001477)
                  ·
                    refine ⟨1207212530985242708812777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6438466831921294447001477 1207212530985242708812777)
                    ·
                      rfl

theorem cell22_3526557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3526557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526557 prefixEnd_3526557 := by exact prefixLift 3526557
  have htrace : WordTrace (prefixWord ++ tailWord_3526557) baseStart_3526557 baseEnd_3526557 := by
    simpa [prefixWord, tailWord_3526557, baseEnd_3526557] using wordTrace_append hprefix tailTrace_3526557
  have hstable : (prefixWord ++ tailWord_3526557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526557).length < 2 ^ (prefixWord ++ tailWord_3526557).sum := by decide
  have hdescent : baseEnd_3526557 < baseStart_3526557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526587 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 2, 3]
def baseStart_3526587 : Nat := 118140960795 + 3526587 * 2 ^ 59
def prefixEnd_3526587 : Nat := 4983230072969 + 3 ^ 40 * 3526587 * 2
def baseEnd_3526587 : Nat := 1207222800598332630562685

theorem tailTrace_3526587 : CollatzResearch.WordTrace tailWord_3526587 prefixEnd_3526587 1207222800598332630562685 := by
  unfold tailWord_3526587
  simp only [CollatzResearch.WordTrace]
  refine ⟨128625194874785066953706015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85750129916523377969137343 128625194874785066953706015)
  ·
    refine ⟨192937792312177600430559023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128625194874785066953706015 192937792312177600430559023)
    ·
      refine ⟨289406688468266400645838535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192937792312177600430559023 289406688468266400645838535)
      ·
        refine ⟨434110032702399600968757803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289406688468266400645838535 434110032702399600968757803)
        ·
          refine ⟨651165049053599401453136705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434110032702399600968757803 651165049053599401453136705)
          ·
            refine ⟨488373786790199551089852529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651165049053599401453136705 488373786790199551089852529)
            ·
              refine ⟨366280340092649663317389397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488373786790199551089852529 366280340092649663317389397)
              ·
                refine ⟨4292347735460738242000657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 366280340092649663317389397 4292347735460738242000657)
                ·
                  refine ⟨3219260801595553681500493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292347735460738242000657 3219260801595553681500493)
                  ·
                    refine ⟨1207222800598332630562685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219260801595553681500493 1207222800598332630562685)
                    ·
                      rfl

theorem cell22_3526587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 3].length) (baseStart_3526587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526587 prefixEnd_3526587 := by exact prefixLift 3526587
  have htrace : WordTrace (prefixWord ++ tailWord_3526587) baseStart_3526587 baseEnd_3526587 := by
    simpa [prefixWord, tailWord_3526587, baseEnd_3526587] using wordTrace_append hprefix tailTrace_3526587
  have hstable : (prefixWord ++ tailWord_3526587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526587).length < 2 ^ (prefixWord ++ tailWord_3526587).sum := by decide
  have hdescent : baseEnd_3526587 < baseStart_3526587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526589 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 4]
def baseStart_3526589 : Nat := 118140960795 + 3526589 * 2 ^ 59
def prefixEnd_3526589 : Nat := 4983230072969 + 3 ^ 40 * 3526589 * 2
def baseEnd_3526589 : Nat := 402407828413068430670893

theorem tailTrace_3526589 : CollatzResearch.WordTrace tailWord_3526589 prefixEnd_3526589 402407828413068430670893 := by
  unfold tailWord_3526589
  simp only [CollatzResearch.WordTrace]
  refine ⟨128625267820777821295278821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85750178547185214196852547 128625267820777821295278821)
  ·
    refine ⟨24117237716395841492864779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128625267820777821295278821 24117237716395841492864779)
    ·
      refine ⟨36175856574593762239297169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24117237716395841492864779 36175856574593762239297169)
      ·
        refine ⟨27131892430945321679472877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36175856574593762239297169 27131892430945321679472877)
        ·
          refine ⟨10174459661604495629802329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27131892430945321679472877 10174459661604495629802329)
          ·
            refine ⟨7630844746203371722351747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10174459661604495629802329 7630844746203371722351747)
            ·
              refine ⟨11446267119305057583527621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630844746203371722351747 11446267119305057583527621)
              ·
                refine ⟨2146175084869698296911429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11446267119305057583527621 2146175084869698296911429)
                ·
                  refine ⟨402407828413068430670893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146175084869698296911429 402407828413068430670893)
                  ·
                    rfl

theorem cell22_3526589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_3526589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526589 prefixEnd_3526589 := by exact prefixLift 3526589
  have htrace : WordTrace (prefixWord ++ tailWord_3526589) baseStart_3526589 baseEnd_3526589 := by
    simpa [prefixWord, tailWord_3526589, baseEnd_3526589] using wordTrace_append hprefix tailTrace_3526589
  have hstable : (prefixWord ++ tailWord_3526589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526589).length < 2 ^ (prefixWord ++ tailWord_3526589).sum := by decide
  have hdescent : baseEnd_3526589 < baseStart_3526589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526604 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_3526604 : Nat := 118140960795 + 3526604 * 2 ^ 59
def prefixEnd_3526604 : Nat := 4983230072969 + 3 ^ 40 * 3526604 * 2
def baseEnd_3526604 : Nat := 1207228620045750252887633

theorem tailTrace_3526604 : CollatzResearch.WordTrace tailWord_3526604 prefixEnd_3526604 1207228620045750252887633 := by
  unfold tailWord_3526604
  simp only [CollatzResearch.WordTrace]
  refine ⟨64312907457861739428537433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85750543277148985904716577 64312907457861739428537433)
  ·
    refine ⟨48234680593396304571403075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64312907457861739428537433 48234680593396304571403075)
    ·
      refine ⟨72352020890094456857104613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48234680593396304571403075 72352020890094456857104613)
      ·
        refine ⟨13566003916892710660707115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72352020890094456857104613 13566003916892710660707115)
        ·
          refine ⟨20349005875339065991060673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13566003916892710660707115 20349005875339065991060673)
          ·
            refine ⟨15261754406504299493295505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20349005875339065991060673 15261754406504299493295505)
            ·
              refine ⟨11446315804878224619971629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15261754406504299493295505 11446315804878224619971629)
              ·
                refine ⟨4292368426829334232489361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11446315804878224619971629 4292368426829334232489361)
                ·
                  refine ⟨3219276320122000674367021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292368426829334232489361 3219276320122000674367021)
                  ·
                    refine ⟨1207228620045750252887633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219276320122000674367021 1207228620045750252887633)
                    ·
                      rfl

theorem cell22_3526604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_3526604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526604 prefixEnd_3526604 := by exact prefixLift 3526604
  have htrace : WordTrace (prefixWord ++ tailWord_3526604) baseStart_3526604 baseEnd_3526604 := by
    simpa [prefixWord, tailWord_3526604, baseEnd_3526604] using wordTrace_append hprefix tailTrace_3526604
  have hstable : (prefixWord ++ tailWord_3526604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526604).length < 2 ^ (prefixWord ++ tailWord_3526604).sum := by decide
  have hdescent : baseEnd_3526604 < baseStart_3526604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526632 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_3526632 : Nat := 118140960795 + 3526632 * 2 ^ 59
def prefixEnd_3526632 : Nat := 4983230072969 + 3 ^ 40 * 3526632 * 2
def baseEnd_3526632 : Nat := 1207238205017967513187547

theorem tailTrace_3526632 : CollatzResearch.WordTrace tailWord_3526632 prefixEnd_3526632 1207238205017967513187547 := by
  unfold tailWord_3526632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64313418079811019819547075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85751224106414693092729433 64313418079811019819547075)
  ·
    refine ⟨96470127119716529729320613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64313418079811019819547075 96470127119716529729320613)
    ·
      refine ⟨18088148834946849324247615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96470127119716529729320613 18088148834946849324247615)
      ·
        refine ⟨27132223252420273986371423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18088148834946849324247615 27132223252420273986371423)
        ·
          refine ⟨40698334878630410979557135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27132223252420273986371423 40698334878630410979557135)
          ·
            refine ⟨61047502317945616469335703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40698334878630410979557135 61047502317945616469335703)
            ·
              refine ⟨91571253476918424704003555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61047502317945616469335703 91571253476918424704003555)
              ·
                refine ⟨137356880215377637056005333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91571253476918424704003555 137356880215377637056005333)
                ·
                  refine ⟨3219301880047913368500125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 137356880215377637056005333 3219301880047913368500125)
                  ·
                    refine ⟨1207238205017967513187547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219301880047913368500125 1207238205017967513187547)
                    ·
                      rfl

theorem cell22_3526632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_3526632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526632 prefixEnd_3526632 := by exact prefixLift 3526632
  have htrace : WordTrace (prefixWord ++ tailWord_3526632) baseStart_3526632 baseEnd_3526632 := by
    simpa [prefixWord, tailWord_3526632, baseEnd_3526632] using wordTrace_append hprefix tailTrace_3526632
  have hstable : (prefixWord ++ tailWord_3526632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526632).length < 2 ^ (prefixWord ++ tailWord_3526632).sum := by decide
  have hdescent : baseEnd_3526632 < baseStart_3526632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526649 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_3526649 : Nat := 118140960795 + 3526649 * 2 ^ 59
def prefixEnd_3526649 : Nat := 4983230072969 + 3 ^ 40 * 3526649 * 2
def baseEnd_3526649 : Nat := 1207244024465385135512495

theorem tailTrace_3526649 : CollatzResearch.WordTrace tailWord_3526649 prefixEnd_3526649 1207244024465385135512495 := by
  unfold tailWord_3526649
  simp only [CollatzResearch.WordTrace]
  refine ⟨128627456200560451542463001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85751637467040301028308667 128627456200560451542463001)
  ·
    refine ⟨96470592150420338656847251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128627456200560451542463001 96470592150420338656847251)
    ·
      refine ⟨144705888225630507985270877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96470592150420338656847251 144705888225630507985270877)
      ·
        refine ⟨54264708084611440494476579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144705888225630507985270877 54264708084611440494476579)
        ·
          refine ⟨81397062126917160741714869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54264708084611440494476579 81397062126917160741714869)
          ·
            refine ⟨7630974574398483819535769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81397062126917160741714869 7630974574398483819535769)
            ·
              refine ⟨5723230930798862864651827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7630974574398483819535769 5723230930798862864651827)
              ·
                refine ⟨8584846396198294296977741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723230930798862864651827 8584846396198294296977741)
                ·
                  refine ⟨3219317398574360361366653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8584846396198294296977741 3219317398574360361366653)
                  ·
                    refine ⟨1207244024465385135512495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219317398574360361366653 1207244024465385135512495)
                    ·
                      rfl

theorem cell22_3526649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_3526649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526649 prefixEnd_3526649 := by exact prefixLift 3526649
  have htrace : WordTrace (prefixWord ++ tailWord_3526649) baseStart_3526649 baseEnd_3526649 := by
    simpa [prefixWord, tailWord_3526649, baseEnd_3526649] using wordTrace_append hprefix tailTrace_3526649
  have hstable : (prefixWord ++ tailWord_3526649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526649).length < 2 ^ (prefixWord ++ tailWord_3526649).sum := by decide
  have hdescent : baseEnd_3526649 < baseStart_3526649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526707 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 6]
def baseStart_3526707 : Nat := 118140960795 + 3526707 * 2 ^ 59
def prefixEnd_3526707 : Nat := 4983230072969 + 3 ^ 40 * 3526707 * 2
def baseEnd_3526707 : Nat := 402421293016897439187439

theorem tailTrace_3526707 : CollatzResearch.WordTrace tailWord_3526707 prefixEnd_3526707 402421293016897439187439 := by
  unfold tailWord_3526707
  simp only [CollatzResearch.WordTrace]
  refine ⟨128629571634350327448074375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85753047756233551632049583 128629571634350327448074375)
  ·
    refine ⟨192944357451525491172111563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128629571634350327448074375 192944357451525491172111563)
    ·
      refine ⟨289416536177288236758167345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192944357451525491172111563 289416536177288236758167345)
      ·
        refine ⟨217062402132966177568625509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289416536177288236758167345 217062402132966177568625509)
        ·
          refine ⟨40699200399931158294117283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217062402132966177568625509 40699200399931158294117283)
          ·
            refine ⟨61048800599896737441175925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40699200399931158294117283 61048800599896737441175925)
            ·
              refine ⟨5723325056240319135110243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61048800599896737441175925 5723325056240319135110243)
              ·
                refine ⟨8584987584360478702665365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723325056240319135110243 8584987584360478702665365)
                ·
                  refine ⟨402421293016897439187439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8584987584360478702665365 402421293016897439187439)
                  ·
                    rfl

theorem cell22_3526707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 6].length) (baseStart_3526707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526707 prefixEnd_3526707 := by exact prefixLift 3526707
  have htrace : WordTrace (prefixWord ++ tailWord_3526707) baseStart_3526707 baseEnd_3526707 := by
    simpa [prefixWord, tailWord_3526707, baseEnd_3526707] using wordTrace_append hprefix tailTrace_3526707
  have hstable : (prefixWord ++ tailWord_3526707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526707).length < 2 ^ (prefixWord ++ tailWord_3526707).sum := by decide
  have hdescent : baseEnd_3526707 < baseStart_3526707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526713 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 5]
def baseStart_3526713 : Nat := 118140960795 + 3526713 * 2 ^ 59
def prefixEnd_3526713 : Nat := 4983230072969 + 3 ^ 40 * 3526713 * 2
def baseEnd_3526713 : Nat := 402421977657770100637433

theorem tailTrace_3526713 : CollatzResearch.WordTrace tailWord_3526713 prefixEnd_3526713 402421977657770100637433 := by
  unfold tailWord_3526713
  simp only [CollatzResearch.WordTrace]
  refine ⟨128629790472328590472792793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85753193648219060315195195 128629790472328590472792793)
  ·
    refine ⟨96472342854246442854594595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128629790472328590472792793 96472342854246442854594595)
    ·
      refine ⟨144708514281369664281891893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96472342854246442854594595 144708514281369664281891893)
      ·
        refine ⟨13566423213878406026427365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144708514281369664281891893 13566423213878406026427365)
        ·
          refine ⟨2543704352602201129955131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13566423213878406026427365 2543704352602201129955131)
          ·
            refine ⟨3815556528903301694932697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543704352602201129955131 3815556528903301694932697)
            ·
              refine ⟨2861667396677476271199523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815556528903301694932697 2861667396677476271199523)
              ·
                refine ⟨4292501095016214406799285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861667396677476271199523 4292501095016214406799285)
                ·
                  refine ⟨402421977657770100637433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4292501095016214406799285 402421977657770100637433)
                  ·
                    rfl

theorem cell22_3526713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_3526713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526713 prefixEnd_3526713 := by exact prefixLift 3526713
  have htrace : WordTrace (prefixWord ++ tailWord_3526713) baseStart_3526713 baseEnd_3526713 := by
    simpa [prefixWord, tailWord_3526713, baseEnd_3526713] using wordTrace_append hprefix tailTrace_3526713
  have hstable : (prefixWord ++ tailWord_3526713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526713).length < 2 ^ (prefixWord ++ tailWord_3526713).sum := by decide
  have hdescent : baseEnd_3526713 < baseStart_3526713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526726 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3526726 : Nat := 118140960795 + 3526726 * 2 ^ 59
def prefixEnd_3526726 : Nat := 4983230072969 + 3 ^ 40 * 3526726 * 2
def baseEnd_3526726 : Nat := 1207270383138982601337259

theorem tailTrace_3526726 : CollatzResearch.WordTrace tailWord_3526726 prefixEnd_3526726 1207270383138982601337259 := by
  unfold tailWord_3526726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019695769415046677906751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85753509747520995795344021 4019695769415046677906751)
  ·
    refine ⟨6029543654122570016860127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019695769415046677906751 6029543654122570016860127)
    ·
      refine ⟨9044315481183855025290191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6029543654122570016860127 9044315481183855025290191)
      ·
        refine ⟨13566473221775782537935287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9044315481183855025290191 13566473221775782537935287)
        ·
          refine ⟨20349709832663673806902931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13566473221775782537935287 20349709832663673806902931)
          ·
            refine ⟨30524564748995510710354397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20349709832663673806902931 30524564748995510710354397)
            ·
              refine ⟨11446711780873316516382899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30524564748995510710354397 11446711780873316516382899)
              ·
                refine ⟨17170067671309974774574349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446711780873316516382899 17170067671309974774574349)
                ·
                  refine ⟨6438775376741240540465381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17170067671309974774574349 6438775376741240540465381)
                  ·
                    refine ⟨1207270383138982601337259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6438775376741240540465381 1207270383138982601337259)
                    ·
                      rfl

theorem cell22_3526726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3526726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526726 prefixEnd_3526726 := by exact prefixLift 3526726
  have htrace : WordTrace (prefixWord ++ tailWord_3526726) baseStart_3526726 baseEnd_3526726 := by
    simpa [prefixWord, tailWord_3526726, baseEnd_3526726] using wordTrace_append hprefix tailTrace_3526726
  have hstable : (prefixWord ++ tailWord_3526726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526726).length < 2 ^ (prefixWord ++ tailWord_3526726).sum := by decide
  have hdescent : baseEnd_3526726 < baseStart_3526726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526818 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3526818 : Nat := 118140960795 + 3526818 * 2 ^ 59
def prefixEnd_3526818 : Nat := 4983230072969 + 3 ^ 40 * 3526818 * 2
def baseEnd_3526818 : Nat := 1207301876619125028036977

theorem tailTrace_3526818 : CollatzResearch.WordTrace tailWord_3526818 prefixEnd_3526818 1207301876619125028036977 := by
  unfold tailWord_3526818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32158405034237048351341277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85755746757965462270243405 32158405034237048351341277)
  ·
    refine ⟨12059401887838893131752979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32158405034237048351341277 12059401887838893131752979)
    ·
      refine ⟨18089102831758339697629469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12059401887838893131752979 18089102831758339697629469)
      ·
        refine ⟨6783413561909377386611051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18089102831758339697629469 6783413561909377386611051)
        ·
          refine ⟨10175120342864066079916577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783413561909377386611051 10175120342864066079916577)
          ·
            refine ⟨7631340257148049559937433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10175120342864066079916577 7631340257148049559937433)
            ·
              refine ⟨5723505192861037169953075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7631340257148049559937433 5723505192861037169953075)
              ·
                refine ⟨8585257789291555754929613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723505192861037169953075 8585257789291555754929613)
                ·
                  refine ⟨3219471670984333408098605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8585257789291555754929613 3219471670984333408098605)
                  ·
                    refine ⟨1207301876619125028036977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219471670984333408098605 1207301876619125028036977)
                    ·
                      rfl

theorem cell22_3526818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3526818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526818 prefixEnd_3526818 := by exact prefixLift 3526818
  have htrace : WordTrace (prefixWord ++ tailWord_3526818) baseStart_3526818 baseEnd_3526818 := by
    simpa [prefixWord, tailWord_3526818, baseEnd_3526818] using wordTrace_append hprefix tailTrace_3526818
  have hstable : (prefixWord ++ tailWord_3526818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526818).length < 2 ^ (prefixWord ++ tailWord_3526818).sum := by decide
  have hdescent : baseEnd_3526818 < baseStart_3526818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526891 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 2, 3]
def baseStart_3526891 : Nat := 118140960795 + 3526891 * 2 ^ 59
def prefixEnd_3526891 : Nat := 4983230072969 + 3 ^ 40 * 3526891 * 2
def baseEnd_3526891 : Nat := 1207326866010977170961753

theorem tailTrace_3526891 : CollatzResearch.WordTrace tailWord_3526891 prefixEnd_3526891 1207326866010977170961753 := by
  unfold tailWord_3526891
  simp only [CollatzResearch.WordTrace]
  refine ⟨128636282665683726872772527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85757521777122484581848351 128636282665683726872772527)
  ·
    refine ⟨192954423998525590309158791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128636282665683726872772527 192954423998525590309158791)
    ·
      refine ⟨289431635997788385463738187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192954423998525590309158791 289431635997788385463738187)
      ·
        refine ⟨434147453996682578195607281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289431635997788385463738187 434147453996682578195607281)
        ·
          refine ⟨325610590497511933646705461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434147453996682578195607281 325610590497511933646705461)
          ·
            refine ⟨30525992859141743779378637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 325610590497511933646705461 30525992859141743779378637)
            ·
              refine ⟨11447247322178153917266989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30525992859141743779378637 11447247322178153917266989)
              ·
                refine ⟨4292717745816807718975121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11447247322178153917266989 4292717745816807718975121)
                ·
                  refine ⟨3219538309362605789231341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292717745816807718975121 3219538309362605789231341)
                  ·
                    refine ⟨1207326866010977170961753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219538309362605789231341 1207326866010977170961753)
                    ·
                      rfl

theorem cell22_3526891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 3].length) (baseStart_3526891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526891 prefixEnd_3526891 := by exact prefixLift 3526891
  have htrace : WordTrace (prefixWord ++ tailWord_3526891) baseStart_3526891 baseEnd_3526891 := by
    simpa [prefixWord, tailWord_3526891, baseEnd_3526891] using wordTrace_append hprefix tailTrace_3526891
  have hstable : (prefixWord ++ tailWord_3526891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526891).length < 2 ^ (prefixWord ++ tailWord_3526891).sum := by decide
  have hdescent : baseEnd_3526891 < baseStart_3526891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526906 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_3526906 : Nat := 118140960795 + 3526906 * 2 ^ 59
def prefixEnd_3526906 : Nat := 4983230072969 + 3 ^ 40 * 3526906 * 2
def baseEnd_3526906 : Nat := 1207332000817522131836707

theorem tailTrace_3526906 : CollatzResearch.WordTrace tailWord_3526906 prefixEnd_3526906 1207332000817522131836707 := by
  unfold tailWord_3526906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32159207440157346108642143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85757886507086256289712381 32159207440157346108642143)
  ·
    refine ⟨48238811160236019162963215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32159207440157346108642143 48238811160236019162963215)
    ·
      refine ⟨72358216740354028744444823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48238811160236019162963215 72358216740354028744444823)
      ·
        refine ⟨108537325110531043116667235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72358216740354028744444823 108537325110531043116667235)
        ·
          refine ⟨162805987665796564675000853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108537325110531043116667235 162805987665796564675000853)
          ·
            refine ⟨7631530671834213969140665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162805987665796564675000853 7631530671834213969140665)
            ·
              refine ⟨5723648003875660476855499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7631530671834213969140665 5723648003875660476855499)
              ·
                refine ⟨8585472005813490715283249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723648003875660476855499 8585472005813490715283249)
                ·
                  refine ⟨6439104004360118036462437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8585472005813490715283249 6439104004360118036462437)
                  ·
                    refine ⟨1207332000817522131836707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439104004360118036462437 1207332000817522131836707)
                    ·
                      rfl

theorem cell22_3526906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_3526906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526906 prefixEnd_3526906 := by exact prefixLift 3526906
  have htrace : WordTrace (prefixWord ++ tailWord_3526906) baseStart_3526906 baseEnd_3526906 := by
    simpa [prefixWord, tailWord_3526906, baseEnd_3526906] using wordTrace_append hprefix tailTrace_3526906
  have hstable : (prefixWord ++ tailWord_3526906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526906).length < 2 ^ (prefixWord ++ tailWord_3526906).sum := by decide
  have hdescent : baseEnd_3526906 < baseStart_3526906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526936 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_3526936 : Nat := 118140960795 + 3526936 * 2 ^ 59
def prefixEnd_3526936 : Nat := 4983230072969 + 3 ^ 40 * 3526936 * 2
def baseEnd_3526936 : Nat := 1207342270430612053586615

theorem tailTrace_3526936 : CollatzResearch.WordTrace tailWord_3526936 prefixEnd_3526936 1207342270430612053586615 := by
  unfold tailWord_3526936
  simp only [CollatzResearch.WordTrace]
  refine ⟨64318961975260349779080331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85758615967013799705440441 64318961975260349779080331)
  ·
    refine ⟨96478442962890524668620497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64318961975260349779080331 96478442962890524668620497)
    ·
      refine ⟨72358832222167893501465373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96478442962890524668620497 72358832222167893501465373)
      ·
        refine ⟨27134562083312960063049515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72358832222167893501465373 27134562083312960063049515)
        ·
          refine ⟨40701843124969440094574273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27134562083312960063049515 40701843124969440094574273)
          ·
            refine ⟨30526382343727080070930705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40701843124969440094574273 30526382343727080070930705)
            ·
              refine ⟨22894786757795310053198029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30526382343727080070930705 22894786757795310053198029)
              ·
                refine ⟨8585545034173241269949261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22894786757795310053198029 8585545034173241269949261)
                ·
                  refine ⟨3219579387814965476230973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8585545034173241269949261 3219579387814965476230973)
                  ·
                    refine ⟨1207342270430612053586615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219579387814965476230973 1207342270430612053586615)
                    ·
                      rfl

theorem cell22_3526936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_3526936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526936 prefixEnd_3526936 := by exact prefixLift 3526936
  have htrace : WordTrace (prefixWord ++ tailWord_3526936) baseStart_3526936 baseEnd_3526936 := by
    simpa [prefixWord, tailWord_3526936, baseEnd_3526936] using wordTrace_append hprefix tailTrace_3526936
  have hstable : (prefixWord ++ tailWord_3526936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526936).length < 2 ^ (prefixWord ++ tailWord_3526936).sum := by decide
  have hdescent : baseEnd_3526936 < baseStart_3526936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526938 : List Nat := [3, 1, 1, 3, 5, 1, 1, 7]
def baseStart_3526938 : Nat := 118140960795 + 3526938 * 2 ^ 59
def prefixEnd_3526938 : Nat := 4983230072969 + 3 ^ 40 * 3526938 * 2
def baseEnd_3526938 : Nat := 134149217230164968337401

theorem tailTrace_3526938 : CollatzResearch.WordTrace tailWord_3526938 prefixEnd_3526938 134149217230164968337401 := by
  unfold tailWord_3526938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32159499224128363474933367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85758664597675635933155645 32159499224128363474933367)
  ·
    refine ⟨48239248836192545212400051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32159499224128363474933367 48239248836192545212400051)
    ·
      refine ⟨72358873254288817818600077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48239248836192545212400051 72358873254288817818600077)
      ·
        refine ⟨27134577470358306681975029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72358873254288817818600077 27134577470358306681975029)
        ·
          refine ⟨2543866637846091251435159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27134577470358306681975029 2543866637846091251435159)
          ·
            refine ⟨3815799956769136877152739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543866637846091251435159 3815799956769136877152739)
            ·
              refine ⟨5723699935153705315729109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815799956769136877152739 5723699935153705315729109)
              ·
                refine ⟨134149217230164968337401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5723699935153705315729109 134149217230164968337401)
                ·
                  rfl

theorem cell22_3526938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_3526938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526938 prefixEnd_3526938 := by exact prefixLift 3526938
  have htrace : WordTrace (prefixWord ++ tailWord_3526938) baseStart_3526938 baseEnd_3526938 := by
    simpa [prefixWord, tailWord_3526938, baseEnd_3526938] using wordTrace_append hprefix tailTrace_3526938
  have hstable : (prefixWord ++ tailWord_3526938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526938).length < 2 ^ (prefixWord ++ tailWord_3526938).sum := by decide
  have hdescent : baseEnd_3526938 < baseStart_3526938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526957 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3526957 : Nat := 118140960795 + 3526957 * 2 ^ 59
def prefixEnd_3526957 : Nat := 4983230072969 + 3 ^ 40 * 3526957 * 2
def baseEnd_3526957 : Nat := 1207349459159774998811551

theorem tailTrace_3526957 : CollatzResearch.WordTrace tailWord_3526957 prefixEnd_3526957 1207349459159774998811551 := by
  unfold tailWord_3526957
  simp only [CollatzResearch.WordTrace]
  refine ⟨128638689883444620144675125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85759126588963080096450083 128638689883444620144675125)
  ·
    refine ⟨12059877176572933138563293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128638689883444620144675125 12059877176572933138563293)
    ·
      refine ⟨4522453941214849926961235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12059877176572933138563293 4522453941214849926961235)
      ·
        refine ⟨6783680911822274890441853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4522453941214849926961235 6783680911822274890441853)
        ·
          refine ⟨2543880341933353083915695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6783680911822274890441853 2543880341933353083915695)
          ·
            refine ⟨3815820512900029625873543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543880341933353083915695 3815820512900029625873543)
            ·
              refine ⟨5723730769350044438810315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815820512900029625873543 5723730769350044438810315)
              ·
                refine ⟨8585596154025066658215473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723730769350044438810315 8585596154025066658215473)
                ·
                  refine ⟨6439197115518799993661605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8585596154025066658215473 6439197115518799993661605)
                  ·
                    refine ⟨1207349459159774998811551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439197115518799993661605 1207349459159774998811551)
                    ·
                      rfl

theorem cell22_3526957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3526957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526957 prefixEnd_3526957 := by exact prefixLift 3526957
  have htrace : WordTrace (prefixWord ++ tailWord_3526957) baseStart_3526957 baseEnd_3526957 := by
    simpa [prefixWord, tailWord_3526957, baseEnd_3526957] using wordTrace_append hprefix tailTrace_3526957
  have hstable : (prefixWord ++ tailWord_3526957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526957).length < 2 ^ (prefixWord ++ tailWord_3526957).sum := by decide
  have hdescent : baseEnd_3526957 < baseStart_3526957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526970 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_3526970 : Nat := 118140960795 + 3526970 * 2 ^ 59
def prefixEnd_3526970 : Nat := 4983230072969 + 3 ^ 40 * 3526970 * 2
def baseEnd_3526970 : Nat := 1207353909325447298236511

theorem tailTrace_3526970 : CollatzResearch.WordTrace tailWord_3526970 prefixEnd_3526970 1207353909325447298236511 := by
  unfold tailWord_3526970
  simp only [CollatzResearch.WordTrace]
  refine ⟨32159791008099380841224591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85759442688265015576598909 32159791008099380841224591)
  ·
    refine ⟨48239686512149071261836887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32159791008099380841224591 48239686512149071261836887)
    ·
      refine ⟨72359529768223606892755331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48239686512149071261836887 72359529768223606892755331)
      ·
        refine ⟨108539294652335410339132997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72359529768223606892755331 108539294652335410339132997)
        ·
          refine ⟨20351117747312889438587437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108539294652335410339132997 20351117747312889438587437)
          ·
            refine ⟨7631669155242333539470289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20351117747312889438587437 7631669155242333539470289)
            ·
              refine ⟨5723751866431750154602717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7631669155242333539470289 5723751866431750154602717)
              ·
                refine ⟨2146406949911906307976019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5723751866431750154602717 2146406949911906307976019)
                ·
                  refine ⟨3219610424867859461964029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146406949911906307976019 3219610424867859461964029)
                  ·
                    refine ⟨1207353909325447298236511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219610424867859461964029 1207353909325447298236511)
                    ·
                      rfl

theorem cell22_3526970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_3526970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3526970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3526970 prefixEnd_3526970 := by exact prefixLift 3526970
  have htrace : WordTrace (prefixWord ++ tailWord_3526970) baseStart_3526970 baseEnd_3526970 := by
    simpa [prefixWord, tailWord_3526970, baseEnd_3526970] using wordTrace_append hprefix tailTrace_3526970
  have hstable : (prefixWord ++ tailWord_3526970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526970).length < 2 ^ (prefixWord ++ tailWord_3526970).sum := by decide
  have hdescent : baseEnd_3526970 < baseStart_3526970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527006 : List Nat := [4, 4, 2, 1, 2, 1, 2, 6]
def baseStart_3527006 : Nat := 118140960795 + 3527006 * 2 ^ 59
def prefixEnd_3527006 : Nat := 4983230072969 + 3 ^ 40 * 3527006 * 2
def baseEnd_3527006 : Nat := 134151803651239467148489

theorem tailTrace_3527006 : CollatzResearch.WordTrace tailWord_3527006 prefixEnd_3527006 134151803651239467148489 := by
  unfold tailWord_3527006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16080059632533387689151109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85760318040178067675472581 16080059632533387689151109)
  ·
    refine ⟨3015011181100010191715833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16080059632533387689151109 3015011181100010191715833)
    ·
      refine ⟨2261258385825007643786875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3015011181100010191715833 2261258385825007643786875)
      ·
        refine ⟨3391887578737511465680313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261258385825007643786875 3391887578737511465680313)
        ·
          refine ⟨2543915684053133599260235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391887578737511465680313 2543915684053133599260235)
          ·
            refine ⟨3815873526079700398890353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543915684053133599260235 3815873526079700398890353)
            ·
              refine ⟨2861905144559775299167765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815873526079700398890353 2861905144559775299167765)
              ·
                refine ⟨134151803651239467148489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2861905144559775299167765 134151803651239467148489)
                ·
                  rfl

theorem cell22_3527006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_3527006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527006 prefixEnd_3527006 := by exact prefixLift 3527006
  have htrace : WordTrace (prefixWord ++ tailWord_3527006) baseStart_3527006 baseEnd_3527006 := by
    simpa [prefixWord, tailWord_3527006, baseEnd_3527006] using wordTrace_append hprefix tailTrace_3527006
  have hstable : (prefixWord ++ tailWord_3527006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527006).length < 2 ^ (prefixWord ++ tailWord_3527006).sum := by decide
  have hdescent : baseEnd_3527006 < baseStart_3527006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527013 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3527013 : Nat := 118140960795 + 3527013 * 2 ^ 59
def prefixEnd_3527013 : Nat := 4983230072969 + 3 ^ 40 * 3527013 * 2
def baseEnd_3527013 : Nat := 1207368629104209519411379

theorem tailTrace_3527013 : CollatzResearch.WordTrace tailWord_3527013 prefixEnd_3527013 1207368629104209519411379 := by
  unfold tailWord_3527013
  simp only [CollatzResearch.WordTrace]
  refine ⟨128640732371241741708713693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85760488247494494472475795 128640732371241741708713693)
  ·
    refine ⟨48240274639215653140767635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128640732371241741708713693 48240274639215653140767635)
    ·
      refine ⟨72360411958823479711151453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48240274639215653140767635 72360411958823479711151453)
      ·
        refine ⟨27135154484558804891681795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72360411958823479711151453 27135154484558804891681795)
        ·
          refine ⟨40702731726838207337522693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27135154484558804891681795 40702731726838207337522693)
          ·
            refine ⟨7631762198782163875785505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40702731726838207337522693 7631762198782163875785505)
            ·
              refine ⟨5723821649086622906839129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7631762198782163875785505 5723821649086622906839129)
              ·
                refine ⟨4292866236814967180129347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5723821649086622906839129 4292866236814967180129347)
                ·
                  refine ⟨6439299355222450770194021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292866236814967180129347 6439299355222450770194021)
                  ·
                    refine ⟨1207368629104209519411379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439299355222450770194021 1207368629104209519411379)
                    ·
                      rfl

theorem cell22_3527013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3527013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527013 prefixEnd_3527013 := by exact prefixLift 3527013
  have htrace : WordTrace (prefixWord ++ tailWord_3527013) baseStart_3527013 baseEnd_3527013 := by
    simpa [prefixWord, tailWord_3527013, baseEnd_3527013] using wordTrace_append hprefix tailTrace_3527013
  have hstable : (prefixWord ++ tailWord_3527013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527013).length < 2 ^ (prefixWord ++ tailWord_3527013).sum := by decide
  have hdescent : baseEnd_3527013 < baseStart_3527013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527122 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3527122 : Nat := 118140960795 + 3527122 * 2 ^ 59
def prefixEnd_3527122 : Nat := 4983230072969 + 3 ^ 40 * 3527122 * 2
def baseEnd_3527122 : Nat := 1207405942031769568436045

theorem tailTrace_3527122 : CollatzResearch.WordTrace tailWord_3527122 prefixEnd_3527122 1207405942031769568436045 := by
  unfold tailWord_3527122
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161176981961713331107905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85763138618564568882954413 32161176981961713331107905)
  ·
    refine ⟨24120882736471284998330929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32161176981961713331107905 24120882736471284998330929)
    ·
      refine ⟨18090662052353463748748197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24120882736471284998330929 18090662052353463748748197)
      ·
        refine ⟨3391999134816274452890287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18090662052353463748748197 3391999134816274452890287)
        ·
          refine ⟨5087998702224411679335431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391999134816274452890287 5087998702224411679335431)
          ·
            refine ⟨7631998053336617519003147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087998702224411679335431 7631998053336617519003147)
            ·
              refine ⟨11447997080004926278504721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631998053336617519003147 11447997080004926278504721)
              ·
                refine ⟨8585997810003694708878541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447997080004926278504721 8585997810003694708878541)
                ·
                  refine ⟨3219749178751385515829453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8585997810003694708878541 3219749178751385515829453)
                  ·
                    refine ⟨1207405942031769568436045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219749178751385515829453 1207405942031769568436045)
                    ·
                      rfl

theorem cell22_3527122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3527122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527122 prefixEnd_3527122 := by exact prefixLift 3527122
  have htrace : WordTrace (prefixWord ++ tailWord_3527122) baseStart_3527122 baseEnd_3527122 := by
    simpa [prefixWord, tailWord_3527122, baseEnd_3527122] using wordTrace_append hprefix tailTrace_3527122
  have hstable : (prefixWord ++ tailWord_3527122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527122).length < 2 ^ (prefixWord ++ tailWord_3527122).sum := by decide
  have hdescent : baseEnd_3527122 < baseStart_3527122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527148 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_3527148 : Nat := 118140960795 + 3527148 * 2 ^ 59
def prefixEnd_3527148 : Nat := 4983230072969 + 3 ^ 40 * 3527148 * 2
def baseEnd_3527148 : Nat := 1207414842363114167285965

theorem tailTrace_3527148 : CollatzResearch.WordTrace tailWord_3527148 prefixEnd_3527148 1207414842363114167285965 := by
  unfold tailWord_3527148
  simp only [CollatzResearch.WordTrace]
  refine ⟨64322828112876329882439049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85763770817168439843252065 64322828112876329882439049)
  ·
    refine ⟨48242121084657247411829287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64322828112876329882439049 48242121084657247411829287)
    ·
      refine ⟨72363181626985871117743931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48242121084657247411829287 72363181626985871117743931)
      ·
        refine ⟨108544772440478806676615897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72363181626985871117743931 108544772440478806676615897)
        ·
          refine ⟨81408579330359105007461923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108544772440478806676615897 81408579330359105007461923)
          ·
            refine ⟨122112868995538657511192885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81408579330359105007461923 122112868995538657511192885)
            ·
              refine ⟨11448081468331749141674333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122112868995538657511192885 11448081468331749141674333)
              ·
                refine ⟨4293030550624405928127875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11448081468331749141674333 4293030550624405928127875)
                ·
                  refine ⟨6439545825936608892191813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293030550624405928127875 6439545825936608892191813)
                  ·
                    refine ⟨1207414842363114167285965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439545825936608892191813 1207414842363114167285965)
                    ·
                      rfl

theorem cell22_3527148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_3527148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527148 prefixEnd_3527148 := by exact prefixLift 3527148
  have htrace : WordTrace (prefixWord ++ tailWord_3527148) baseStart_3527148 baseEnd_3527148 := by
    simpa [prefixWord, tailWord_3527148, baseEnd_3527148] using wordTrace_append hprefix tailTrace_3527148
  have hstable : (prefixWord ++ tailWord_3527148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527148).length < 2 ^ (prefixWord ++ tailWord_3527148).sum := by decide
  have hdescent : baseEnd_3527148 < baseStart_3527148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527161 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_3527161 : Nat := 118140960795 + 3527161 * 2 ^ 59
def prefixEnd_3527161 : Nat := 4983230072969 + 3 ^ 40 * 3527161 * 2
def baseEnd_3527161 : Nat := 1207419292528786466710925

theorem tailTrace_3527161 : CollatzResearch.WordTrace tailWord_3527161 prefixEnd_3527161 1207419292528786466710925 := by
  unfold tailWord_3527161
  simp only [CollatzResearch.WordTrace]
  refine ⟨128646130374705562985101337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85764086916470375323400891 128646130374705562985101337)
  ·
    refine ⟨96484597781029172238826003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128646130374705562985101337 96484597781029172238826003)
    ·
      refine ⟨144726896671543758358239005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96484597781029172238826003 144726896671543758358239005)
      ·
        refine ⟨54272586251828909384339627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144726896671543758358239005 54272586251828909384339627)
        ·
          refine ⟨81408879377743364076509441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54272586251828909384339627 81408879377743364076509441)
          ·
            refine ⟨61056659533307523057382081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81408879377743364076509441 61056659533307523057382081)
            ·
              refine ⟨45792494649980642293036561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61056659533307523057382081 45792494649980642293036561)
              ·
                refine ⟨34344370987485481719777421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45792494649980642293036561 34344370987485481719777421)
                ·
                  refine ⟨12879139120307055644916533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34344370987485481719777421 12879139120307055644916533)
                  ·
                    refine ⟨1207419292528786466710925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12879139120307055644916533 1207419292528786466710925)
                    ·
                      rfl

theorem cell22_3527161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_3527161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527161 prefixEnd_3527161 := by exact prefixLift 3527161
  have htrace : WordTrace (prefixWord ++ tailWord_3527161) baseStart_3527161 baseEnd_3527161 := by
    simpa [prefixWord, tailWord_3527161, baseEnd_3527161] using wordTrace_append hprefix tailTrace_3527161
  have hstable : (prefixWord ++ tailWord_3527161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527161).length < 2 ^ (prefixWord ++ tailWord_3527161).sum := by decide
  have hdescent : baseEnd_3527161 < baseStart_3527161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527197 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 4]
def baseStart_3527197 : Nat := 118140960795 + 3527197 * 2 ^ 59
def prefixEnd_3527197 : Nat := 4983230072969 + 3 ^ 40 * 3527197 * 2
def baseEnd_3527197 : Nat := 402477205354831457603605

theorem tailTrace_3527197 : CollatzResearch.WordTrace tailWord_3527197 prefixEnd_3527197 402477205354831457603605 := by
  unfold tailWord_3527197
  simp only [CollatzResearch.WordTrace]
  refine ⟨128647443402575141133411845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85764962268383427422274563 128647443402575141133411845)
  ·
    refine ⟨24121395637982838962514721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128647443402575141133411845 24121395637982838962514721)
    ·
      refine ⟨18091046728487129221886041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24121395637982838962514721 18091046728487129221886041)
      ·
        refine ⟨13568285046365346916414531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18091046728487129221886041 13568285046365346916414531)
        ·
          refine ⟨20352427569548020374621797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13568285046365346916414531 20352427569548020374621797)
          ·
            refine ⟨3816080169290253820241587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20352427569548020374621797 3816080169290253820241587)
            ·
              refine ⟨5724120253935380730362381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816080169290253820241587 5724120253935380730362381)
              ·
                refine ⟨2146545095225767773885893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5724120253935380730362381 2146545095225767773885893)
                ·
                  refine ⟨402477205354831457603605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146545095225767773885893 402477205354831457603605)
                  ·
                    rfl

theorem cell22_3527197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_3527197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527197 prefixEnd_3527197 := by exact prefixLift 3527197
  have htrace : WordTrace (prefixWord ++ tailWord_3527197) baseStart_3527197 baseEnd_3527197 := by
    simpa [prefixWord, tailWord_3527197, baseEnd_3527197] using wordTrace_append hprefix tailTrace_3527197
  have hstable : (prefixWord ++ tailWord_3527197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527197).length < 2 ^ (prefixWord ++ tailWord_3527197).sum := by decide
  have hdescent : baseEnd_3527197 < baseStart_3527197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527208 : List Nat := [2, 1, 5, 2, 1, 1, 10]
def baseStart_3527208 : Nat := 118140960795 + 3527208 * 2 ^ 59
def prefixEnd_3527208 : Nat := 4983230072969 + 3 ^ 40 * 3527208 * 2
def baseEnd_3527208 : Nat := 44719828947751630029103

theorem tailTrace_3527208 : CollatzResearch.WordTrace tailWord_3527208 prefixEnd_3527208 44719828947751630029103 := by
  unfold tailWord_3527208
  simp only [CollatzResearch.WordTrace]
  refine ⟨64323922302767645006031139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85765229737023526674708185 64323922302767645006031139)
  ·
    refine ⟨96485883454151467509046709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64323922302767645006031139 96485883454151467509046709)
    ·
      refine ⟨9045551573826700078973129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96485883454151467509046709 9045551573826700078973129)
      ·
        refine ⟨6784163680370025059229847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9045551573826700078973129 6784163680370025059229847)
        ·
          refine ⟨10176245520555037588844771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6784163680370025059229847 10176245520555037588844771)
          ·
            refine ⟨15264368280832556383267157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10176245520555037588844771 15264368280832556383267157)
            ·
              refine ⟨44719828947751630029103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15264368280832556383267157 44719828947751630029103)
              ·
                rfl

theorem cell22_3527208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 10].length) (baseStart_3527208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527208 prefixEnd_3527208 := by exact prefixLift 3527208
  have htrace : WordTrace (prefixWord ++ tailWord_3527208) baseStart_3527208 baseEnd_3527208 := by
    simpa [prefixWord, tailWord_3527208, baseEnd_3527208] using wordTrace_append hprefix tailTrace_3527208
  have hstable : (prefixWord ++ tailWord_3527208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527208).length < 2 ^ (prefixWord ++ tailWord_3527208).sum := by decide
  have hdescent : baseEnd_3527208 < baseStart_3527208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527210 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3527210 : Nat := 118140960795 + 3527210 * 2 ^ 59
def prefixEnd_3527210 : Nat := 4983230072969 + 3 ^ 40 * 3527210 * 2
def baseEnd_3527210 : Nat := 1207436066230166672235775

theorem tailTrace_3527210 : CollatzResearch.WordTrace tailWord_3527210 prefixEnd_3527210 1207436066230166672235775 := by
  unfold tailWord_3527210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161979387882011088408771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85765278367685362902423389 32161979387882011088408771)
  ·
    refine ⟨48242969081823016632613157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32161979387882011088408771 48242969081823016632613157)
    ·
      refine ⟨9045556702841815618614967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48242969081823016632613157 9045556702841815618614967)
      ·
        refine ⟨13568335054262723427922451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045556702841815618614967 13568335054262723427922451)
        ·
          refine ⟨20352502581394085141883677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13568335054262723427922451 20352502581394085141883677)
          ·
            refine ⟨7632188468022781928206379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20352502581394085141883677 7632188468022781928206379)
            ·
              refine ⟨11448282702034172892309569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632188468022781928206379 11448282702034172892309569)
              ·
                refine ⟨8586212026525629669232177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11448282702034172892309569 8586212026525629669232177)
                ·
                  refine ⟨6439659019894222251924133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8586212026525629669232177 6439659019894222251924133)
                  ·
                    refine ⟨1207436066230166672235775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439659019894222251924133 1207436066230166672235775)
                    ·
                      rfl

theorem cell22_3527210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3527210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527210 prefixEnd_3527210 := by exact prefixLift 3527210
  have htrace : WordTrace (prefixWord ++ tailWord_3527210) baseStart_3527210 baseEnd_3527210 := by
    simpa [prefixWord, tailWord_3527210, baseEnd_3527210] using wordTrace_append hprefix tailTrace_3527210
  have hstable : (prefixWord ++ tailWord_3527210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527210).length < 2 ^ (prefixWord ++ tailWord_3527210).sum := by decide
  have hdescent : baseEnd_3527210 < baseStart_3527210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527214 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_3527214 : Nat := 118140960795 + 3527214 * 2 ^ 59
def prefixEnd_3527214 : Nat := 4983230072969 + 3 ^ 40 * 3527214 * 2
def baseEnd_3527214 : Nat := 402479145170637331711921

theorem tailTrace_3527214 : CollatzResearch.WordTrace tailWord_3527214 prefixEnd_3527214 402479145170637331711921 := by
  unfold tailWord_3527214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16081007930439194129597587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85765375629009035357853797 16081007930439194129597587)
  ·
    refine ⟨24121511895658791194396381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16081007930439194129597587 24121511895658791194396381)
    ·
      refine ⟨9045566960872046697898643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24121511895658791194396381 9045566960872046697898643)
      ·
        refine ⟨13568350441308070046847965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045566960872046697898643 13568350441308070046847965)
        ·
          refine ⟨5088131415490526267567987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13568350441308070046847965 5088131415490526267567987)
          ·
            refine ⟨7632197123235789401351981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088131415490526267567987 7632197123235789401351981)
            ·
              refine ⟨2862073921213421025506993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7632197123235789401351981 2862073921213421025506993)
              ·
                refine ⟨2146555440910065769130245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862073921213421025506993 2146555440910065769130245)
                ·
                  refine ⟨402479145170637331711921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146555440910065769130245 402479145170637331711921)
                  ·
                    rfl

theorem cell22_3527214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_3527214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527214 prefixEnd_3527214 := by exact prefixLift 3527214
  have htrace : WordTrace (prefixWord ++ tailWord_3527214) baseStart_3527214 baseEnd_3527214 := by
    simpa [prefixWord, tailWord_3527214, baseEnd_3527214] using wordTrace_append hprefix tailTrace_3527214
  have hstable : (prefixWord ++ tailWord_3527214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527214).length < 2 ^ (prefixWord ++ tailWord_3527214).sum := by decide
  have hdescent : baseEnd_3527214 < baseStart_3527214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527229 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_3527229 : Nat := 118140960795 + 3527229 * 2 ^ 59
def prefixEnd_3527229 : Nat := 4983230072969 + 3 ^ 40 * 3527229 * 2
def baseEnd_3527229 : Nat := 1207442570318456956010717

theorem tailTrace_3527229 : CollatzResearch.WordTrace tailWord_3527229 prefixEnd_3527229 1207442570318456956010717 := by
  unfold tailWord_3527229
  simp only [CollatzResearch.WordTrace]
  refine ⟨128648610538459210598576741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85765740358972807065717827 128648610538459210598576741)
  ·
    refine ⟨24121614475961101987233139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128648610538459210598576741 24121614475961101987233139)
    ·
      refine ⟨36182421713941652980849709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24121614475961101987233139 36182421713941652980849709)
      ·
        refine ⟨13568408142728119867818641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36182421713941652980849709 13568408142728119867818641)
        ·
          refine ⟨10176306107046089900863981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13568408142728119867818641 10176306107046089900863981)
          ·
            refine ⟨3816114790142283712823993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10176306107046089900863981 3816114790142283712823993)
            ·
              refine ⟨2862086092606712784617995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3816114790142283712823993 2862086092606712784617995)
              ·
                refine ⟨4293129138910069176926993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862086092606712784617995 4293129138910069176926993)
                ·
                  refine ⟨3219846854182551882695245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4293129138910069176926993 3219846854182551882695245)
                  ·
                    refine ⟨1207442570318456956010717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3219846854182551882695245 1207442570318456956010717)
                    ·
                      rfl

theorem cell22_3527229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_3527229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527229 prefixEnd_3527229 := by exact prefixLift 3527229
  have htrace : WordTrace (prefixWord ++ tailWord_3527229) baseStart_3527229 baseEnd_3527229 := by
    simpa [prefixWord, tailWord_3527229, baseEnd_3527229] using wordTrace_append hprefix tailTrace_3527229
  have hstable : (prefixWord ++ tailWord_3527229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527229).length < 2 ^ (prefixWord ++ tailWord_3527229).sum := by decide
  have hdescent : baseEnd_3527229 < baseStart_3527229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527268 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_3527268 : Nat := 118140960795 + 3527268 * 2 ^ 59
def prefixEnd_3527268 : Nat := 4983230072969 + 3 ^ 40 * 3527268 * 2
def baseEnd_3527268 : Nat := 1207455920815473854285597

theorem tailTrace_3527268 : CollatzResearch.WordTrace tailWord_3527268 prefixEnd_3527268 1207455920815473854285597 := by
  unfold tailWord_3527268
  simp only [CollatzResearch.WordTrace]
  refine ⟨64325016492658960129623229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85766688656878613506164305 64325016492658960129623229)
  ·
    refine ⟨24121881184747110048608711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64325016492658960129623229 24121881184747110048608711)
    ·
      refine ⟨36182821777120665072913067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24121881184747110048608711 36182821777120665072913067)
      ·
        refine ⟨54274232665680997609369601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36182821777120665072913067 54274232665680997609369601)
        ·
          refine ⟨40705674499260748207027201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54274232665680997609369601 40705674499260748207027201)
          ·
            refine ⟨30529255874445561155270401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40705674499260748207027201 30529255874445561155270401)
            ·
              refine ⟨22896941905834170866452801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30529255874445561155270401 22896941905834170866452801)
              ·
                refine ⟨17172706429375628149839601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22896941905834170866452801 17172706429375628149839601)
                ·
                  refine ⟨12879529822031721112379701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17172706429375628149839601 12879529822031721112379701)
                  ·
                    refine ⟨1207455920815473854285597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12879529822031721112379701 1207455920815473854285597)
                    ·
                      rfl

theorem cell22_3527268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_3527268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527268 prefixEnd_3527268 := by exact prefixLift 3527268
  have htrace : WordTrace (prefixWord ++ tailWord_3527268) baseStart_3527268 baseEnd_3527268 := by
    simpa [prefixWord, tailWord_3527268, baseEnd_3527268] using wordTrace_append hprefix tailTrace_3527268
  have hstable : (prefixWord ++ tailWord_3527268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527268).length < 2 ^ (prefixWord ++ tailWord_3527268).sum := by decide
  have hdescent : baseEnd_3527268 < baseStart_3527268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527300 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3527300 : Nat := 118140960795 + 3527300 * 2 ^ 59
def prefixEnd_3527300 : Nat := 4983230072969 + 3 ^ 40 * 3527300 * 2
def baseEnd_3527300 : Nat := 1207466875069436437485499

theorem tailTrace_3527300 : CollatzResearch.WordTrace tailWord_3527300 prefixEnd_3527300 1207466875069436437485499 := by
  unfold tailWord_3527300
  simp only [CollatzResearch.WordTrace]
  refine ⟨64325600060600994862205677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85767466747467993149607569 64325600060600994862205677)
  ·
    refine ⟨24122100022725373073327129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64325600060600994862205677 24122100022725373073327129)
    ·
      refine ⟨18091575017044029804995347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24122100022725373073327129 18091575017044029804995347)
      ·
        refine ⟨27137362525566044707493021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18091575017044029804995347 27137362525566044707493021)
        ·
          refine ⟨10176510947087266765309883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27137362525566044707493021 10176510947087266765309883)
          ·
            refine ⟨15264766420630900147964825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10176510947087266765309883 15264766420630900147964825)
            ·
              refine ⟨11448574815473175110973619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15264766420630900147964825 11448574815473175110973619)
              ·
                refine ⟨17172862223209762666460429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11448574815473175110973619 17172862223209762666460429)
                ·
                  refine ⟨6439823333703660999922661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17172862223209762666460429 6439823333703660999922661)
                  ·
                    refine ⟨1207466875069436437485499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439823333703660999922661 1207466875069436437485499)
                    ·
                      rfl

theorem cell22_3527300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3527300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527300 prefixEnd_3527300 := by exact prefixLift 3527300
  have htrace : WordTrace (prefixWord ++ tailWord_3527300) baseStart_3527300 baseEnd_3527300 := by
    simpa [prefixWord, tailWord_3527300, baseEnd_3527300] using wordTrace_append hprefix tailTrace_3527300
  have hstable : (prefixWord ++ tailWord_3527300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527300).length < 2 ^ (prefixWord ++ tailWord_3527300).sum := by decide
  have hdescent : baseEnd_3527300 < baseStart_3527300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527360 : List Nat := [2, 1, 1, 2, 4, 2, 4, 6]
def baseStart_3527360 : Nat := 118140960795 + 3527360 * 2 ^ 59
def prefixEnd_3527360 : Nat := 4983230072969 + 3 ^ 40 * 3527360 * 2
def baseEnd_3527360 : Nat := 134165268255068475665035

theorem tailTrace_3527360 : CollatzResearch.WordTrace tailWord_3527360 prefixEnd_3527360 134165268255068475665035 := by
  unfold tailWord_3527360
  simp only [CollatzResearch.WordTrace]
  refine ⟨64326694250492309985797767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85768925667323079981063689 64326694250492309985797767)
  ·
    refine ⟨96490041375738464978696651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64326694250492309985797767 96490041375738464978696651)
    ·
      refine ⟨144735062063607697468044977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96490041375738464978696651 144735062063607697468044977)
      ·
        refine ⟨108551296547705773101033733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144735062063607697468044977 108551296547705773101033733)
        ·
          refine ⟨20353368102694832456443825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108551296547705773101033733 20353368102694832456443825)
          ·
            refine ⟨15265026077021124342332869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20353368102694832456443825 15265026077021124342332869)
            ·
              refine ⟨2862192389441460814187413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15265026077021124342332869 2862192389441460814187413)
              ·
                refine ⟨134165268255068475665035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2862192389441460814187413 134165268255068475665035)
                ·
                  rfl

theorem cell22_3527360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_3527360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527360 prefixEnd_3527360 := by exact prefixLift 3527360
  have htrace : WordTrace (prefixWord ++ tailWord_3527360) baseStart_3527360 baseEnd_3527360 := by
    simpa [prefixWord, tailWord_3527360, baseEnd_3527360] using wordTrace_append hprefix tailTrace_3527360
  have hstable : (prefixWord ++ tailWord_3527360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527360).length < 2 ^ (prefixWord ++ tailWord_3527360).sum := by decide
  have hdescent : baseEnd_3527360 < baseStart_3527360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527403 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_3527403 : Nat := 118140960795 + 3527403 * 2 ^ 59
def prefixEnd_3527403 : Nat := 4983230072969 + 3 ^ 40 * 3527403 * 2
def baseEnd_3527403 : Nat := 1207502134074378502160183

theorem tailTrace_3527403 : CollatzResearch.WordTrace tailWord_3527403 prefixEnd_3527403 1207502134074378502160183 := by
  unfold tailWord_3527403
  simp only [CollatzResearch.WordTrace]
  refine ⟨128654956839828838315410863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85769971226552558876940575 128654956839828838315410863)
  ·
    refine ⟨192982435259743257473116295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128654956839828838315410863 192982435259743257473116295)
    ·
      refine ⟨289473652889614886209674443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192982435259743257473116295 289473652889614886209674443)
      ·
        refine ⟨434210479334422329314511665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289473652889614886209674443 434210479334422329314511665)
        ·
          refine ⟨325657859500816746985883749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434210479334422329314511665 325657859500816746985883749)
          ·
            refine ⟨61060848656403140059853203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325657859500816746985883749 61060848656403140059853203)
            ·
              refine ⟨91591272984604710089779805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61060848656403140059853203 91591272984604710089779805)
              ·
                refine ⟨34346727369226766283667427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91591272984604710089779805 34346727369226766283667427)
                ·
                  refine ⟨51520091053840149425501141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34346727369226766283667427 51520091053840149425501141)
                  ·
                    refine ⟨1207502134074378502160183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51520091053840149425501141 1207502134074378502160183)
                    ·
                      rfl

theorem cell22_3527403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_3527403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527403 prefixEnd_3527403 := by exact prefixLift 3527403
  have htrace : WordTrace (prefixWord ++ tailWord_3527403) baseStart_3527403 baseEnd_3527403 := by
    simpa [prefixWord, tailWord_3527403, baseEnd_3527403] using wordTrace_append hprefix tailTrace_3527403
  have hstable : (prefixWord ++ tailWord_3527403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527403).length < 2 ^ (prefixWord ++ tailWord_3527403).sum := by decide
  have hdescent : baseEnd_3527403 < baseStart_3527403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527450 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_3527450 : Nat := 118140960795 + 3527450 * 2 ^ 59
def prefixEnd_3527450 : Nat := 4983230072969 + 3 ^ 40 * 3527450 * 2
def baseEnd_3527450 : Nat := 402506074378295348745013

theorem tailTrace_3527450 : CollatzResearch.WordTrace tailWord_3527450 prefixEnd_3527450 402506074378295348745013 := by
  unfold tailWord_3527450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32164167767664641335592951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85771114047105710228247869 32164167767664641335592951)
  ·
    refine ⟨48246251651496962003389427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32164167767664641335592951 48246251651496962003389427)
    ·
      refine ⟨72369377477245443005084141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48246251651496962003389427 72369377477245443005084141)
      ·
        refine ⟨27138516553967041126906553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72369377477245443005084141 27138516553967041126906553)
        ·
          refine ⟨20353887415475280845179915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27138516553967041126906553 20353887415475280845179915)
          ·
            refine ⟨30530831123212921267769873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20353887415475280845179915 30530831123212921267769873)
            ·
              refine ⟨22898123342409690950827405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30530831123212921267769873 22898123342409690950827405)
              ·
                refine ⟨8586796253403634106560277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22898123342409690950827405 8586796253403634106560277)
                ·
                  refine ⟨402506074378295348745013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8586796253403634106560277 402506074378295348745013)
                  ·
                    rfl

theorem cell22_3527450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_3527450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527450 prefixEnd_3527450 := by exact prefixLift 3527450
  have htrace : WordTrace (prefixWord ++ tailWord_3527450) baseStart_3527450 baseEnd_3527450 := by
    simpa [prefixWord, tailWord_3527450, baseEnd_3527450] using wordTrace_append hprefix tailTrace_3527450
  have hstable : (prefixWord ++ tailWord_3527450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527450).length < 2 ^ (prefixWord ++ tailWord_3527450).sum := by decide
  have hdescent : baseEnd_3527450 < baseStart_3527450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527480 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_3527480 : Nat := 118140960795 + 3527480 * 2 ^ 59
def prefixEnd_3527480 : Nat := 4983230072969 + 3 ^ 40 * 3527480 * 2
def baseEnd_3527480 : Nat := 1207528492747975967984947

theorem tailTrace_3527480 : CollatzResearch.WordTrace tailWord_3527480 prefixEnd_3527480 1207528492747975967984947 := by
  unfold tailWord_3527480
  simp only [CollatzResearch.WordTrace]
  refine ⟨64328882630274940232981947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85771843507033253643975929 64328882630274940232981947)
  ·
    refine ⟨96493323945412410349472921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64328882630274940232981947 96493323945412410349472921)
    ·
      refine ⟨72369992959059307762104691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96493323945412410349472921 72369992959059307762104691)
      ·
        refine ⟨108554989438588961643157037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72369992959059307762104691 108554989438588961643157037)
        ·
          refine ⟨40708121039470860616183889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108554989438588961643157037 40708121039470860616183889)
          ·
            refine ⟨30531090779603145462137917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40708121039470860616183889 30531090779603145462137917)
            ·
              refine ⟨11449159042351179548301719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30531090779603145462137917 11449159042351179548301719)
              ·
                refine ⟨17173738563526769322452579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11449159042351179548301719 17173738563526769322452579)
                ·
                  refine ⟨25760607845290153983678869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17173738563526769322452579 25760607845290153983678869)
                  ·
                    refine ⟨1207528492747975967984947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25760607845290153983678869 1207528492747975967984947)
                    ·
                      rfl

theorem cell22_3527480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_3527480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527480 prefixEnd_3527480 := by exact prefixLift 3527480
  have htrace : WordTrace (prefixWord ++ tailWord_3527480) baseStart_3527480 baseEnd_3527480 := by
    simpa [prefixWord, tailWord_3527480, baseEnd_3527480] using wordTrace_append hprefix tailTrace_3527480
  have hstable : (prefixWord ++ tailWord_3527480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527480).length < 2 ^ (prefixWord ++ tailWord_3527480).sum := by decide
  have hdescent : baseEnd_3527480 < baseStart_3527480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527525 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3527525 : Nat := 118140960795 + 3527525 * 2 ^ 59
def prefixEnd_3527525 : Nat := 4983230072969 + 3 ^ 40 * 3527525 * 2
def baseEnd_3527525 : Nat := 1207543897167610850609809

theorem tailTrace_3527525 : CollatzResearch.WordTrace tailWord_3527525 prefixEnd_3527525 1207543897167610850609809 := by
  unfold tailWord_3527525
  simp only [CollatzResearch.WordTrace]
  refine ⟨128659406545386853151352029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85772937696924568767568019 128659406545386853151352029)
  ·
    refine ⟨48247277454520069931757011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128659406545386853151352029 48247277454520069931757011)
    ·
      refine ⟨72370916181780104897635517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48247277454520069931757011 72370916181780104897635517)
      ·
        refine ⟨27139093568167539336613319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72370916181780104897635517 27139093568167539336613319)
        ·
          refine ⟨40708640352251309004919979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27139093568167539336613319 40708640352251309004919979)
          ·
            refine ⟨61062960528376963507379969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40708640352251309004919979 61062960528376963507379969)
            ·
              refine ⟨45797220396282722630534977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61062960528376963507379969 45797220396282722630534977)
              ·
                refine ⟨34347915297212041972901233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45797220396282722630534977 34347915297212041972901233)
                ·
                  refine ⟨25760936472909031479675925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34347915297212041972901233 25760936472909031479675925)
                  ·
                    refine ⟨1207543897167610850609809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25760936472909031479675925 1207543897167610850609809)
                    ·
                      rfl

theorem cell22_3527525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3527525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527525 prefixEnd_3527525 := by exact prefixLift 3527525
  have htrace : WordTrace (prefixWord ++ tailWord_3527525) baseStart_3527525 baseEnd_3527525 := by
    simpa [prefixWord, tailWord_3527525, baseEnd_3527525] using wordTrace_append hprefix tailTrace_3527525
  have hstable : (prefixWord ++ tailWord_3527525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527525).length < 2 ^ (prefixWord ++ tailWord_3527525).sum := by decide
  have hdescent : baseEnd_3527525 < baseStart_3527525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527544 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 1, 3]
def baseStart_3527544 : Nat := 118140960795 + 3527544 * 2 ^ 59
def prefixEnd_3527544 : Nat := 4983230072969 + 3 ^ 40 * 3527544 * 2
def baseEnd_3527544 : Nat := 1207550401255901134384751

theorem tailTrace_3527544 : CollatzResearch.WordTrace tailWord_3527544 prefixEnd_3527544 1207550401255901134384751 := by
  unfold tailWord_3527544
  simp only [CollatzResearch.WordTrace]
  refine ⟨64330049766159009698146843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85773399688212012930862457 64330049766159009698146843)
  ·
    refine ⟨96495074649238514547220265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64330049766159009698146843 96495074649238514547220265)
    ·
      refine ⟨72371305986928885910415199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96495074649238514547220265 72371305986928885910415199)
      ·
        refine ⟨108556958980393328865622799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72371305986928885910415199 108556958980393328865622799)
        ·
          refine ⟨162835438470589993298434199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108556958980393328865622799 162835438470589993298434199)
          ·
            refine ⟨244253157705884989947651299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162835438470589993298434199 244253157705884989947651299)
            ·
              refine ⟨366379736558827484921476949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244253157705884989947651299 366379736558827484921476949)
              ·
                refine ⟨2146756268899379794461779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 366379736558827484921476949 2146756268899379794461779)
                ·
                  refine ⟨3220134403349069691692669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146756268899379794461779 3220134403349069691692669)
                  ·
                    refine ⟨1207550401255901134384751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220134403349069691692669 1207550401255901134384751)
                    ·
                      rfl

theorem cell22_3527544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_3527544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527544 prefixEnd_3527544 := by exact prefixLift 3527544
  have htrace : WordTrace (prefixWord ++ tailWord_3527544) baseStart_3527544 baseEnd_3527544 := by
    simpa [prefixWord, tailWord_3527544, baseEnd_3527544] using wordTrace_append hprefix tailTrace_3527544
  have hstable : (prefixWord ++ tailWord_3527544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527544).length < 2 ^ (prefixWord ++ tailWord_3527544).sum := by decide
  have hdescent : baseEnd_3527544 < baseStart_3527544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527572 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3527572 : Nat := 118140960795 + 3527572 * 2 ^ 59
def prefixEnd_3527572 : Nat := 4983230072969 + 3 ^ 40 * 3527572 * 2
def baseEnd_3527572 : Nat := 1207559986228118394684665

theorem tailTrace_3527572 : CollatzResearch.WordTrace tailWord_3527572 prefixEnd_3527572 1207559986228118394684665 := by
  unfold tailWord_3527572
  simp only [CollatzResearch.WordTrace]
  refine ⟨64330560388108290089156485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85774080517477720118875313 64330560388108290089156485)
  ·
    refine ⟨12061980072770304391716841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64330560388108290089156485 12061980072770304391716841)
    ·
      refine ⟨9046485054577728293787631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12061980072770304391716841 9046485054577728293787631)
      ·
        refine ⟨13569727581866592440681447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9046485054577728293787631 13569727581866592440681447)
        ·
          refine ⟨20354591372799888661022171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13569727581866592440681447 20354591372799888661022171)
          ·
            refine ⟨30531887059199832991533257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20354591372799888661022171 30531887059199832991533257)
            ·
              refine ⟨22898915294399874743649943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30531887059199832991533257 22898915294399874743649943)
              ·
                refine ⟨34348372941599812115474915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22898915294399874743649943 34348372941599812115474915)
                ·
                  refine ⟨51522559412399718173212373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34348372941599812115474915 51522559412399718173212373)
                  ·
                    refine ⟨1207559986228118394684665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51522559412399718173212373 1207559986228118394684665)
                    ·
                      rfl

theorem cell22_3527572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3527572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527572 prefixEnd_3527572 := by exact prefixLift 3527572
  have htrace : WordTrace (prefixWord ++ tailWord_3527572) baseStart_3527572 baseEnd_3527572 := by
    simpa [prefixWord, tailWord_3527572, baseEnd_3527572] using wordTrace_append hprefix tailTrace_3527572
  have hstable : (prefixWord ++ tailWord_3527572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527572).length < 2 ^ (prefixWord ++ tailWord_3527572).sum := by decide
  have hdescent : baseEnd_3527572 < baseStart_3527572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527634 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3527634 : Nat := 118140960795 + 3527634 * 2 ^ 59
def prefixEnd_3527634 : Nat := 4983230072969 + 3 ^ 40 * 3527634 * 2
def baseEnd_3527634 : Nat := 1207581210095170899634475

theorem tailTrace_3527634 : CollatzResearch.WordTrace tailWord_3527634 prefixEnd_3527634 1207581210095170899634475 := by
  unfold tailWord_3527634
  simp only [CollatzResearch.WordTrace]
  refine ⟨32165845525497991191767489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85775588067994643178046637 32165845525497991191767489)
  ·
    refine ⟨24124384144123493393825617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32165845525497991191767489 24124384144123493393825617)
    ·
      refine ⟨18093288108092620045369213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24124384144123493393825617 18093288108092620045369213)
      ·
        refine ⟨6784983040534732517013455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18093288108092620045369213 6784983040534732517013455)
        ·
          refine ⟨10177474560802098775520183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6784983040534732517013455 10177474560802098775520183)
          ·
            refine ⟨15266211841203148163280275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10177474560802098775520183 15266211841203148163280275)
            ·
              refine ⟨22899317761804722244920413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266211841203148163280275 22899317761804722244920413)
              ·
                refine ⟨8587244160676770841845155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22899317761804722244920413 8587244160676770841845155)
                ·
                  refine ⟨12880866241015156262767733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587244160676770841845155 12880866241015156262767733)
                  ·
                    refine ⟨1207581210095170899634475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12880866241015156262767733 1207581210095170899634475)
                    ·
                      rfl

theorem cell22_3527634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3527634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527634 prefixEnd_3527634 := by exact prefixLift 3527634
  have htrace : WordTrace (prefixWord ++ tailWord_3527634) baseStart_3527634 baseEnd_3527634 := by
    simpa [prefixWord, tailWord_3527634, baseEnd_3527634] using wordTrace_append hprefix tailTrace_3527634
  have hstable : (prefixWord ++ tailWord_3527634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527634).length < 2 ^ (prefixWord ++ tailWord_3527634).sum := by decide
  have hdescent : baseEnd_3527634 < baseStart_3527634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527653 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 4]
def baseStart_3527653 : Nat := 118140960795 + 3527653 * 2 ^ 59
def prefixEnd_3527653 : Nat := 4983230072969 + 3 ^ 40 * 3527653 * 2
def baseEnd_3527653 : Nat := 402529238061153727803139

theorem tailTrace_3527653 : CollatzResearch.WordTrace tailWord_3527653 prefixEnd_3527653 402529238061153727803139 := by
  unfold tailWord_3527653
  simp only [CollatzResearch.WordTrace]
  refine ⟨128664075088923131012011613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85776050059282087341341075 128664075088923131012011613)
  ·
    refine ⟨48249028158346174129504355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128664075088923131012011613 48249028158346174129504355)
    ·
      refine ⟨72373542237519261194256533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48249028158346174129504355 72373542237519261194256533)
      ·
        refine ⟨3392509792383715368480775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72373542237519261194256533 3392509792383715368480775)
        ·
          refine ⟨5088764688575573052721163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3392509792383715368480775 5088764688575573052721163)
          ·
            refine ⟨7633147032863359579081745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088764688575573052721163 7633147032863359579081745)
            ·
              refine ⟨5724860274647519684311309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7633147032863359579081745 5724860274647519684311309)
              ·
                refine ⟨2146822602992819881616741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5724860274647519684311309 2146822602992819881616741)
                ·
                  refine ⟨402529238061153727803139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146822602992819881616741 402529238061153727803139)
                  ·
                    rfl

theorem cell22_3527653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_3527653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527653 prefixEnd_3527653 := by exact prefixLift 3527653
  have htrace : WordTrace (prefixWord ++ tailWord_3527653) baseStart_3527653 baseEnd_3527653 := by
    simpa [prefixWord, tailWord_3527653, baseEnd_3527653] using wordTrace_append hprefix tailTrace_3527653
  have hstable : (prefixWord ++ tailWord_3527653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527653).length < 2 ^ (prefixWord ++ tailWord_3527653).sum := by decide
  have hdescent : baseEnd_3527653 < baseStart_3527653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527698 : List Nat := [3, 2, 5, 1, 1, 1, 1, 8]
def baseStart_3527698 : Nat := 118140960795 + 3527698 * 2 ^ 59
def prefixEnd_3527698 : Nat := 4983230072969 + 3 ^ 40 * 3527698 * 2
def baseEnd_3527698 : Nat := 134178124289232896226031

theorem tailTrace_3527698 : CollatzResearch.WordTrace tailWord_3527698 prefixEnd_3527698 134178124289232896226031 := by
  unfold tailWord_3527698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32166429093440025924349937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85777144249173402464933165 32166429093440025924349937)
  ·
    refine ⟨24124821820080019443262453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32166429093440025924349937 24124821820080019443262453)
    ·
      refine ⟨2261702045632501822805855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24124821820080019443262453 2261702045632501822805855)
      ·
        refine ⟨3392553068448752734208783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261702045632501822805855 3392553068448752734208783)
        ·
          refine ⟨5088829602673129101313175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3392553068448752734208783 5088829602673129101313175)
          ·
            refine ⟨7633244404009693651969763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088829602673129101313175 7633244404009693651969763)
            ·
              refine ⟨11449866606014540477954645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7633244404009693651969763 11449866606014540477954645)
              ·
                refine ⟨134178124289232896226031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11449866606014540477954645 134178124289232896226031)
                ·
                  rfl

theorem cell22_3527698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_3527698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527698 prefixEnd_3527698 := by exact prefixLift 3527698
  have htrace : WordTrace (prefixWord ++ tailWord_3527698) baseStart_3527698 baseEnd_3527698 := by
    simpa [prefixWord, tailWord_3527698, baseEnd_3527698] using wordTrace_append hprefix tailTrace_3527698
  have hstable : (prefixWord ++ tailWord_3527698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527698).length < 2 ^ (prefixWord ++ tailWord_3527698).sum := by decide
  have hdescent : baseEnd_3527698 < baseStart_3527698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527713 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 1, 3]
def baseStart_3527713 : Nat := 118140960795 + 3527713 * 2 ^ 59
def prefixEnd_3527713 : Nat := 4983230072969 + 3 ^ 40 * 3527713 * 2
def baseEnd_3527713 : Nat := 1207608253409641026909233

theorem tailTrace_3527713 : CollatzResearch.WordTrace tailWord_3527713 prefixEnd_3527713 1207608253409641026909233 := by
  unfold tailWord_3527713
  simp only [CollatzResearch.WordTrace]
  refine ⟨128666263468705761259195793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85777508979137174172797195 128666263468705761259195793)
  ·
    refine ⟨96499697601529320944396845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128666263468705761259195793 96499697601529320944396845)
    ·
      refine ⟨36187386600573495354148817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96499697601529320944396845 36187386600573495354148817)
      ·
        refine ⟨27140539950430121515611613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36187386600573495354148817 27140539950430121515611613)
        ·
          refine ⟨10177702481411295568354355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27140539950430121515611613 10177702481411295568354355)
          ·
            refine ⟨15266553722116943352531533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10177702481411295568354355 15266553722116943352531533)
            ·
              refine ⟨5724957645793853757199325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15266553722116943352531533 5724957645793853757199325)
              ·
                refine ⟨2146859117172695158949747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5724957645793853757199325 2146859117172695158949747)
                ·
                  refine ⟨3220288675759042738424621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146859117172695158949747 3220288675759042738424621)
                  ·
                    refine ⟨1207608253409641026909233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220288675759042738424621 1207608253409641026909233)
                    ·
                      rfl

theorem cell22_3527713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_3527713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527713 prefixEnd_3527713 := by exact prefixLift 3527713
  have htrace : WordTrace (prefixWord ++ tailWord_3527713) baseStart_3527713 baseEnd_3527713 := by
    simpa [prefixWord, tailWord_3527713, baseEnd_3527713] using wordTrace_append hprefix tailTrace_3527713
  have hstable : (prefixWord ++ tailWord_3527713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527713).length < 2 ^ (prefixWord ++ tailWord_3527713).sum := by decide
  have hdescent : baseEnd_3527713 < baseStart_3527713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527769 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_3527769 : Nat := 118140960795 + 3527769 * 2 ^ 59
def prefixEnd_3527769 : Nat := 4983230072969 + 3 ^ 40 * 3527769 * 2
def baseEnd_3527769 : Nat := 1207627423354075547509061

theorem tailTrace_3527769 : CollatzResearch.WordTrace tailWord_3527769 prefixEnd_3527769 1207627423354075547509061 := by
  unfold tailWord_3527769
  simp only [CollatzResearch.WordTrace]
  refine ⟨128668305956502882823234361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85778870637668588548822907 128668305956502882823234361)
  ·
    refine ⟨96501229467377162117425771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128668305956502882823234361 96501229467377162117425771)
    ·
      refine ⟨144751844201065743176138657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96501229467377162117425771 144751844201065743176138657)
      ·
        refine ⟨108563883150799307382103993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144751844201065743176138657 108563883150799307382103993)
        ·
          refine ⟨81422912363099480536577995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108563883150799307382103993 81422912363099480536577995)
          ·
            refine ⟨122134368544649220804866993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81422912363099480536577995 122134368544649220804866993)
            ·
              refine ⟨91600776408486915603650245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122134368544649220804866993 91600776408486915603650245)
              ·
                refine ⟨17175145576591296675684421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91600776408486915603650245 17175145576591296675684421)
                ·
                  refine ⟨3220339795610868126690829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17175145576591296675684421 3220339795610868126690829)
                  ·
                    refine ⟨1207627423354075547509061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220339795610868126690829 1207627423354075547509061)
                    ·
                      rfl

theorem cell22_3527769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_3527769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527769 prefixEnd_3527769 := by exact prefixLift 3527769
  have htrace : WordTrace (prefixWord ++ tailWord_3527769) baseStart_3527769 baseEnd_3527769 := by
    simpa [prefixWord, tailWord_3527769, baseEnd_3527769] using wordTrace_append hprefix tailTrace_3527769
  have hstable : (prefixWord ++ tailWord_3527769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527769).length < 2 ^ (prefixWord ++ tailWord_3527769).sum := by decide
  have hdescent : baseEnd_3527769 < baseStart_3527769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527859 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 2, 5]
def baseStart_3527859 : Nat := 118140960795 + 3527859 * 2 ^ 59
def prefixEnd_3527859 : Nat := 4983230072969 + 3 ^ 40 * 3527859 * 2
def baseEnd_3527859 : Nat := 1207658232193345312758785

theorem tailTrace_3527859 : CollatzResearch.WordTrace tailWord_3527859 prefixEnd_3527859 1207658232193345312758785 := by
  unfold tailWord_3527859
  simp only [CollatzResearch.WordTrace]
  refine ⟨128671588526176828194010631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85781059017451218796007087 128671588526176828194010631)
  ·
    refine ⟨193007382789265242291015947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128671588526176828194010631 193007382789265242291015947)
    ·
      refine ⟨289511074183897863436523921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193007382789265242291015947 289511074183897863436523921)
      ·
        refine ⟨217133305637923397577392941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289511074183897863436523921 217133305637923397577392941)
        ·
          refine ⟨81424989614221274091522353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217133305637923397577392941 81424989614221274091522353)
          ·
            refine ⟨61068742210665955568641765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81424989614221274091522353 61068742210665955568641765)
            ·
              refine ⟨11450389164499866669120331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61068742210665955568641765 11450389164499866669120331)
              ·
                refine ⟨17175583746749800003680497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450389164499866669120331 17175583746749800003680497)
                ·
                  refine ⟨12881687810062350002760373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17175583746749800003680497 12881687810062350002760373)
                  ·
                    refine ⟨1207658232193345312758785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12881687810062350002760373 1207658232193345312758785)
                    ·
                      rfl

theorem cell22_3527859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_3527859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527859 prefixEnd_3527859 := by exact prefixLift 3527859
  have htrace : WordTrace (prefixWord ++ tailWord_3527859) baseStart_3527859 baseEnd_3527859 := by
    simpa [prefixWord, tailWord_3527859, baseEnd_3527859] using wordTrace_append hprefix tailTrace_3527859
  have hstable : (prefixWord ++ tailWord_3527859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527859).length < 2 ^ (prefixWord ++ tailWord_3527859).sum := by decide
  have hdescent : baseEnd_3527859 < baseStart_3527859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527968 : List Nat := [2, 1, 1, 5, 3, 2, 1, 7]
def baseStart_3527968 : Nat := 118140960795 + 3527968 * 2 ^ 59
def prefixEnd_3527968 : Nat := 4983230072969 + 3 ^ 40 * 3527968 * 2
def baseEnd_3527968 : Nat := 134188393902322817975939

theorem tailTrace_3527968 : CollatzResearch.WordTrace tailWord_3527968 prefixEnd_3527968 134188393902322817975939 := by
  unfold tailWord_3527968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64337782041390969904864279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85783709388521293206485705 64337782041390969904864279)
  ·
    refine ⟨96506673062086454857296419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64337782041390969904864279 96506673062086454857296419)
    ·
      refine ⟨144760009593129682285944629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96506673062086454857296419 144760009593129682285944629)
      ·
        refine ⟨13571250899355907714307309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144760009593129682285944629 13571250899355907714307309)
        ·
          refine ⟨5089219087258465392865241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13571250899355907714307309 5089219087258465392865241)
          ·
            refine ⟨3816914315443849044648931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089219087258465392865241 3816914315443849044648931)
            ·
              refine ⟨5725371473165773566973397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816914315443849044648931 5725371473165773566973397)
              ·
                refine ⟨134188393902322817975939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5725371473165773566973397 134188393902322817975939)
                ·
                  rfl

theorem cell22_3527968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_3527968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3527968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3527968 prefixEnd_3527968 := by exact prefixLift 3527968
  have htrace : WordTrace (prefixWord ++ tailWord_3527968) baseStart_3527968 baseEnd_3527968 := by
    simpa [prefixWord, tailWord_3527968, baseEnd_3527968] using wordTrace_append hprefix tailTrace_3527968
  have hstable : (prefixWord ++ tailWord_3527968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527968).length < 2 ^ (prefixWord ++ tailWord_3527968).sum := by decide
  have hdescent : baseEnd_3527968 < baseStart_3527968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528000 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 1, 3]
def baseStart_3528000 : Nat := 118140960795 + 3528000 * 2 ^ 59
def prefixEnd_3528000 : Nat := 4983230072969 + 3 ^ 40 * 3528000 * 2
def baseEnd_3528000 : Nat := 1207706499374867944983353

theorem tailTrace_3528000 : CollatzResearch.WordTrace tailWord_3528000 prefixEnd_3528000 1207706499374867944983353 := by
  unfold tailWord_3528000
  simp only [CollatzResearch.WordTrace]
  refine ⟨64338365609333004637446727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85784487479110672849928969 64338365609333004637446727)
  ·
    refine ⟨96507548413999506956170091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64338365609333004637446727 96507548413999506956170091)
    ·
      refine ⟨144761322620999260434255137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96507548413999506956170091 144761322620999260434255137)
      ·
        refine ⟨108570991965749445325691353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144761322620999260434255137 108570991965749445325691353)
        ·
          refine ⟨81428243974312083994268515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108570991965749445325691353 81428243974312083994268515)
          ·
            refine ⟨122142365961468125991402773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81428243974312083994268515 122142365961468125991402773)
            ·
              refine ⟨5725423404443818405847005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122142365961468125991402773 5725423404443818405847005)
              ·
                refine ⟨2147033776666431902192627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5725423404443818405847005 2147033776666431902192627)
                ·
                  refine ⟨3220550664999647853288941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147033776666431902192627 3220550664999647853288941)
                  ·
                    refine ⟨1207706499374867944983353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220550664999647853288941 1207706499374867944983353)
                    ·
                      rfl

theorem cell22_3528000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_3528000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528000 prefixEnd_3528000 := by exact prefixLift 3528000
  have htrace : WordTrace (prefixWord ++ tailWord_3528000) baseStart_3528000 baseEnd_3528000 := by
    simpa [prefixWord, tailWord_3528000, baseEnd_3528000] using wordTrace_append hprefix tailTrace_3528000
  have hstable : (prefixWord ++ tailWord_3528000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528000).length < 2 ^ (prefixWord ++ tailWord_3528000).sum := by decide
  have hdescent : baseEnd_3528000 < baseStart_3528000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528006 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3528006 : Nat := 118140960795 + 3528006 * 2 ^ 59
def prefixEnd_3528006 : Nat := 4983230072969 + 3 ^ 40 * 3528006 * 2
def baseEnd_3528006 : Nat := 1207708553297485929333335

theorem tailTrace_3528006 : CollatzResearch.WordTrace tailWord_3528006 prefixEnd_3528006 1207708553297485929333335 := by
  unfold tailWord_3528006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021154689270133509362871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85784633371096181533074581 4021154689270133509362871)
  ·
    refine ⟨6031732033905200264044307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4021154689270133509362871 6031732033905200264044307)
    ·
      refine ⟨9047598050857800396066461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6031732033905200264044307 9047598050857800396066461)
      ·
        refine ⟨3392849269071675148524923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9047598050857800396066461 3392849269071675148524923)
        ·
          refine ⟨5089273903607512722787385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3392849269071675148524923 5089273903607512722787385)
          ·
            refine ⟨3816955427705634542090539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089273903607512722787385 3816955427705634542090539)
            ·
              refine ⟨5725433141558451813135809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816955427705634542090539 5725433141558451813135809)
              ·
                refine ⟨4294074856168838859851857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5725433141558451813135809 4294074856168838859851857)
                ·
                  refine ⟨3220556142126629144888893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4294074856168838859851857 3220556142126629144888893)
                  ·
                    refine ⟨1207708553297485929333335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220556142126629144888893 1207708553297485929333335)
                    ·
                      rfl

theorem cell22_3528006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3528006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528006 prefixEnd_3528006 := by exact prefixLift 3528006
  have htrace : WordTrace (prefixWord ++ tailWord_3528006) baseStart_3528006 baseEnd_3528006 := by
    simpa [prefixWord, tailWord_3528006, baseEnd_3528006] using wordTrace_append hprefix tailTrace_3528006
  have hstable : (prefixWord ++ tailWord_3528006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528006).length < 2 ^ (prefixWord ++ tailWord_3528006).sum := by decide
  have hdescent : baseEnd_3528006 < baseStart_3528006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528026 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_3528026 : Nat := 118140960795 + 3528026 * 2 ^ 59
def prefixEnd_3528026 : Nat := 4983230072969 + 3 ^ 40 * 3528026 * 2
def baseEnd_3528026 : Nat := 1207715399706212543833273

theorem tailTrace_3528026 : CollatzResearch.WordTrace tailWord_3528026 prefixEnd_3528026 1207715399706212543833273 := by
  unfold tailWord_3528026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32169419879142953928834983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85785119677714543810226621 32169419879142953928834983)
  ·
    refine ⟨48254129818714430893252475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32169419879142953928834983 48254129818714430893252475)
    ·
      refine ⟨72381194728071646339878713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48254129818714430893252475 72381194728071646339878713)
      ·
        refine ⟨54285896046053734754909035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72381194728071646339878713 54285896046053734754909035)
        ·
          refine ⟨81428844069080602132363553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54285896046053734754909035 81428844069080602132363553)
          ·
            refine ⟨61071633051810451599272665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81428844069080602132363553 61071633051810451599272665)
            ·
              refine ⟨45803724788857838699454499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61071633051810451599272665 45803724788857838699454499)
              ·
                refine ⟨68705587183286758049181749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45803724788857838699454499 68705587183286758049181749)
                ·
                  refine ⟨6441148798433133567110789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68705587183286758049181749 6441148798433133567110789)
                  ·
                    refine ⟨1207715399706212543833273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441148798433133567110789 1207715399706212543833273)
                    ·
                      rfl

theorem cell22_3528026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_3528026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528026 prefixEnd_3528026 := by exact prefixLift 3528026
  have htrace : WordTrace (prefixWord ++ tailWord_3528026) baseStart_3528026 baseEnd_3528026 := by
    simpa [prefixWord, tailWord_3528026, baseEnd_3528026] using wordTrace_append hprefix tailTrace_3528026
  have hstable : (prefixWord ++ tailWord_3528026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528026).length < 2 ^ (prefixWord ++ tailWord_3528026).sum := by decide
  have hdescent : baseEnd_3528026 < baseStart_3528026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528075 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 4]
def baseStart_3528075 : Nat := 118140960795 + 3528075 * 2 ^ 59
def prefixEnd_3528075 : Nat := 4983230072969 + 3 ^ 40 * 3528075 * 2
def baseEnd_3528075 : Nat := 402577391135864249786041

theorem tailTrace_3528075 : CollatzResearch.WordTrace tailWord_3528075 prefixEnd_3528075 402577391135864249786041 := by
  unfold tailWord_3528075
  simp only [CollatzResearch.WordTrace]
  refine ⟨128679466693394297083873679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85786311128929531389249119 128679466693394297083873679)
  ·
    refine ⟨193019200040091445625810519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128679466693394297083873679 193019200040091445625810519)
    ·
      refine ⟨289528800060137168438715779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193019200040091445625810519 289528800060137168438715779)
      ·
        refine ⟨434293200090205752658073669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289528800060137168438715779 434293200090205752658073669)
        ·
          refine ⟨81429975016913578623388813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434293200090205752658073669 81429975016913578623388813)
          ·
            refine ⟨30536240631342591983770805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81429975016913578623388813 30536240631342591983770805)
            ·
              refine ⟨2862772559188367998478513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30536240631342591983770805 2862772559188367998478513)
              ·
                refine ⟨2147079419391275998858885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862772559188367998478513 2147079419391275998858885)
                ·
                  refine ⟨402577391135864249786041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147079419391275998858885 402577391135864249786041)
                  ·
                    rfl

theorem cell22_3528075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 4].length) (baseStart_3528075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528075 prefixEnd_3528075 := by exact prefixLift 3528075
  have htrace : WordTrace (prefixWord ++ tailWord_3528075) baseStart_3528075 baseEnd_3528075 := by
    simpa [prefixWord, tailWord_3528075, baseEnd_3528075] using wordTrace_append hprefix tailTrace_3528075
  have hstable : (prefixWord ++ tailWord_3528075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528075).length < 2 ^ (prefixWord ++ tailWord_3528075).sum := by decide
  have hdescent : baseEnd_3528075 < baseStart_3528075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528090 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_3528090 : Nat := 118140960795 + 3528090 * 2 ^ 59
def prefixEnd_3528090 : Nat := 4983230072969 + 3 ^ 40 * 3528090 * 2
def baseEnd_3528090 : Nat := 1207737308214137710233077

theorem tailTrace_3528090 : CollatzResearch.WordTrace tailWord_3528090 prefixEnd_3528090 1207737308214137710233077 := by
  unfold tailWord_3528090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32170003447084988661417431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85786675858893303097113149 32170003447084988661417431)
  ·
    refine ⟨48255005170627482992126147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32170003447084988661417431 48255005170627482992126147)
    ·
      refine ⟨72382507755941224488189221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48255005170627482992126147 72382507755941224488189221)
      ·
        refine ⟨13571720204238979591535479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72382507755941224488189221 13571720204238979591535479)
        ·
          refine ⟨20357580306358469387303219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571720204238979591535479 20357580306358469387303219)
          ·
            refine ⟨30536370459537704080954829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20357580306358469387303219 30536370459537704080954829)
            ·
              refine ⟨11451138922326639030358061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30536370459537704080954829 11451138922326639030358061)
              ·
                refine ⟨4294177095872489636384273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11451138922326639030358061 4294177095872489636384273)
                ·
                  refine ⟨3220632821904367227288205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4294177095872489636384273 3220632821904367227288205)
                  ·
                    refine ⟨1207737308214137710233077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220632821904367227288205 1207737308214137710233077)
                    ·
                      rfl

theorem cell22_3528090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_3528090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528090 prefixEnd_3528090 := by exact prefixLift 3528090
  have htrace : WordTrace (prefixWord ++ tailWord_3528090) baseStart_3528090 baseEnd_3528090 := by
    simpa [prefixWord, tailWord_3528090, baseEnd_3528090] using wordTrace_append hprefix tailTrace_3528090
  have hstable : (prefixWord ++ tailWord_3528090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528090).length < 2 ^ (prefixWord ++ tailWord_3528090).sum := by decide
  have hdescent : baseEnd_3528090 < baseStart_3528090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528094 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3528094 : Nat := 118140960795 + 3528094 * 2 ^ 59
def prefixEnd_3528094 : Nat := 4983230072969 + 3 ^ 40 * 3528094 * 2
def baseEnd_3528094 : Nat := 1207738677495883033133065

theorem tailTrace_3528094 : CollatzResearch.WordTrace tailWord_3528094 prefixEnd_3528094 1207738677495883033133065 := by
  unfold tailWord_3528094
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085019960040682916101917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85786773120216975552543557 16085019960040682916101917)
  ·
    refine ⟨6031882485015256093538219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16085019960040682916101917 6031882485015256093538219)
    ·
      refine ⟨9047823727522884140307329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6031882485015256093538219 9047823727522884140307329)
      ·
        refine ⟨6785867795642163105230497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9047823727522884140307329 6785867795642163105230497)
        ·
          refine ⟨5089400846731622328922873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6785867795642163105230497 5089400846731622328922873)
          ·
            refine ⟨3817050635048716746692155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089400846731622328922873 3817050635048716746692155)
            ·
              refine ⟨5725575952573075120038233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817050635048716746692155 5725575952573075120038233)
              ·
                refine ⟨4294181964429806340028675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5725575952573075120038233 4294181964429806340028675)
                ·
                  refine ⟨6441272946644709510043013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294181964429806340028675 6441272946644709510043013)
                  ·
                    refine ⟨1207738677495883033133065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441272946644709510043013 1207738677495883033133065)
                    ·
                      rfl

theorem cell22_3528094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3528094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528094 prefixEnd_3528094 := by exact prefixLift 3528094
  have htrace : WordTrace (prefixWord ++ tailWord_3528094) baseStart_3528094 baseEnd_3528094 := by
    simpa [prefixWord, tailWord_3528094, baseEnd_3528094] using wordTrace_append hprefix tailTrace_3528094
  have hstable : (prefixWord ++ tailWord_3528094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528094).length < 2 ^ (prefixWord ++ tailWord_3528094).sum := by decide
  have hdescent : baseEnd_3528094 < baseStart_3528094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528131 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 7]
def baseStart_3528131 : Nat := 118140960795 + 3528131 * 2 ^ 59
def prefixEnd_3528131 : Nat := 4983230072969 + 3 ^ 40 * 3528131 * 2
def baseEnd_3528131 : Nat := 402583781117342423319317

theorem tailTrace_3528131 : CollatzResearch.WordTrace tailWord_3528131 prefixEnd_3528131 402583781117342423319317 := by
  unfold tailWord_3528131
  simp only [CollatzResearch.WordTrace]
  refine ⟨128681509181191418647912247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85787672787460945765274831 128681509181191418647912247)
  ·
    refine ⟨193022263771787127971868371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128681509181191418647912247 193022263771787127971868371)
    ·
      refine ⟨289533395657680691957802557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193022263771787127971868371 289533395657680691957802557)
      ·
        refine ⟨108575023371630259484175959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289533395657680691957802557 108575023371630259484175959)
        ·
          refine ⟨162862535057445389226263939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108575023371630259484175959 162862535057445389226263939)
          ·
            refine ⟨244293802586168083839395909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162862535057445389226263939 244293802586168083839395909)
            ·
              refine ⟨45805087984906515719886733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244293802586168083839395909 45805087984906515719886733)
              ·
                refine ⟨17176907994339943394957525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45805087984906515719886733 17176907994339943394957525)
                ·
                  refine ⟨402583781117342423319317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17176907994339943394957525 402583781117342423319317)
                  ·
                    rfl

theorem cell22_3528131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_3528131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528131 prefixEnd_3528131 := by exact prefixLift 3528131
  have htrace : WordTrace (prefixWord ++ tailWord_3528131) baseStart_3528131 baseEnd_3528131 := by
    simpa [prefixWord, tailWord_3528131, baseEnd_3528131] using wordTrace_append hprefix tailTrace_3528131
  have hstable : (prefixWord ++ tailWord_3528131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528131).length < 2 ^ (prefixWord ++ tailWord_3528131).sum := by decide
  have hdescent : baseEnd_3528131 < baseStart_3528131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528182 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_3528182 : Nat := 118140960795 + 3528182 * 2 ^ 59
def prefixEnd_3528182 : Nat := 4983230072969 + 3 ^ 40 * 3528182 * 2
def baseEnd_3528182 : Nat := 402589600564760045644265

theorem tailTrace_3528182 : CollatzResearch.WordTrace tailWord_3528182 prefixEnd_3528182 402589600564760045644265 := by
  unfold tailWord_3528182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042710581500415897376175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85788912869337769572012533 8042710581500415897376175)
  ·
    refine ⟨12064065872250623846064263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8042710581500415897376175 12064065872250623846064263)
    ·
      refine ⟨18096098808375935769096395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12064065872250623846064263 18096098808375935769096395)
      ·
        refine ⟨27144148212563903653644593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18096098808375935769096395 27144148212563903653644593)
        ·
          refine ⟨20358111159422927740233445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27144148212563903653644593 20358111159422927740233445)
          ·
            refine ⟨3817145842391798951293771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20358111159422927740233445 3817145842391798951293771)
            ·
              refine ⟨5725718763587698426940657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817145842391798951293771 5725718763587698426940657)
              ·
                refine ⟨4294289072690773820205493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5725718763587698426940657 4294289072690773820205493)
                ·
                  refine ⟨402589600564760045644265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4294289072690773820205493 402589600564760045644265)
                  ·
                    rfl

theorem cell22_3528182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_3528182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528182 prefixEnd_3528182 := by exact prefixLift 3528182
  have htrace : WordTrace (prefixWord ++ tailWord_3528182) baseStart_3528182 baseEnd_3528182 := by
    simpa [prefixWord, tailWord_3528182, baseEnd_3528182] using wordTrace_append hprefix tailTrace_3528182
  have hstable : (prefixWord ++ tailWord_3528182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528182).length < 2 ^ (prefixWord ++ tailWord_3528182).sum := by decide
  have hdescent : baseEnd_3528182 < baseStart_3528182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528223 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 1, 6]
def baseStart_3528223 : Nat := 118140960795 + 3528223 * 2 ^ 59
def prefixEnd_3528223 : Nat := 4983230072969 + 3 ^ 40 * 3528223 * 2
def baseEnd_3528223 : Nat := 1207782836832169696657669

theorem tailTrace_3528223 : CollatzResearch.WordTrace tailWord_3528223 prefixEnd_3528223 1207782836832169696657669 := by
  unfold tailWord_3528223
  simp only [CollatzResearch.WordTrace]
  refine ⟨128684864696858118360261323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85789909797905412240174215 128684864696858118360261323)
  ·
    refine ⟨193027297045287177540391985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128684864696858118360261323 193027297045287177540391985)
    ·
      refine ⟨144770472783965383155293989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193027297045287177540391985 144770472783965383155293989)
      ·
        refine ⟨27144463646993509341617623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144770472783965383155293989 27144463646993509341617623)
        ·
          refine ⟨40716695470490264012426435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27144463646993509341617623 40716695470490264012426435)
          ·
            refine ⟨61075043205735396018639653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40716695470490264012426435 61075043205735396018639653)
            ·
              refine ⟨11451570601075386753494935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61075043205735396018639653 11451570601075386753494935)
              ·
                refine ⟨17177355901613080130242403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11451570601075386753494935 17177355901613080130242403)
                ·
                  refine ⟨25766033852419620195363605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17177355901613080130242403 25766033852419620195363605)
                  ·
                    refine ⟨1207782836832169696657669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25766033852419620195363605 1207782836832169696657669)
                    ·
                      rfl

theorem cell22_3528223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_3528223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528223 prefixEnd_3528223 := by exact prefixLift 3528223
  have htrace : WordTrace (prefixWord ++ tailWord_3528223) baseStart_3528223 baseEnd_3528223 := by
    simpa [prefixWord, tailWord_3528223, baseEnd_3528223] using wordTrace_append hprefix tailTrace_3528223
  have hstable : (prefixWord ++ tailWord_3528223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528223).length < 2 ^ (prefixWord ++ tailWord_3528223).sum := by decide
  have hdescent : baseEnd_3528223 < baseStart_3528223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528225 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3528225 : Nat := 118140960795 + 3528225 * 2 ^ 59
def prefixEnd_3528225 : Nat := 4983230072969 + 3 ^ 40 * 3528225 * 2
def baseEnd_3528225 : Nat := 1207783521473042358107663

theorem tailTrace_3528225 : CollatzResearch.WordTrace tailWord_3528225 prefixEnd_3528225 1207783521473042358107663 := by
  unfold tailWord_3528225
  simp only [CollatzResearch.WordTrace]
  refine ⟨128684937642850872701834129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85789958428567248467889419 128684937642850872701834129)
  ·
    refine ⟨96513703232138154526375597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128684937642850872701834129 96513703232138154526375597)
    ·
      refine ⟨36192638712051807947390849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96513703232138154526375597 36192638712051807947390849)
      ·
        refine ⟨27144479034038855960543137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36192638712051807947390849 27144479034038855960543137)
        ·
          refine ⟨20358359275529141970407353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27144479034038855960543137 20358359275529141970407353)
          ·
            refine ⟨15268769456646856477805515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20358359275529141970407353 15268769456646856477805515)
            ·
              refine ⟨22903154184970284716708273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15268769456646856477805515 22903154184970284716708273)
              ·
                refine ⟨17177365638727713537531205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22903154184970284716708273 17177365638727713537531205)
                ·
                  refine ⟨3220756057261446288287101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17177365638727713537531205 3220756057261446288287101)
                  ·
                    refine ⟨1207783521473042358107663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220756057261446288287101 1207783521473042358107663)
                    ·
                      rfl

theorem cell22_3528225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3528225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528225 prefixEnd_3528225 := by exact prefixLift 3528225
  have htrace : WordTrace (prefixWord ++ tailWord_3528225) baseStart_3528225 baseEnd_3528225 := by
    simpa [prefixWord, tailWord_3528225, baseEnd_3528225] using wordTrace_append hprefix tailTrace_3528225
  have hstable : (prefixWord ++ tailWord_3528225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528225).length < 2 ^ (prefixWord ++ tailWord_3528225).sum := by decide
  have hdescent : baseEnd_3528225 < baseStart_3528225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528270 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_3528270 : Nat := 118140960795 + 3528270 * 2 ^ 59
def prefixEnd_3528270 : Nat := 4983230072969 + 3 ^ 40 * 3528270 * 2
def baseEnd_3528270 : Nat := 1207798925892677240732525

theorem tailTrace_3528270 : CollatzResearch.WordTrace tailWord_3528270 prefixEnd_3528270 1207798925892677240732525 := by
  unfold tailWord_3528270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085822365960980673402783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85791052618458563591481509 16085822365960980673402783)
  ·
    refine ⟨24128733548941471010104175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16085822365960980673402783 24128733548941471010104175)
    ·
      refine ⟨36193100323412206515156263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24128733548941471010104175 36193100323412206515156263)
      ·
        refine ⟨54289650485118309772734395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36193100323412206515156263 54289650485118309772734395)
        ·
          refine ⟨81434475727677464659101593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54289650485118309772734395 81434475727677464659101593)
          ·
            refine ⟨61075856795758098494326195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81434475727677464659101593 61075856795758098494326195)
            ·
              refine ⟨91613785193637147741489293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61075856795758098494326195 91613785193637147741489293)
              ·
                refine ⟨34355169447613930403058485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91613785193637147741489293 34355169447613930403058485)
                ·
                  refine ⟨3220797135713805975286733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34355169447613930403058485 3220797135713805975286733)
                  ·
                    refine ⟨1207798925892677240732525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220797135713805975286733 1207798925892677240732525)
                    ·
                      rfl

theorem cell22_3528270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_3528270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528270 prefixEnd_3528270 := by exact prefixLift 3528270
  have htrace : WordTrace (prefixWord ++ tailWord_3528270) baseStart_3528270 baseEnd_3528270 := by
    simpa [prefixWord, tailWord_3528270, baseEnd_3528270] using wordTrace_append hprefix tailTrace_3528270
  have hstable : (prefixWord ++ tailWord_3528270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528270).length < 2 ^ (prefixWord ++ tailWord_3528270).sum := by decide
  have hdescent : baseEnd_3528270 < baseStart_3528270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528304 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 1, 3]
def baseStart_3528304 : Nat := 118140960795 + 3528304 * 2 ^ 59
def prefixEnd_3528304 : Nat := 4983230072969 + 3 ^ 40 * 3528304 * 2
def baseEnd_3528304 : Nat := 1207810564787512485382421

theorem tailTrace_3528304 : CollatzResearch.WordTrace tailWord_3528304 prefixEnd_3528304 1207810564787512485382421 := by
  unfold tailWord_3528304
  simp only [CollatzResearch.WordTrace]
  refine ⟨64343909504782334596979983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85791879339709779462639977 64343909504782334596979983)
  ·
    refine ⟨96515864257173501895469975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64343909504782334596979983 96515864257173501895469975)
    ·
      refine ⟨144773796385760252843204963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96515864257173501895469975 144773796385760252843204963)
      ·
        refine ⟨217160694578640379264807445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144773796385760252843204963 217160694578640379264807445)
        ·
          refine ⟨10179407558373767778037849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 217160694578640379264807445 10179407558373767778037849)
          ·
            refine ⟨7634555668780325833528387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10179407558373767778037849 7634555668780325833528387)
            ·
              refine ⟨11451833503170488750292581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634555668780325833528387 11451833503170488750292581)
              ·
                refine ⟨2147218781844466640679859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11451833503170488750292581 2147218781844466640679859)
                ·
                  refine ⟨3220828172766699961019789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147218781844466640679859 3220828172766699961019789)
                  ·
                    refine ⟨1207810564787512485382421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220828172766699961019789 1207810564787512485382421)
                    ·
                      rfl

theorem cell22_3528304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_3528304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528304 prefixEnd_3528304 := by exact prefixLift 3528304
  have htrace : WordTrace (prefixWord ++ tailWord_3528304) baseStart_3528304 baseEnd_3528304 := by
    simpa [prefixWord, tailWord_3528304, baseEnd_3528304] using wordTrace_append hprefix tailTrace_3528304
  have hstable : (prefixWord ++ tailWord_3528304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528304).length < 2 ^ (prefixWord ++ tailWord_3528304).sum := by decide
  have hdescent : baseEnd_3528304 < baseStart_3528304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528351 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 5]
def baseStart_3528351 : Nat := 118140960795 + 3528351 * 2 ^ 59
def prefixEnd_3528351 : Nat := 4983230072969 + 3 ^ 40 * 3528351 * 2
def baseEnd_3528351 : Nat := 402608884616006676485759

theorem tailTrace_3528351 : CollatzResearch.WordTrace tailWord_3528351 prefixEnd_3528351 402608884616006676485759 := by
  unfold tailWord_3528351
  simp only [CollatzResearch.WordTrace]
  refine ⟨128689533240394396220920907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85793022160262930813947271 128689533240394396220920907)
  ·
    refine ⟨193034299860591594331381361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128689533240394396220920907 193034299860591594331381361)
    ·
      refine ⟨144775724895443695748536021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193034299860591594331381361 144775724895443695748536021)
      ·
        refine ⟨3393181052236961619106313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 144775724895443695748536021 3393181052236961619106313)
        ·
          refine ⟨2544885789177721214329735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3393181052236961619106313 2544885789177721214329735)
          ·
            refine ⟨3817328683766581821494603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544885789177721214329735 3817328683766581821494603)
            ·
              refine ⟨5725993025649872732241905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817328683766581821494603 5725993025649872732241905)
              ·
                refine ⟨4294494769237404549181429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5725993025649872732241905 4294494769237404549181429)
                ·
                  refine ⟨402608884616006676485759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4294494769237404549181429 402608884616006676485759)
                  ·
                    rfl

theorem cell22_3528351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 5].length) (baseStart_3528351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528351 prefixEnd_3528351 := by exact prefixLift 3528351
  have htrace : WordTrace (prefixWord ++ tailWord_3528351) baseStart_3528351 baseEnd_3528351 := by
    simpa [prefixWord, tailWord_3528351, baseEnd_3528351] using wordTrace_append hprefix tailTrace_3528351
  have hstable : (prefixWord ++ tailWord_3528351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528351).length < 2 ^ (prefixWord ++ tailWord_3528351).sum := by decide
  have hdescent : baseEnd_3528351 < baseStart_3528351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528375 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3528375 : Nat := 118140960795 + 3528375 * 2 ^ 59
def prefixEnd_3528375 : Nat := 4983230072969 + 3 ^ 40 * 3528375 * 2
def baseEnd_3528375 : Nat := 1207834869538491966857203

theorem tailTrace_3528375 : CollatzResearch.WordTrace tailWord_3528375 prefixEnd_3528375 1207834869538491966857203 := by
  unfold tailWord_3528375
  simp only [CollatzResearch.WordTrace]
  refine ⟨128690408592307448319794579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85793605728204965546529719 128690408592307448319794579)
  ·
    refine ⟨193035612888461172479691869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128690408592307448319794579 193035612888461172479691869)
    ·
      refine ⟨72388354833172939679884451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193035612888461172479691869 72388354833172939679884451)
      ·
        refine ⟨108582532249759409519826677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72388354833172939679884451 108582532249759409519826677)
        ·
          refine ⟨10179612398414944642483751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108582532249759409519826677 10179612398414944642483751)
          ·
            refine ⟨15269418597622416963725627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10179612398414944642483751 15269418597622416963725627)
            ·
              refine ⟨22904127896433625445588441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15269418597622416963725627 22904127896433625445588441)
              ·
                refine ⟨17178095922325219084191331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22904127896433625445588441 17178095922325219084191331)
                ·
                  refine ⟨25767143883487828626286997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17178095922325219084191331 25767143883487828626286997)
                  ·
                    refine ⟨1207834869538491966857203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25767143883487828626286997 1207834869538491966857203)
                    ·
                      rfl

theorem cell22_3528375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3528375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528375 prefixEnd_3528375 := by exact prefixLift 3528375
  have htrace : WordTrace (prefixWord ++ tailWord_3528375) baseStart_3528375 baseEnd_3528375 := by
    simpa [prefixWord, tailWord_3528375, baseEnd_3528375] using wordTrace_append hprefix tailTrace_3528375
  have hstable : (prefixWord ++ tailWord_3528375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528375).length < 2 ^ (prefixWord ++ tailWord_3528375).sum := by decide
  have hdescent : baseEnd_3528375 < baseStart_3528375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528377 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_3528377 : Nat := 118140960795 + 3528377 * 2 ^ 59
def prefixEnd_3528377 : Nat := 4983230072969 + 3 ^ 40 * 3528377 * 2
def baseEnd_3528377 : Nat := 1207835554179364628307197

theorem tailTrace_3528377 : CollatzResearch.WordTrace tailWord_3528377 prefixEnd_3528377 1207835554179364628307197 := by
  unfold tailWord_3528377
  simp only [CollatzResearch.WordTrace]
  refine ⟨128690481538300202661367385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85793654358866801774244923 128690481538300202661367385)
  ·
    refine ⟨96517861153725151996025539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128690481538300202661367385 96517861153725151996025539)
    ·
      refine ⟨144776791730587727994038309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96517861153725151996025539 144776791730587727994038309)
      ·
        refine ⟨27145648449485198998882183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144776791730587727994038309 27145648449485198998882183)
        ·
          refine ⟨40718472674227798498323275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27145648449485198998882183 40718472674227798498323275)
          ·
            refine ⟨61077709011341697747484913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40718472674227798498323275 61077709011341697747484913)
            ·
              refine ⟨45808281758506273310613685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61077709011341697747484913 45808281758506273310613685)
              ·
                refine ⟨4294526414859963122870033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45808281758506273310613685 4294526414859963122870033)
                ·
                  refine ⟨3220894811144972342152525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4294526414859963122870033 3220894811144972342152525)
                  ·
                    refine ⟨1207835554179364628307197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3220894811144972342152525 1207835554179364628307197)
                    ·
                      rfl

theorem cell22_3528377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_3528377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528377 prefixEnd_3528377 := by exact prefixLift 3528377
  have htrace : WordTrace (prefixWord ++ tailWord_3528377) baseStart_3528377 baseEnd_3528377 := by
    simpa [prefixWord, tailWord_3528377, baseEnd_3528377] using wordTrace_append hprefix tailTrace_3528377
  have hstable : (prefixWord ++ tailWord_3528377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528377).length < 2 ^ (prefixWord ++ tailWord_3528377).sum := by decide
  have hdescent : baseEnd_3528377 < baseStart_3528377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528396 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 4]
def baseStart_3528396 : Nat := 118140960795 + 3528396 * 2 ^ 59
def prefixEnd_3528396 : Nat := 4983230072969 + 3 ^ 40 * 3528396 * 2
def baseEnd_3528396 : Nat := 402614019422551637360713

theorem tailTrace_3528396 : CollatzResearch.WordTrace tailWord_3528396 prefixEnd_3528396 402614019422551637360713 := by
  unfold tailWord_3528396
  simp only [CollatzResearch.WordTrace]
  refine ⟨64345587262615684453154521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85794116350154245937539361 64345587262615684453154521)
  ·
    refine ⟨48259190446961763339865891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64345587262615684453154521 48259190446961763339865891)
    ·
      refine ⟨72388785670442645009798837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48259190446961763339865891 72388785670442645009798837)
      ·
        refine ⟨6786448656603997969668641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72388785670442645009798837 6786448656603997969668641)
        ·
          refine ⟨5089836492452998477251481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6786448656603997969668641 5089836492452998477251481)
          ·
            refine ⟨3817377369339748857938611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089836492452998477251481 3817377369339748857938611)
            ·
              refine ⟨5726066054009623286907917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817377369339748857938611 5726066054009623286907917)
              ·
                refine ⟨2147274770253608732590469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5726066054009623286907917 2147274770253608732590469)
                ·
                  refine ⟨402614019422551637360713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147274770253608732590469 402614019422551637360713)
                  ·
                    rfl

theorem cell22_3528396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_3528396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528396 prefixEnd_3528396 := by exact prefixLift 3528396
  have htrace : WordTrace (prefixWord ++ tailWord_3528396) baseStart_3528396 baseEnd_3528396 := by
    simpa [prefixWord, tailWord_3528396, baseEnd_3528396] using wordTrace_append hprefix tailTrace_3528396
  have hstable : (prefixWord ++ tailWord_3528396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528396).length < 2 ^ (prefixWord ++ tailWord_3528396).sum := by decide
  have hdescent : baseEnd_3528396 < baseStart_3528396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528413 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 4]
def baseStart_3528413 : Nat := 118140960795 + 3528413 * 2 ^ 59
def prefixEnd_3528413 : Nat := 4983230072969 + 3 ^ 40 * 3528413 * 2
def baseEnd_3528413 : Nat := 402615959238357511469029

theorem tailTrace_3528413 : CollatzResearch.WordTrace tailWord_3528413 prefixEnd_3528413 402615959238357511469029 := by
  unfold tailWord_3528413
  simp only [CollatzResearch.WordTrace]
  refine ⟨128691794566169780809677893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85794529710779853873118595 128691794566169780809677893)
  ·
    refine ⟨24129711481156833901814605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128691794566169780809677893 24129711481156833901814605)
    ·
      refine ⟨9048641805433812713180477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24129711481156833901814605 9048641805433812713180477)
      ·
        refine ⟨3393240677037679767442679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9048641805433812713180477 3393240677037679767442679)
        ·
          refine ⟨5089861015556519651164019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393240677037679767442679 5089861015556519651164019)
          ·
            refine ⟨7634791523334779476746029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089861015556519651164019 7634791523334779476746029)
            ·
              refine ⟨2863046821250542303779761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7634791523334779476746029 2863046821250542303779761)
              ·
                refine ⟨2147285115937906727834821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863046821250542303779761 2147285115937906727834821)
                ·
                  refine ⟨402615959238357511469029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147285115937906727834821 402615959238357511469029)
                  ·
                    rfl

theorem cell22_3528413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_3528413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528413 prefixEnd_3528413 := by exact prefixLift 3528413
  have htrace : WordTrace (prefixWord ++ tailWord_3528413) baseStart_3528413 baseEnd_3528413 := by
    simpa [prefixWord, tailWord_3528413, baseEnd_3528413] using wordTrace_append hprefix tailTrace_3528413
  have hstable : (prefixWord ++ tailWord_3528413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528413).length < 2 ^ (prefixWord ++ tailWord_3528413).sum := by decide
  have hdescent : baseEnd_3528413 < baseStart_3528413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528420 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_3528420 : Nat := 118140960795 + 3528420 * 2 ^ 59
def prefixEnd_3528420 : Nat := 4983230072969 + 3 ^ 40 * 3528420 * 2
def baseEnd_3528420 : Nat := 1207850273958126849482065

theorem tailTrace_3528420 : CollatzResearch.WordTrace tailWord_3528420 prefixEnd_3528420 1207850273958126849482065 := by
  unfold tailWord_3528420
  simp only [CollatzResearch.WordTrace]
  refine ⟨64346024938572210502591357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85794699918096280670121809 64346024938572210502591357)
  ·
    refine ⟨24129759351964578938471759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64346024938572210502591357 24129759351964578938471759)
    ·
      refine ⟨36194639027946868407707639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24129759351964578938471759 36194639027946868407707639)
      ·
        refine ⟨54291958541920302611561459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36194639027946868407707639 54291958541920302611561459)
        ·
          refine ⟨81437937812880453917342189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54291958541920302611561459 81437937812880453917342189)
          ·
            refine ⟨30539226679830170219003321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81437937812880453917342189 30539226679830170219003321)
            ·
              refine ⟨22904420009872627664252491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30539226679830170219003321 22904420009872627664252491)
              ·
                refine ⟨34356630014808941496378737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22904420009872627664252491 34356630014808941496378737)
                ·
                  refine ⟨25767472511106706122284053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34356630014808941496378737 25767472511106706122284053)
                  ·
                    refine ⟨1207850273958126849482065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25767472511106706122284053 1207850273958126849482065)
                    ·
                      rfl

theorem cell22_3528420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_3528420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528420 prefixEnd_3528420 := by exact prefixLift 3528420
  have htrace : WordTrace (prefixWord ++ tailWord_3528420) baseStart_3528420 baseEnd_3528420 := by
    simpa [prefixWord, tailWord_3528420, baseEnd_3528420] using wordTrace_append hprefix tailTrace_3528420
  have hstable : (prefixWord ++ tailWord_3528420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528420).length < 2 ^ (prefixWord ++ tailWord_3528420).sum := by decide
  have hdescent : baseEnd_3528420 < baseStart_3528420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528482 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3528482 : Nat := 118140960795 + 3528482 * 2 ^ 59
def prefixEnd_3528482 : Nat := 4983230072969 + 3 ^ 40 * 3528482 * 2
def baseEnd_3528482 : Nat := 1207871497825179354431875

theorem tailTrace_3528482 : CollatzResearch.WordTrace tailWord_3528482 prefixEnd_3528482 1207871497825179354431875 := by
  unfold tailWord_3528482
  simp only [CollatzResearch.WordTrace]
  refine ⟨32173577800729951398484925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85796207468613203729293133 32173577800729951398484925)
  ·
    refine ⟨12065091675273731774431847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32173577800729951398484925 12065091675273731774431847)
    ·
      refine ⟨18097637512910597661647771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12065091675273731774431847 18097637512910597661647771)
      ·
        refine ⟨27146456269365896492471657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18097637512910597661647771 27146456269365896492471657)
        ·
          refine ⟨20359842202024422369353743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27146456269365896492471657 20359842202024422369353743)
          ·
            refine ⟨30539763303036633554030615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20359842202024422369353743 30539763303036633554030615)
            ·
              refine ⟨45809644954554950331045923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30539763303036633554030615 45809644954554950331045923)
              ·
                refine ⟨68714467431832425496568885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45809644954554950331045923 68714467431832425496568885)
                ·
                  refine ⟨6441981321734289890303333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68714467431832425496568885 6441981321734289890303333)
                  ·
                    refine ⟨1207871497825179354431875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441981321734289890303333 1207871497825179354431875)
                    ·
                      rfl

theorem cell22_3528482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3528482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528482 prefixEnd_3528482 := by exact prefixLift 3528482
  have htrace : WordTrace (prefixWord ++ tailWord_3528482) baseStart_3528482 baseEnd_3528482 := by
    simpa [prefixWord, tailWord_3528482, baseEnd_3528482] using wordTrace_append hprefix tailTrace_3528482
  have hstable : (prefixWord ++ tailWord_3528482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528482).length < 2 ^ (prefixWord ++ tailWord_3528482).sum := by decide
  have hdescent : baseEnd_3528482 < baseStart_3528482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528495 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_3528495 : Nat := 118140960795 + 3528495 * 2 ^ 59
def prefixEnd_3528495 : Nat := 4983230072969 + 3 ^ 40 * 3528495 * 2
def baseEnd_3528495 : Nat := 1207875947990851653856835

theorem tailTrace_3528495 : CollatzResearch.WordTrace tailWord_3528495 prefixEnd_3528495 1207875947990851653856835 := by
  unfold tailWord_3528495
  simp only [CollatzResearch.WordTrace]
  refine ⟨128694785351872708814162939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85796523567915139209441959 128694785351872708814162939)
  ·
    refine ⟨193042178027809063221244409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128694785351872708814162939 193042178027809063221244409)
    ·
      refine ⟨144781633520856797415933307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193042178027809063221244409 144781633520856797415933307)
      ·
        refine ⟨217172450281285196123899961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144781633520856797415933307 217172450281285196123899961)
        ·
          refine ⟨162879337710963897092924971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217172450281285196123899961 162879337710963897092924971)
          ·
            refine ⟨244319006566445845639387457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162879337710963897092924971 244319006566445845639387457)
            ·
              refine ⟨183239254924834384229540593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244319006566445845639387457 183239254924834384229540593)
              ·
                refine ⟨137429441193625788172155445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183239254924834384229540593 137429441193625788172155445)
                ·
                  refine ⟨12884010111902417641139573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137429441193625788172155445 12884010111902417641139573)
                  ·
                    refine ⟨1207875947990851653856835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12884010111902417641139573 1207875947990851653856835)
                    ·
                      rfl

theorem cell22_3528495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_3528495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528495 prefixEnd_3528495 := by exact prefixLift 3528495
  have htrace : WordTrace (prefixWord ++ tailWord_3528495) baseStart_3528495 baseEnd_3528495 := by
    simpa [prefixWord, tailWord_3528495, baseEnd_3528495] using wordTrace_append hprefix tailTrace_3528495
  have hstable : (prefixWord ++ tailWord_3528495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528495).length < 2 ^ (prefixWord ++ tailWord_3528495).sum := by decide
  have hdescent : baseEnd_3528495 < baseStart_3528495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528497 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 6]
def baseStart_3528497 : Nat := 118140960795 + 3528497 * 2 ^ 59
def prefixEnd_3528497 : Nat := 4983230072969 + 3 ^ 40 * 3528497 * 2
def baseEnd_3528497 : Nat := 402625544210574771768943

theorem tailTrace_3528497 : CollatzResearch.WordTrace tailWord_3528497 prefixEnd_3528497 402625544210574771768943 := by
  unfold tailWord_3528497
  simp only [CollatzResearch.WordTrace]
  refine ⟨128694858297865463155735745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85796572198576975437157163 128694858297865463155735745)
  ·
    refine ⟨96521143723399097366801809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128694858297865463155735745 96521143723399097366801809)
    ·
      refine ⟨72390857792549323025101357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96521143723399097366801809 72390857792549323025101357)
      ·
        refine ⟨27146571672205996134413009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72390857792549323025101357 27146571672205996134413009)
        ·
          refine ⟨20359928754154497100809757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27146571672205996134413009 20359928754154497100809757)
          ·
            refine ⟨7634973282807936412803659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20359928754154497100809757 7634973282807936412803659)
            ·
              refine ⟨11452459924211904619205489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634973282807936412803659 11452459924211904619205489)
              ·
                refine ⟨8589344943158928464404117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11452459924211904619205489 8589344943158928464404117)
                ·
                  refine ⟨402625544210574771768943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8589344943158928464404117 402625544210574771768943)
                  ·
                    rfl

theorem cell22_3528497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_3528497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528497 prefixEnd_3528497 := by exact prefixLift 3528497
  have htrace : WordTrace (prefixWord ++ tailWord_3528497) baseStart_3528497 baseEnd_3528497 := by
    simpa [prefixWord, tailWord_3528497, baseEnd_3528497] using wordTrace_append hprefix tailTrace_3528497
  have hstable : (prefixWord ++ tailWord_3528497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528497).length < 2 ^ (prefixWord ++ tailWord_3528497).sum := by decide
  have hdescent : baseEnd_3528497 < baseStart_3528497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528529 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_3528529 : Nat := 118140960795 + 3528529 * 2 ^ 59
def prefixEnd_3528529 : Nat := 4983230072969 + 3 ^ 40 * 3528529 * 2
def baseEnd_3528529 : Nat := 1207887586885686898506731

theorem tailTrace_3528529 : CollatzResearch.WordTrace tailWord_3528529 prefixEnd_3528529 1207887586885686898506731 := by
  unfold tailWord_3528529
  simp only [CollatzResearch.WordTrace]
  refine ⟨128696025433749532620900641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85797350289166355080600427 128696025433749532620900641)
  ·
    refine ⟨96522019075312149465675481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128696025433749532620900641 96522019075312149465675481)
    ·
      refine ⟨72391514306484112099256611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96522019075312149465675481 72391514306484112099256611)
      ·
        refine ⟨108587271459726168148884917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72391514306484112099256611 108587271459726168148884917)
        ·
          refine ⟨10180056699349328263957961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108587271459726168148884917 10180056699349328263957961)
          ·
            refine ⟨7635042524511996197968471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10180056699349328263957961 7635042524511996197968471)
            ·
              refine ⟨11452563786767994296952707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635042524511996197968471 11452563786767994296952707)
              ·
                refine ⟨17178845680151991445429061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11452563786767994296952707 17178845680151991445429061)
                ·
                  refine ⟨3221033565028498396017949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17178845680151991445429061 3221033565028498396017949)
                  ·
                    refine ⟨1207887586885686898506731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3221033565028498396017949 1207887586885686898506731)
                    ·
                      rfl

theorem cell22_3528529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_3528529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528529 prefixEnd_3528529 := by exact prefixLift 3528529
  have htrace : WordTrace (prefixWord ++ tailWord_3528529) baseStart_3528529 baseEnd_3528529 := by
    simpa [prefixWord, tailWord_3528529, baseEnd_3528529] using wordTrace_append hprefix tailTrace_3528529
  have hstable : (prefixWord ++ tailWord_3528529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528529).length < 2 ^ (prefixWord ++ tailWord_3528529).sum := by decide
  have hdescent : baseEnd_3528529 < baseStart_3528529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528546 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3528546 : Nat := 118140960795 + 3528546 * 2 ^ 59
def prefixEnd_3528546 : Nat := 4983230072969 + 3 ^ 40 * 3528546 * 2
def baseEnd_3528546 : Nat := 1207893406333104520831679

theorem tailTrace_3528546 : CollatzResearch.WordTrace tailWord_3528546 prefixEnd_3528546 1207893406333104520831679 := by
  unfold tailWord_3528546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32174161368671986131067373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85797763649791963016179661 32174161368671986131067373)
  ·
    refine ⟨12065310513251994799150265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32174161368671986131067373 12065310513251994799150265)
    ·
      refine ⟨9048982884938996099362699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12065310513251994799150265 9048982884938996099362699)
      ·
        refine ⟨13573474327408494149044049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9048982884938996099362699 13573474327408494149044049)
        ·
          refine ⟨10180105745556370611783037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13573474327408494149044049 10180105745556370611783037)
          ·
            refine ⟨3817539654583638979418639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10180105745556370611783037 3817539654583638979418639)
            ·
              refine ⟨5726309481875458469127959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817539654583638979418639 5726309481875458469127959)
              ·
                refine ⟨8589464222813187703691939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726309481875458469127959 8589464222813187703691939)
                ·
                  refine ⟨12884196334219781555537909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589464222813187703691939 12884196334219781555537909)
                  ·
                    refine ⟨1207893406333104520831679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12884196334219781555537909 1207893406333104520831679)
                    ·
                      rfl

theorem cell22_3528546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3528546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528546 prefixEnd_3528546 := by exact prefixLift 3528546
  have htrace : WordTrace (prefixWord ++ tailWord_3528546) baseStart_3528546 baseEnd_3528546 := by
    simpa [prefixWord, tailWord_3528546, baseEnd_3528546] using wordTrace_append hprefix tailTrace_3528546
  have hstable : (prefixWord ++ tailWord_3528546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528546).length < 2 ^ (prefixWord ++ tailWord_3528546).sum := by decide
  have hdescent : baseEnd_3528546 < baseStart_3528546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528587 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 5]
def baseStart_3528587 : Nat := 118140960795 + 3528587 * 2 ^ 59
def prefixEnd_3528587 : Nat := 4983230072969 + 3 ^ 40 * 3528587 * 2
def baseEnd_3528587 : Nat := 402635813823664693518851

theorem tailTrace_3528587 : CollatzResearch.WordTrace tailWord_3528587 prefixEnd_3528587 402635813823664693518851 := by
  unfold tailWord_3528587
  simp only [CollatzResearch.WordTrace]
  refine ⟨128698140867539408526512015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85798760578359605684341343 128698140867539408526512015)
  ·
    refine ⟨193047211301309112789768023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128698140867539408526512015 193047211301309112789768023)
    ·
      refine ⟨289570816951963669184652035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193047211301309112789768023 289570816951963669184652035)
      ·
        refine ⟨434356225427945503776978053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289570816951963669184652035 434356225427945503776978053)
        ·
          refine ⟨81441792267739781958183385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434356225427945503776978053 81441792267739781958183385)
          ·
            refine ⟨61081344200804836468637539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81441792267739781958183385 61081344200804836468637539)
            ·
              refine ⟨91622016301207254702956309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61081344200804836468637539 91622016301207254702956309)
              ·
                refine ⟨4294782014119090064201077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91622016301207254702956309 4294782014119090064201077)
                ·
                  refine ⟨402635813823664693518851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4294782014119090064201077 402635813823664693518851)
                  ·
                    rfl

theorem cell22_3528587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 5].length) (baseStart_3528587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528587 prefixEnd_3528587 := by exact prefixLift 3528587
  have htrace : WordTrace (prefixWord ++ tailWord_3528587) baseStart_3528587 baseEnd_3528587 := by
    simpa [prefixWord, tailWord_3528587, baseEnd_3528587] using wordTrace_append hprefix tailTrace_3528587
  have hstable : (prefixWord ++ tailWord_3528587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528587).length < 2 ^ (prefixWord ++ tailWord_3528587).sum := by decide
  have hdescent : baseEnd_3528587 < baseStart_3528587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528647 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3528647 : Nat := 118140960795 + 3528647 * 2 ^ 59
def prefixEnd_3528647 : Nat := 4983230072969 + 3 ^ 40 * 3528647 * 2
def baseEnd_3528647 : Nat := 1207927980697173924056369

theorem tailTrace_3528647 : CollatzResearch.WordTrace tailWord_3528647 prefixEnd_3528647 1207927980697173924056369 := by
  unfold tailWord_3528647
  simp only [CollatzResearch.WordTrace]
  refine ⟨128700329247322038773696195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85800219498214692515797463 128700329247322038773696195)
  ·
    refine ⟨193050493870983058160544293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128700329247322038773696195 193050493870983058160544293)
    ·
      refine ⟨36196967600809323405102055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193050493870983058160544293 36196967600809323405102055)
      ·
        refine ⟨54295451401213985107653083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36196967600809323405102055 54295451401213985107653083)
        ·
          refine ⟨81443177101820977661479625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54295451401213985107653083 81443177101820977661479625)
          ·
            refine ⟨61082382826365733246109719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81443177101820977661479625 61082382826365733246109719)
            ·
              refine ⟨91623574239548599869164579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61082382826365733246109719 91623574239548599869164579)
              ·
                refine ⟨137435361359322899803746869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91623574239548599869164579 137435361359322899803746869)
                ·
                  refine ⟨12884565127436521856601269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137435361359322899803746869 12884565127436521856601269)
                  ·
                    refine ⟨1207927980697173924056369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12884565127436521856601269 1207927980697173924056369)
                    ·
                      rfl

theorem cell22_3528647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3528647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528647 prefixEnd_3528647 := by exact prefixLift 3528647
  have htrace : WordTrace (prefixWord ++ tailWord_3528647) baseStart_3528647 baseEnd_3528647 := by
    simpa [prefixWord, tailWord_3528647, baseEnd_3528647] using wordTrace_append hprefix tailTrace_3528647
  have hstable : (prefixWord ++ tailWord_3528647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528647).length < 2 ^ (prefixWord ++ tailWord_3528647).sum := by decide
  have hdescent : baseEnd_3528647 < baseStart_3528647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528649 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 4]
def baseStart_3528649 : Nat := 118140960795 + 3528649 * 2 ^ 59
def prefixEnd_3528649 : Nat := 4983230072969 + 3 ^ 40 * 3528649 * 2
def baseEnd_3528649 : Nat := 402642888446015528502121

theorem tailTrace_3528649 : CollatzResearch.WordTrace tailWord_3528649 prefixEnd_3528649 402642888446015528502121 := by
  unfold tailWord_3528649
  simp only [CollatzResearch.WordTrace]
  refine ⟨128700402193314793115269001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85800268128876528743512667 128700402193314793115269001)
  ·
    refine ⟨96525301644986094836451751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128700402193314793115269001 96525301644986094836451751)
    ·
      refine ⟨144787952467479142254677627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96525301644986094836451751 144787952467479142254677627)
      ·
        refine ⟨217181928701218713382016441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144787952467479142254677627 217181928701218713382016441)
        ·
          refine ⟨162886446525914035036512331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217181928701218713382016441 162886446525914035036512331)
          ·
            refine ⟨244329669788871052554768497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162886446525914035036512331 244329669788871052554768497)
            ·
              refine ⟨183247252341653289416076373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244329669788871052554768497 183247252341653289416076373)
              ·
                refine ⟨2147428738378749485344645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 183247252341653289416076373 2147428738378749485344645)
                ·
                  refine ⟨402642888446015528502121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147428738378749485344645 402642888446015528502121)
                  ·
                    rfl

theorem cell22_3528649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_3528649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528649 prefixEnd_3528649 := by exact prefixLift 3528649
  have htrace : WordTrace (prefixWord ++ tailWord_3528649) baseStart_3528649 baseEnd_3528649 := by
    simpa [prefixWord, tailWord_3528649, baseEnd_3528649] using wordTrace_append hprefix tailTrace_3528649
  have hstable : (prefixWord ++ tailWord_3528649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528649).length < 2 ^ (prefixWord ++ tailWord_3528649).sum := by decide
  have hdescent : baseEnd_3528649 < baseStart_3528649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528664 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_3528664 : Nat := 118140960795 + 3528664 * 2 ^ 59
def prefixEnd_3528664 : Nat := 4983230072969 + 3 ^ 40 * 3528664 * 2
def baseEnd_3528664 : Nat := 1207933800144591546381317

theorem tailTrace_3528664 : CollatzResearch.WordTrace tailWord_3528664 prefixEnd_3528664 1207933800144591546381317 := by
  unfold tailWord_3528664
  simp only [CollatzResearch.WordTrace]
  refine ⟨64350474644130225338532523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85800632858840300451376697 64350474644130225338532523)
  ·
    refine ⟨96525711966195338007798785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64350474644130225338532523 96525711966195338007798785)
    ·
      refine ⟨72394283974646503505849089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96525711966195338007798785 72394283974646503505849089)
      ·
        refine ⟨54295712980984877629386817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72394283974646503505849089 54295712980984877629386817)
        ·
          refine ⟨40721784735738658222040113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54295712980984877629386817 40721784735738658222040113)
          ·
            refine ⟨30541338551803993666530085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40721784735738658222040113 30541338551803993666530085)
            ·
              refine ⟨5726500978463248812474391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30541338551803993666530085 5726500978463248812474391)
              ·
                refine ⟨8589751467694873218711587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726500978463248812474391 8589751467694873218711587)
                ·
                  refine ⟨12884627201542309828067381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589751467694873218711587 12884627201542309828067381)
                  ·
                    refine ⟨1207933800144591546381317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12884627201542309828067381 1207933800144591546381317)
                    ·
                      rfl

theorem cell22_3528664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_3528664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528664 prefixEnd_3528664 := by exact prefixLift 3528664
  have htrace : WordTrace (prefixWord ++ tailWord_3528664) baseStart_3528664 baseEnd_3528664 := by
    simpa [prefixWord, tailWord_3528664, baseEnd_3528664] using wordTrace_append hprefix tailTrace_3528664
  have hstable : (prefixWord ++ tailWord_3528664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528664).length < 2 ^ (prefixWord ++ tailWord_3528664).sum := by decide
  have hdescent : baseEnd_3528664 < baseStart_3528664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528707 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_3528707 : Nat := 118140960795 + 3528707 * 2 ^ 59
def prefixEnd_3528707 : Nat := 4983230072969 + 3 ^ 40 * 3528707 * 2
def baseEnd_3528707 : Nat := 1207948519923353767556185

theorem tailTrace_3528707 : CollatzResearch.WordTrace tailWord_3528707 prefixEnd_3528707 1207948519923353767556185 := by
  unfold tailWord_3528707
  simp only [CollatzResearch.WordTrace]
  refine ⟨128702517627104669020880375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85801678418069779347253583 128702517627104669020880375)
  ·
    refine ⟨193053776440657003531320563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128702517627104669020880375 193053776440657003531320563)
    ·
      refine ⟨289580664660985505296980845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193053776440657003531320563 289580664660985505296980845)
      ·
        refine ⟨108592749247869564486367817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289580664660985505296980845 108592749247869564486367817)
        ·
          refine ⟨81444561935902173364775863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108592749247869564486367817 81444561935902173364775863)
          ·
            refine ⟨122166842903853260047163795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81444561935902173364775863 122166842903853260047163795)
            ·
              refine ⟨183250264355779890070745693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122166842903853260047163795 183250264355779890070745693)
              ·
                refine ⟨68718849133417458776529635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183250264355779890070745693 68718849133417458776529635)
                ·
                  refine ⟨103078273700126188164794453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68718849133417458776529635 103078273700126188164794453)
                  ·
                    refine ⟨1207948519923353767556185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103078273700126188164794453 1207948519923353767556185)
                    ·
                      rfl

theorem cell22_3528707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_3528707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528707 prefixEnd_3528707 := by exact prefixLift 3528707
  have htrace : WordTrace (prefixWord ++ tailWord_3528707) baseStart_3528707 baseEnd_3528707 := by
    simpa [prefixWord, tailWord_3528707, baseEnd_3528707] using wordTrace_append hprefix tailTrace_3528707
  have hstable : (prefixWord ++ tailWord_3528707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528707).length < 2 ^ (prefixWord ++ tailWord_3528707).sum := by decide
  have hdescent : baseEnd_3528707 < baseStart_3528707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528760 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 3, 3]
def baseStart_3528760 : Nat := 118140960795 + 3528760 * 2 ^ 59
def prefixEnd_3528760 : Nat := 4983230072969 + 3 ^ 40 * 3528760 * 2
def baseEnd_3528760 : Nat := 1207966662906479295981023

theorem tailTrace_3528760 : CollatzResearch.WordTrace tailWord_3528760 prefixEnd_3528760 1207966662906479295981023 := by
  unfold tailWord_3528760
  simp only [CollatzResearch.WordTrace]
  refine ⟨64352225347956329536279867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85802967130608439381706489 64352225347956329536279867)
  ·
    refine ⟨96528338021934494304419801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64352225347956329536279867 96528338021934494304419801)
    ·
      refine ⟨72396253516450870728314851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96528338021934494304419801 72396253516450870728314851)
      ·
        refine ⟨108594380274676306092472277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72396253516450870728314851 108594380274676306092472277)
        ·
          refine ⟨2545180787687725924042319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 108594380274676306092472277 2545180787687725924042319)
          ·
            refine ⟨3817771181531588886063479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545180787687725924042319 3817771181531588886063479)
            ·
              refine ⟨5726656772297383329095219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817771181531588886063479 5726656772297383329095219)
              ·
                refine ⟨8589985158446074993642829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726656772297383329095219 8589985158446074993642829)
                ·
                  refine ⟨3221244434417278122616061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8589985158446074993642829 3221244434417278122616061)
                  ·
                    refine ⟨1207966662906479295981023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3221244434417278122616061 1207966662906479295981023)
                    ·
                      rfl

theorem cell22_3528760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_3528760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528760 prefixEnd_3528760 := by exact prefixLift 3528760
  have htrace : WordTrace (prefixWord ++ tailWord_3528760) baseStart_3528760 baseEnd_3528760 := by
    simpa [prefixWord, tailWord_3528760, baseEnd_3528760] using wordTrace_append hprefix tailTrace_3528760
  have hstable : (prefixWord ++ tailWord_3528760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528760).length < 2 ^ (prefixWord ++ tailWord_3528760).sum := by decide
  have hdescent : baseEnd_3528760 < baseStart_3528760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528801 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 4]
def baseStart_3528801 : Nat := 118140960795 + 3528801 * 2 ^ 59
def prefixEnd_3528801 : Nat := 4983230072969 + 3 ^ 40 * 3528801 * 2
def baseEnd_3528801 : Nat := 402660232681456285235299

theorem tailTrace_3528801 : CollatzResearch.WordTrace tailWord_3528801 prefixEnd_3528801 402660232681456285235299 := by
  unfold tailWord_3528801
  simp only [CollatzResearch.WordTrace]
  refine ⟨128705946088764123074802257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85803964059176082049868171 128705946088764123074802257)
  ·
    refine ⟨96529459566573092306101693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128705946088764123074802257 96529459566573092306101693)
    ·
      refine ⟨36198547337464909614788135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96529459566573092306101693 36198547337464909614788135)
      ·
        refine ⟨54297821006197364422182203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36198547337464909614788135 54297821006197364422182203)
        ·
          refine ⟨81446731509296046633273305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54297821006197364422182203 81446731509296046633273305)
          ·
            refine ⟨61085048631972034974954979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81446731509296046633273305 61085048631972034974954979)
            ·
              refine ⟨91627572947958052462432469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61085048631972034974954979 91627572947958052462432469)
              ·
                refine ⟨2147521240967766854588261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91627572947958052462432469 2147521240967766854588261)
                ·
                  refine ⟨402660232681456285235299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147521240967766854588261 402660232681456285235299)
                  ·
                    rfl

theorem cell22_3528801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_3528801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528801 prefixEnd_3528801 := by exact prefixLift 3528801
  have htrace : WordTrace (prefixWord ++ tailWord_3528801) baseStart_3528801 baseEnd_3528801 := by
    simpa [prefixWord, tailWord_3528801, baseEnd_3528801] using wordTrace_append hprefix tailTrace_3528801
  have hstable : (prefixWord ++ tailWord_3528801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528801).length < 2 ^ (prefixWord ++ tailWord_3528801).sum := by decide
  have hdescent : baseEnd_3528801 < baseStart_3528801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528818 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_3528818 : Nat := 118140960795 + 3528818 * 2 ^ 59
def prefixEnd_3528818 : Nat := 4983230072969 + 3 ^ 40 * 3528818 * 2
def baseEnd_3528818 : Nat := 402662172497262159343615

theorem tailTrace_3528818 : CollatzResearch.WordTrace tailWord_3528818 prefixEnd_3528818 402662172497262159343615 := by
  unfold tailWord_3528818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32176641532425633744542777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85804377419801689985447405 32176641532425633744542777)
  ·
    refine ⟨24132481149319225308407083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32176641532425633744542777 24132481149319225308407083)
    ·
      refine ⟨36198721723978837962610625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24132481149319225308407083 36198721723978837962610625)
      ·
        refine ⟨27149041292984128471957969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36198721723978837962610625 27149041292984128471957969)
        ·
          refine ⟨20361780969738096353968477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27149041292984128471957969 20361780969738096353968477)
          ·
            refine ⟨7635667863651786132738179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20361780969738096353968477 7635667863651786132738179)
            ·
              refine ⟨11453501795477679199107269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635667863651786132738179 11453501795477679199107269)
              ·
                refine ⟨2147531586652064849832613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11453501795477679199107269 2147531586652064849832613)
                ·
                  refine ⟨402662172497262159343615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147531586652064849832613 402662172497262159343615)
                  ·
                    rfl

theorem cell22_3528818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_3528818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528818 prefixEnd_3528818 := by exact prefixLift 3528818
  have htrace : WordTrace (prefixWord ++ tailWord_3528818) baseStart_3528818 baseEnd_3528818 := by
    simpa [prefixWord, tailWord_3528818, baseEnd_3528818] using wordTrace_append hprefix tailTrace_3528818
  have hstable : (prefixWord ++ tailWord_3528818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528818).length < 2 ^ (prefixWord ++ tailWord_3528818).sum := by decide
  have hdescent : baseEnd_3528818 < baseStart_3528818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528833 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3528833 : Nat := 118140960795 + 3528833 * 2 ^ 59
def prefixEnd_3528833 : Nat := 4983230072969 + 3 ^ 40 * 3528833 * 2
def baseEnd_3528833 : Nat := 1207991652298331438905799

theorem tailTrace_3528833 : CollatzResearch.WordTrace tailWord_3528833 prefixEnd_3528833 1207991652298331438905799 := by
  unfold tailWord_3528833
  simp only [CollatzResearch.WordTrace]
  refine ⟨128707113224648192539967153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85804742149765461693311435 128707113224648192539967153)
  ·
    refine ⟨96530334918486144404975365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128707113224648192539967153 96530334918486144404975365)
    ·
      refine ⟨18099437797216152075932881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96530334918486144404975365 18099437797216152075932881)
      ·
        refine ⟨13574578347912114056949661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18099437797216152075932881 13574578347912114056949661)
        ·
          refine ⟨5090466880467042771356123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13574578347912114056949661 5090466880467042771356123)
          ·
            refine ⟨7635700320700564157034185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090466880467042771356123 7635700320700564157034185)
            ·
              refine ⟨5726775240525423117775639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635700320700564157034185 5726775240525423117775639)
              ·
                refine ⟨8590162860788134676663459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726775240525423117775639 8590162860788134676663459)
                ·
                  refine ⟨12885244291182202014995189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8590162860788134676663459 12885244291182202014995189)
                  ·
                    refine ⟨1207991652298331438905799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12885244291182202014995189 1207991652298331438905799)
                    ·
                      rfl

theorem cell22_3528833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3528833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528833 prefixEnd_3528833 := by exact prefixLift 3528833
  have htrace : WordTrace (prefixWord ++ tailWord_3528833) baseStart_3528833 baseEnd_3528833 := by
    simpa [prefixWord, tailWord_3528833, baseEnd_3528833] using wordTrace_append hprefix tailTrace_3528833
  have hstable : (prefixWord ++ tailWord_3528833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528833).length < 2 ^ (prefixWord ++ tailWord_3528833).sum := by decide
  have hdescent : baseEnd_3528833 < baseStart_3528833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528852 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3528852 : Nat := 118140960795 + 3528852 * 2 ^ 59
def prefixEnd_3528852 : Nat := 4983230072969 + 3 ^ 40 * 3528852 * 2
def baseEnd_3528852 : Nat := 402666052128873907560247

theorem tailTrace_3528852 : CollatzResearch.WordTrace tailWord_3528852 prefixEnd_3528852 402666052128873907560247 := by
  unfold tailWord_3528852
  simp only [CollatzResearch.WordTrace]
  refine ⟨64353903105789679392454405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85805204141052905856605873 64353903105789679392454405)
  ·
    refine ⟨12066356832335564886085201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64353903105789679392454405 12066356832335564886085201)
    ·
      refine ⟨9049767624251673664563901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12066356832335564886085201 9049767624251673664563901)
      ·
        refine ⟨3393662859094377624211463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9049767624251673664563901 3393662859094377624211463)
        ·
          refine ⟨5090494288641566436317195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393662859094377624211463 5090494288641566436317195)
          ·
            refine ⟨7635741432962349654475793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090494288641566436317195 7635741432962349654475793)
            ·
              refine ⟨5726806074721762240856845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635741432962349654475793 5726806074721762240856845)
              ·
                refine ⟨2147552278020660840321317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5726806074721762240856845 2147552278020660840321317)
                ·
                  refine ⟨402666052128873907560247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147552278020660840321317 402666052128873907560247)
                  ·
                    rfl

theorem cell22_3528852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3528852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528852 prefixEnd_3528852 := by exact prefixLift 3528852
  have htrace : WordTrace (prefixWord ++ tailWord_3528852) baseStart_3528852 baseEnd_3528852 := by
    simpa [prefixWord, tailWord_3528852, baseEnd_3528852] using wordTrace_append hprefix tailTrace_3528852
  have hstable : (prefixWord ++ tailWord_3528852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528852).length < 2 ^ (prefixWord ++ tailWord_3528852).sum := by decide
  have hdescent : baseEnd_3528852 < baseStart_3528852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528884 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3528884 : Nat := 118140960795 + 3528884 * 2 ^ 59
def prefixEnd_3528884 : Nat := 4983230072969 + 3 ^ 40 * 3528884 * 2
def baseEnd_3528884 : Nat := 1208009110640584305880643

theorem tailTrace_3528884 : CollatzResearch.WordTrace tailWord_3528884 prefixEnd_3528884 1208009110640584305880643 := by
  unfold tailWord_3528884
  simp only [CollatzResearch.WordTrace]
  refine ⟨64354486673731714125036853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85805982231642285500049137 64354486673731714125036853)
  ·
    refine ⟨6033233125662348199222205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64354486673731714125036853 6033233125662348199222205)
    ·
      refine ⟨2262462422123380574708327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6033233125662348199222205 2262462422123380574708327)
      ·
        refine ⟨3393693633185070862062491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262462422123380574708327 3393693633185070862062491)
        ·
          refine ⟨5090540449777606293093737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393693633185070862062491 5090540449777606293093737)
          ·
            refine ⟨3817905337333204719820303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090540449777606293093737 3817905337333204719820303)
            ·
              refine ⟨5726858005999807079730455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817905337333204719820303 5726858005999807079730455)
              ·
                refine ⟨8590287008999710619595683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726858005999807079730455 8590287008999710619595683)
                ·
                  refine ⟨12885430513499565929393525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8590287008999710619595683 12885430513499565929393525)
                  ·
                    refine ⟨1208009110640584305880643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12885430513499565929393525 1208009110640584305880643)
                    ·
                      rfl

theorem cell22_3528884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3528884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528884 prefixEnd_3528884 := by exact prefixLift 3528884
  have htrace : WordTrace (prefixWord ++ tailWord_3528884) baseStart_3528884 baseEnd_3528884 := by
    simpa [prefixWord, tailWord_3528884, baseEnd_3528884] using wordTrace_append hprefix tailTrace_3528884
  have hstable : (prefixWord ++ tailWord_3528884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528884).length < 2 ^ (prefixWord ++ tailWord_3528884).sum := by decide
  have hdescent : baseEnd_3528884 < baseStart_3528884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528897 : List Nat := [1, 2, 6, 1, 3, 1, 2, 6]
def baseStart_3528897 : Nat := 118140960795 + 3528897 * 2 ^ 59
def prefixEnd_3528897 : Nat := 4983230072969 + 3 ^ 40 * 3528897 * 2
def baseEnd_3528897 : Nat := 134223728978472956145067

theorem tailTrace_3528897 : CollatzResearch.WordTrace tailWord_3528897 prefixEnd_3528897 134223728978472956145067 := by
  unfold tailWord_3528897
  simp only [CollatzResearch.WordTrace]
  refine ⟨128709447496416331470296945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85806298330944220980197963 128709447496416331470296945)
  ·
    refine ⟨96532085622312248602722709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128709447496416331470296945 96532085622312248602722709)
    ·
      refine ⟨4524941513545886653252627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96532085622312248602722709 4524941513545886653252627)
      ·
        refine ⟨6787412270318829979878941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4524941513545886653252627 6787412270318829979878941)
        ·
          refine ⟨2545279601369561242454603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6787412270318829979878941 2545279601369561242454603)
          ·
            refine ⟨3817919402054341863681905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545279601369561242454603 3817919402054341863681905)
            ·
              refine ⟨2863439551540756397761429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817919402054341863681905 2863439551540756397761429)
              ·
                refine ⟨134223728978472956145067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2863439551540756397761429 134223728978472956145067)
                ·
                  rfl

theorem cell22_3528897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 6].length) (baseStart_3528897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528897 prefixEnd_3528897 := by exact prefixLift 3528897
  have htrace : WordTrace (prefixWord ++ tailWord_3528897) baseStart_3528897 baseEnd_3528897 := by
    simpa [prefixWord, tailWord_3528897, baseEnd_3528897] using wordTrace_append hprefix tailTrace_3528897
  have hstable : (prefixWord ++ tailWord_3528897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528897).length < 2 ^ (prefixWord ++ tailWord_3528897).sum := by decide
  have hdescent : baseEnd_3528897 < baseStart_3528897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528968 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_3528968 : Nat := 118140960795 + 3528968 * 2 ^ 59
def prefixEnd_3528968 : Nat := 4983230072969 + 3 ^ 40 * 3528968 * 2
def baseEnd_3528968 : Nat := 1208037865557236086780385

theorem tailTrace_3528968 : CollatzResearch.WordTrace tailWord_3528968 prefixEnd_3528968 1208037865557236086780385 := by
  unfold tailWord_3528968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64356018539579555298065779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85808024719439407064087705 64356018539579555298065779)
  ·
    refine ⟨96534027809369332947098669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64356018539579555298065779 96534027809369332947098669)
    ·
      refine ⟨36200260428513499855162001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96534027809369332947098669 36200260428513499855162001)
      ·
        refine ⟨27150195321385124891371501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36200260428513499855162001 27150195321385124891371501)
        ·
          refine ⟨10181323245519421834264313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27150195321385124891371501 10181323245519421834264313)
          ·
            refine ⟨7635992434139566375698235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10181323245519421834264313 7635992434139566375698235)
            ·
              refine ⟨11453988651209349563547353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635992434139566375698235 11453988651209349563547353)
              ·
                refine ⟨8590491488407012172660515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11453988651209349563547353 8590491488407012172660515)
                ·
                  refine ⟨12885737232610518258990773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8590491488407012172660515 12885737232610518258990773)
                  ·
                    refine ⟨1208037865557236086780385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12885737232610518258990773 1208037865557236086780385)
                    ·
                      rfl

theorem cell22_3528968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_3528968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528968 prefixEnd_3528968 := by exact prefixLift 3528968
  have htrace : WordTrace (prefixWord ++ tailWord_3528968) baseStart_3528968 baseEnd_3528968 := by
    simpa [prefixWord, tailWord_3528968, baseEnd_3528968] using wordTrace_append hprefix tailTrace_3528968
  have hstable : (prefixWord ++ tailWord_3528968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528968).length < 2 ^ (prefixWord ++ tailWord_3528968).sum := by decide
  have hdescent : baseEnd_3528968 < baseStart_3528968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3528983 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 2, 4]
def baseStart_3528983 : Nat := 118140960795 + 3528983 * 2 ^ 59
def prefixEnd_3528983 : Nat := 4983230072969 + 3 ^ 40 * 3528983 * 2
def baseEnd_3528983 : Nat := 1208043000363781047655339

theorem tailTrace_3528983 : CollatzResearch.WordTrace tailWord_3528983 prefixEnd_3528983 1208043000363781047655339 := by
  unfold tailWord_3528983
  simp only [CollatzResearch.WordTrace]
  refine ⟨128712584174104768157927603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85808389449403178771951735 128712584174104768157927603)
  ·
    refine ⟨193068876261157152236891405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128712584174104768157927603 193068876261157152236891405)
    ·
      refine ⟨72400828597933932088834277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193068876261157152236891405 72400828597933932088834277)
      ·
        refine ⟨13575155362112612266656427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72400828597933932088834277 13575155362112612266656427)
        ·
          refine ⟨20362733043168918399984641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13575155362112612266656427 20362733043168918399984641)
          ·
            refine ⟨15272049782376688799988481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20362733043168918399984641 15272049782376688799988481)
            ·
              refine ⟨11454037336782516599991361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15272049782376688799988481 11454037336782516599991361)
              ·
                refine ⟨8590528002586887449993521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11454037336782516599991361 8590528002586887449993521)
                ·
                  refine ⟨6442896001940165587495141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590528002586887449993521 6442896001940165587495141)
                  ·
                    refine ⟨1208043000363781047655339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442896001940165587495141 1208043000363781047655339)
                    ·
                      rfl

theorem cell22_3528983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_3528983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3528983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3528983 prefixEnd_3528983 := by exact prefixLift 3528983
  have htrace : WordTrace (prefixWord ++ tailWord_3528983) baseStart_3528983 baseEnd_3528983 := by
    simpa [prefixWord, tailWord_3528983, baseEnd_3528983] using wordTrace_append hprefix tailTrace_3528983
  have hstable : (prefixWord ++ tailWord_3528983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3528983).length < 2 ^ (prefixWord ++ tailWord_3528983).sum := by decide
  have hdescent : baseEnd_3528983 < baseStart_3528983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3528983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529011 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_3529011 : Nat := 118140960795 + 3529011 * 2 ^ 59
def prefixEnd_3529011 : Nat := 4983230072969 + 3 ^ 40 * 3529011 * 2
def baseEnd_3529011 : Nat := 1208052585335998307955253

theorem tailTrace_3529011 : CollatzResearch.WordTrace tailWord_3529011 prefixEnd_3529011 1208052585335998307955253 := by
  unfold tailWord_3529011
  simp only [CollatzResearch.WordTrace]
  refine ⟨128713605418003328939946887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85809070278668885959964591 128713605418003328939946887)
  ·
    refine ⟨193070408127004993409920331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128713605418003328939946887 193070408127004993409920331)
    ·
      refine ⟨289605612190507490114880497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193070408127004993409920331 289605612190507490114880497)
      ·
        refine ⟨217204209142880617586160373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289605612190507490114880497 217204209142880617586160373)
        ·
          refine ⟨20362894607145057898702535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217204209142880617586160373 20362894607145057898702535)
          ·
            refine ⟨30544341910717586848053803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20362894607145057898702535 30544341910717586848053803)
            ·
              refine ⟨45816512866076380272080705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30544341910717586848053803 45816512866076380272080705)
              ·
                refine ⟨34362384649557285204060529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45816512866076380272080705 34362384649557285204060529)
                ·
                  refine ⟨25771788487167963903045397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34362384649557285204060529 25771788487167963903045397)
                  ·
                    refine ⟨1208052585335998307955253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25771788487167963903045397 1208052585335998307955253)
                    ·
                      rfl

theorem cell22_3529011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_3529011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529011 prefixEnd_3529011 := by exact prefixLift 3529011
  have htrace : WordTrace (prefixWord ++ tailWord_3529011) baseStart_3529011 baseEnd_3529011 := by
    simpa [prefixWord, tailWord_3529011, baseEnd_3529011] using wordTrace_append hprefix tailTrace_3529011
  have hstable : (prefixWord ++ tailWord_3529011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529011).length < 2 ^ (prefixWord ++ tailWord_3529011).sum := by decide
  have hdescent : baseEnd_3529011 < baseStart_3529011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529060 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 5]
def baseStart_3529060 : Nat := 118140960795 + 3529060 * 2 ^ 59
def prefixEnd_3529060 : Nat := 4983230072969 + 3 ^ 40 * 3529060 * 2
def baseEnd_3529060 : Nat := 402689786345792837826701

theorem tailTrace_3529060 : CollatzResearch.WordTrace tailWord_3529060 prefixEnd_3529060 402689786345792837826701 := by
  unfold tailWord_3529060
  simp only [CollatzResearch.WordTrace]
  refine ⟨64357696297412905154240317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85810261729883873538987089 64357696297412905154240317)
  ·
    refine ⟨24134136111529839432840119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64357696297412905154240317 24134136111529839432840119)
    ·
      refine ⟨36201204167294759149260179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24134136111529839432840119 36201204167294759149260179)
      ·
        refine ⟨54301806250942138723890269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36201204167294759149260179 54301806250942138723890269)
        ·
          refine ⟨20363177344103302021458851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54301806250942138723890269 20363177344103302021458851)
          ·
            refine ⟨30544766016154953032188277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20363177344103302021458851 30544766016154953032188277)
            ·
              refine ⟨2863571814014526846767651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30544766016154953032188277 2863571814014526846767651)
              ·
                refine ⟨4295357721021790270151477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863571814014526846767651 4295357721021790270151477)
                ·
                  refine ⟨402689786345792837826701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4295357721021790270151477 402689786345792837826701)
                  ·
                    rfl

theorem cell22_3529060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_3529060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529060 prefixEnd_3529060 := by exact prefixLift 3529060
  have htrace : WordTrace (prefixWord ++ tailWord_3529060) baseStart_3529060 baseEnd_3529060 := by
    simpa [prefixWord, tailWord_3529060, baseEnd_3529060] using wordTrace_append hprefix tailTrace_3529060
  have hstable : (prefixWord ++ tailWord_3529060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529060).length < 2 ^ (prefixWord ++ tailWord_3529060).sum := by decide
  have hdescent : baseEnd_3529060 < baseStart_3529060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529071 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 8]
def baseStart_3529071 : Nat := 118140960795 + 3529071 * 2 ^ 59
def prefixEnd_3529071 : Nat := 4983230072969 + 3 ^ 40 * 3529071 * 2
def baseEnd_3529071 : Nat := 402691041520726050485023

theorem tailTrace_3529071 : CollatzResearch.WordTrace tailWord_3529071 prefixEnd_3529071 402691041520726050485023 := by
  unfold tailWord_3529071
  simp only [CollatzResearch.WordTrace]
  refine ⟨128715793797785959187131067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85810529198523972791420711 128715793797785959187131067)
  ·
    refine ⟨193073690696678938780696601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128715793797785959187131067 193073690696678938780696601)
    ·
      refine ⟨144805268022509204085522451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193073690696678938780696601 144805268022509204085522451)
      ·
        refine ⟨217207902033763806128283677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144805268022509204085522451 217207902033763806128283677)
        ·
          refine ⟨81452963262661427298106379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217207902033763806128283677 81452963262661427298106379)
          ·
            refine ⟨122179444893992140947159569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81452963262661427298106379 122179444893992140947159569)
            ·
              refine ⟨91634583670494105710369677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122179444893992140947159569 91634583670494105710369677)
              ·
                refine ⟨34362968876435289641388629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91634583670494105710369677 34362968876435289641388629)
                ·
                  refine ⟨402691041520726050485023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34362968876435289641388629 402691041520726050485023)
                  ·
                    rfl

theorem cell22_3529071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_3529071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529071 prefixEnd_3529071 := by exact prefixLift 3529071
  have htrace : WordTrace (prefixWord ++ tailWord_3529071) baseStart_3529071 baseEnd_3529071 := by
    simpa [prefixWord, tailWord_3529071, baseEnd_3529071] using wordTrace_append hprefix tailTrace_3529071
  have hstable : (prefixWord ++ tailWord_3529071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529071).length < 2 ^ (prefixWord ++ tailWord_3529071).sum := by decide
  have hdescent : baseEnd_3529071 < baseStart_3529071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529156 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3529156 : Nat := 118140960795 + 3529156 * 2 ^ 59
def prefixEnd_3529156 : Nat := 4983230072969 + 3 ^ 40 * 3529156 * 2
def baseEnd_3529156 : Nat := 402700740599755421026603

theorem tailTrace_3529156 : CollatzResearch.WordTrace tailWord_3529156 prefixEnd_3529156 402700740599755421026603 := by
  unfold tailWord_3529156
  simp only [CollatzResearch.WordTrace]
  refine ⟨64359447001239009351987661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85812596001652012469316881 64359447001239009351987661)
  ·
    refine ⟨24134792625464628506995373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64359447001239009351987661 24134792625464628506995373)
    ·
      refine ⟨9050547234549235690123265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24134792625464628506995373 9050547234549235690123265)
      ·
        refine ⟨6787910425911926767592449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9050547234549235690123265 6787910425911926767592449)
        ·
          refine ⟨5090932819433945075694337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6787910425911926767592449 5090932819433945075694337)
          ·
            refine ⟨3818199614575458806770753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090932819433945075694337 3818199614575458806770753)
            ·
              refine ⟨2863649710931594105078065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818199614575458806770753 2863649710931594105078065)
              ·
                refine ⟨2147737283198695578808549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863649710931594105078065 2147737283198695578808549)
                ·
                  refine ⟨402700740599755421026603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147737283198695578808549 402700740599755421026603)
                  ·
                    rfl

theorem cell22_3529156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3529156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529156 prefixEnd_3529156 := by exact prefixLift 3529156
  have htrace : WordTrace (prefixWord ++ tailWord_3529156) baseStart_3529156 baseEnd_3529156 := by
    simpa [prefixWord, tailWord_3529156, baseEnd_3529156] using wordTrace_append hprefix tailTrace_3529156
  have hstable : (prefixWord ++ tailWord_3529156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529156).length < 2 ^ (prefixWord ++ tailWord_3529156).sum := by decide
  have hdescent : baseEnd_3529156 < baseStart_3529156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529186 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3529186 : Nat := 118140960795 + 3529186 * 2 ^ 59
def prefixEnd_3529186 : Nat := 4983230072969 + 3 ^ 40 * 3529186 * 2
def baseEnd_3529186 : Nat := 1208112491412356184829717

theorem tailTrace_3529186 : CollatzResearch.WordTrace tailWord_3529186 prefixEnd_3529186 1208112491412356184829717 := by
  unfold tailWord_3529186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32179997048092333456891853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85813325461579555885044941 32179997048092333456891853)
  ·
    refine ⟨12067498893034625046334445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32179997048092333456891853 12067498893034625046334445)
    ·
      refine ⟨4525312084887984392375417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12067498893034625046334445 4525312084887984392375417)
      ·
        refine ⟨3393984063665988294281563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4525312084887984392375417 3393984063665988294281563)
        ·
          refine ⟨5090976095498982441422345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393984063665988294281563 5090976095498982441422345)
          ·
            refine ⟨3818232071624236831066759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090976095498982441422345 3818232071624236831066759)
            ·
              refine ⟨5727348107436355246600139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818232071624236831066759 5727348107436355246600139)
              ·
                refine ⟨8591022161154532869900209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5727348107436355246600139 8591022161154532869900209)
                ·
                  refine ⟨6443266620865899652425157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8591022161154532869900209 6443266620865899652425157)
                  ·
                    refine ⟨1208112491412356184829717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6443266620865899652425157 1208112491412356184829717)
                    ·
                      rfl

theorem cell22_3529186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3529186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529186 prefixEnd_3529186 := by exact prefixLift 3529186
  have htrace : WordTrace (prefixWord ++ tailWord_3529186) baseStart_3529186 baseEnd_3529186 := by
    simpa [prefixWord, tailWord_3529186, baseEnd_3529186] using wordTrace_append hprefix tailTrace_3529186
  have hstable : (prefixWord ++ tailWord_3529186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529186).length < 2 ^ (prefixWord ++ tailWord_3529186).sum := by decide
  have hdescent : baseEnd_3529186 < baseStart_3529186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529240 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_3529240 : Nat := 118140960795 + 3529240 * 2 ^ 59
def prefixEnd_3529240 : Nat := 4983230072969 + 3 ^ 40 * 3529240 * 2
def baseEnd_3529240 : Nat := 402710325571972681326517

theorem tailTrace_3529240 : CollatzResearch.WordTrace tailWord_3529240 prefixEnd_3529240 402710325571972681326517 := by
  unfold tailWord_3529240
  simp only [CollatzResearch.WordTrace]
  refine ⟨64360978867086850525016587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85814638489449134033355449 64360978867086850525016587)
  ·
    refine ⟨96541468300630275787524881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64360978867086850525016587 96541468300630275787524881)
    ·
      refine ⟨72406101225472706840643661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96541468300630275787524881 72406101225472706840643661)
      ·
        refine ⟨27152287959552265065241373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72406101225472706840643661 27152287959552265065241373)
        ·
          refine ⟨10182107984832099399465515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27152287959552265065241373 10182107984832099399465515)
          ·
            refine ⟨15273161977248149099198273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182107984832099399465515 15273161977248149099198273)
            ·
              refine ⟨11454871482936111824398705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15273161977248149099198273 11454871482936111824398705)
              ·
                refine ⟨8591153612202083868299029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11454871482936111824398705 8591153612202083868299029)
                ·
                  refine ⟨402710325571972681326517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8591153612202083868299029 402710325571972681326517)
                  ·
                    rfl

theorem cell22_3529240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_3529240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529240 prefixEnd_3529240 := by exact prefixLift 3529240
  have htrace : WordTrace (prefixWord ++ tailWord_3529240) baseStart_3529240 baseEnd_3529240 := by
    simpa [prefixWord, tailWord_3529240, baseEnd_3529240] using wordTrace_append hprefix tailTrace_3529240
  have hstable : (prefixWord ++ tailWord_3529240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529240).length < 2 ^ (prefixWord ++ tailWord_3529240).sum := by decide
  have hdescent : baseEnd_3529240 < baseStart_3529240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529272 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_3529272 : Nat := 118140960795 + 3529272 * 2 ^ 59
def prefixEnd_3529272 : Nat := 4983230072969 + 3 ^ 40 * 3529272 * 2
def baseEnd_3529272 : Nat := 1208141930969880627179453

theorem tailTrace_3529272 : CollatzResearch.WordTrace tailWord_3529272 prefixEnd_3529272 1208141930969880627179453 := by
  unfold tailWord_3529272
  simp only [CollatzResearch.WordTrace]
  refine ⟨64361562435028885257599035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85815416580038513676798713 64361562435028885257599035)
  ·
    refine ⟨96542343652543327886398553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64361562435028885257599035 96542343652543327886398553)
    ·
      refine ⟨72406757739407495914798915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96542343652543327886398553 72406757739407495914798915)
      ·
        refine ⟨108610136609111243872198373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72406757739407495914798915 108610136609111243872198373)
        ·
          refine ⟨20364400614208358226037195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108610136609111243872198373 20364400614208358226037195)
          ·
            refine ⟨30546600921312537339055793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20364400614208358226037195 30546600921312537339055793)
            ·
              refine ⟨22909950690984403004291845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30546600921312537339055793 22909950690984403004291845)
              ·
                refine ⟨4295615754559575563304721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22909950690984403004291845 4295615754559575563304721)
                ·
                  refine ⟨3221711815919681672478541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4295615754559575563304721 3221711815919681672478541)
                  ·
                    refine ⟨1208141930969880627179453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3221711815919681672478541 1208141930969880627179453)
                    ·
                      rfl

theorem cell22_3529272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_3529272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529272 prefixEnd_3529272 := by exact prefixLift 3529272
  have htrace : WordTrace (prefixWord ++ tailWord_3529272) baseStart_3529272 baseEnd_3529272 := by
    simpa [prefixWord, tailWord_3529272, baseEnd_3529272] using wordTrace_append hprefix tailTrace_3529272
  have hstable : (prefixWord ++ tailWord_3529272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529272).length < 2 ^ (prefixWord ++ tailWord_3529272).sum := by decide
  have hdescent : baseEnd_3529272 < baseStart_3529272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529274 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_3529274 : Nat := 118140960795 + 3529274 * 2 ^ 59
def prefixEnd_3529274 : Nat := 4983230072969 + 3 ^ 40 * 3529274 * 2
def baseEnd_3529274 : Nat := 402714205203584429543149

theorem tailTrace_3529274 : CollatzResearch.WordTrace tailWord_3529274 prefixEnd_3529274 402714205203584429543149 := by
  unfold tailWord_3529274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32180799454012631214192719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85815465210700349904513917 32180799454012631214192719)
  ·
    refine ⟨48271199181018946821289079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32180799454012631214192719 48271199181018946821289079)
    ·
      refine ⟨72406798771528420231933619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48271199181018946821289079 72406798771528420231933619)
      ·
        refine ⟨108610198157292630347900429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72406798771528420231933619 108610198157292630347900429)
        ·
          refine ⟨40728824308984736380462661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108610198157292630347900429 40728824308984736380462661)
          ·
            refine ⟨7636654557934638071336749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40728824308984736380462661 7636654557934638071336749)
            ·
              refine ⟨2863745459225489276751281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7636654557934638071336749 2863745459225489276751281)
              ·
                refine ⟨2147809094419116957563461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863745459225489276751281 2147809094419116957563461)
                ·
                  refine ⟨402714205203584429543149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147809094419116957563461 402714205203584429543149)
                  ·
                    rfl

theorem cell22_3529274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_3529274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529274 prefixEnd_3529274 := by exact prefixLift 3529274
  have htrace : WordTrace (prefixWord ++ tailWord_3529274) baseStart_3529274 baseEnd_3529274 := by
    simpa [prefixWord, tailWord_3529274, baseEnd_3529274] using wordTrace_append hprefix tailTrace_3529274
  have hstable : (prefixWord ++ tailWord_3529274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529274).length < 2 ^ (prefixWord ++ tailWord_3529274).sum := by decide
  have hdescent : baseEnd_3529274 < baseStart_3529274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529285 : List Nat := [1, 3, 1, 1, 1, 6, 2, 7]
def baseStart_3529285 : Nat := 118140960795 + 3529285 * 2 ^ 59
def prefixEnd_3529285 : Nat := 4983230072969 + 3 ^ 40 * 3529285 * 2
def baseEnd_3529285 : Nat := 134238486792839214067157

theorem tailTrace_3529285 : CollatzResearch.WordTrace tailWord_3529285 prefixEnd_3529285 134238486792839214067157 := by
  unfold tailWord_3529285
  simp only [CollatzResearch.WordTrace]
  refine ⟨128723599019010673735421309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85815732679340449156947539 128723599019010673735421309)
  ·
    refine ⟨48271349632129002650782991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128723599019010673735421309 48271349632129002650782991)
    ·
      refine ⟨72407024448193503976174487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48271349632129002650782991 72407024448193503976174487)
      ·
        refine ⟨108610536672290255964261731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72407024448193503976174487 108610536672290255964261731)
        ·
          refine ⟨162915805008435383946392597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108610536672290255964261731 162915805008435383946392597)
          ·
            refine ⟨7636678359770408622487153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162915805008435383946392597 7636678359770408622487153)
            ·
              refine ⟨5727508769827806466865365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7636678359770408622487153 5727508769827806466865365)
              ·
                refine ⟨134238486792839214067157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5727508769827806466865365 134238486792839214067157)
                ·
                  rfl

theorem cell22_3529285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 7].length) (baseStart_3529285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529285 prefixEnd_3529285 := by exact prefixLift 3529285
  have htrace : WordTrace (prefixWord ++ tailWord_3529285) baseStart_3529285 baseEnd_3529285 := by
    simpa [prefixWord, tailWord_3529285, baseEnd_3529285] using wordTrace_append hprefix tailTrace_3529285
  have hstable : (prefixWord ++ tailWord_3529285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529285).length < 2 ^ (prefixWord ++ tailWord_3529285).sum := by decide
  have hdescent : baseEnd_3529285 < baseStart_3529285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529310 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3529310 : Nat := 118140960795 + 3529310 * 2 ^ 59
def prefixEnd_3529310 : Nat := 4983230072969 + 3 ^ 40 * 3529310 * 2
def baseEnd_3529310 : Nat := 1208154939146461194729337

theorem tailTrace_3529310 : CollatzResearch.WordTrace tailWord_3529310 prefixEnd_3529310 1208154939146461194729337 := by
  unfold tailWord_3529310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16090563855490012875635173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85816340562613402003387589 16090563855490012875635173)
  ·
    refine ⟨3016980722904377414181595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16090563855490012875635173 3016980722904377414181595)
    ·
      refine ⟨4525471084356566121272393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016980722904377414181595 4525471084356566121272393)
      ·
        refine ⟨3394103313267424590954295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4525471084356566121272393 3394103313267424590954295)
        ·
          refine ⟨5091154969901136886431443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394103313267424590954295 5091154969901136886431443)
          ·
            refine ⟨7636732454851705329647165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091154969901136886431443 7636732454851705329647165)
            ·
              refine ⟨2863774670569389498617687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7636732454851705329647165 2863774670569389498617687)
              ·
                refine ⟨4295662005854084247926531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863774670569389498617687 4295662005854084247926531)
                ·
                  refine ⟨6443493008781126371889797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295662005854084247926531 6443493008781126371889797)
                  ·
                    refine ⟨1208154939146461194729337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6443493008781126371889797 1208154939146461194729337)
                    ·
                      rfl

theorem cell22_3529310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3529310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529310 prefixEnd_3529310 := by exact prefixLift 3529310
  have htrace : WordTrace (prefixWord ++ tailWord_3529310) baseStart_3529310 baseEnd_3529310 := by
    simpa [prefixWord, tailWord_3529310, baseEnd_3529310] using wordTrace_append hprefix tailTrace_3529310
  have hstable : (prefixWord ++ tailWord_3529310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529310).length < 2 ^ (prefixWord ++ tailWord_3529310).sum := by decide
  have hdescent : baseEnd_3529310 < baseStart_3529310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529398 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3529398 : Nat := 118140960795 + 3529398 * 2 ^ 59
def prefixEnd_3529398 : Nat := 4983230072969 + 3 ^ 40 * 3529398 * 2
def baseEnd_3529398 : Nat := 402728354448286099509689

theorem tailTrace_3529398 : CollatzResearch.WordTrace tailWord_3529398 prefixEnd_3529398 402728354448286099509689 := by
  unfold tailWord_3529398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045482529225080877142803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85818480311734196022856565 8045482529225080877142803)
  ·
    refine ⟨12068223793837621315714205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045482529225080877142803 12068223793837621315714205)
    ·
      refine ⟨4525583922689107993392827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12068223793837621315714205 4525583922689107993392827)
      ·
        refine ⟨6788375884033661990089241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525583922689107993392827 6788375884033661990089241)
        ·
          refine ⟨5091281913025246492566931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6788375884033661990089241 5091281913025246492566931)
          ·
            refine ⟨7636922869537869738850397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091281913025246492566931 7636922869537869738850397)
            ·
              refine ⟨2863846076076701152068899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7636922869537869738850397 2863846076076701152068899)
              ·
                refine ⟨4295769114115051728103349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863846076076701152068899 4295769114115051728103349)
                ·
                  refine ⟨402728354448286099509689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4295769114115051728103349 402728354448286099509689)
                  ·
                    rfl

theorem cell22_3529398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3529398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529398 prefixEnd_3529398 := by exact prefixLift 3529398
  have htrace : WordTrace (prefixWord ++ tailWord_3529398) baseStart_3529398 baseEnd_3529398 := by
    simpa [prefixWord, tailWord_3529398, baseEnd_3529398] using wordTrace_append hprefix tailTrace_3529398
  have hstable : (prefixWord ++ tailWord_3529398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529398).length < 2 ^ (prefixWord ++ tailWord_3529398).sum := by decide
  have hdescent : baseEnd_3529398 < baseStart_3529398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529407 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 1, 5]
def baseStart_3529407 : Nat := 118140960795 + 3529407 * 2 ^ 59
def prefixEnd_3529407 : Nat := 4983230072969 + 3 ^ 40 * 3529407 * 2
def baseEnd_3529407 : Nat := 1208188144228785275054039

theorem tailTrace_3529407 : CollatzResearch.WordTrace tailWord_3529407 prefixEnd_3529407 1208188144228785275054039 := by
  unfold tailWord_3529407
  simp only [CollatzResearch.WordTrace]
  refine ⟨128728048724568688571362475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85818699149712459047574983 128728048724568688571362475)
  ·
    refine ⟨193092073086853032857043713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128728048724568688571362475 193092073086853032857043713)
    ·
      refine ⟨144819054815139774642782785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193092073086853032857043713 144819054815139774642782785)
      ·
        refine ⟨108614291111354830982087089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144819054815139774642782785 108614291111354830982087089)
        ·
          refine ⟨81460718333516123236565317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108614291111354830982087089 81460718333516123236565317)
          ·
            refine ⟨15273884687534273106855997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81460718333516123236565317 15273884687534273106855997)
            ·
              refine ⟨5727706757825352415070999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15273884687534273106855997 5727706757825352415070999)
              ·
                refine ⟨8591560136738028622606499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5727706757825352415070999 8591560136738028622606499)
                ·
                  refine ⟨12887340205107042933909749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591560136738028622606499 12887340205107042933909749)
                  ·
                    refine ⟨1208188144228785275054039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12887340205107042933909749 1208188144228785275054039)
                    ·
                      rfl

theorem cell22_3529407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_3529407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529407 prefixEnd_3529407 := by exact prefixLift 3529407
  have htrace : WordTrace (prefixWord ++ tailWord_3529407) baseStart_3529407 baseEnd_3529407 := by
    simpa [prefixWord, tailWord_3529407, baseEnd_3529407] using wordTrace_append hprefix tailTrace_3529407
  have hstable : (prefixWord ++ tailWord_3529407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529407).length < 2 ^ (prefixWord ++ tailWord_3529407).sum := by decide
  have hdescent : baseEnd_3529407 < baseStart_3529407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529422 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3529422 : Nat := 118140960795 + 3529422 * 2 ^ 59
def prefixEnd_3529422 : Nat := 4983230072969 + 3 ^ 40 * 3529422 * 2
def baseEnd_3529422 : Nat := 1208193279035330235928993

theorem tailTrace_3529422 : CollatzResearch.WordTrace tailWord_3529422 prefixEnd_3529422 1208193279035330235928993 := by
  unfold tailWord_3529422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16091074477439293266644815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85819063879676230755439013 16091074477439293266644815)
  ·
    refine ⟨24136611716158939899967223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16091074477439293266644815 24136611716158939899967223)
    ·
      refine ⟨36204917574238409849950835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24136611716158939899967223 36204917574238409849950835)
      ·
        refine ⟨54307376361357614774926253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36204917574238409849950835 54307376361357614774926253)
        ·
          refine ⟨20365266135509105540597345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54307376361357614774926253 20365266135509105540597345)
          ·
            refine ⟨15273949601631829155448009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20365266135509105540597345 15273949601631829155448009)
            ·
              refine ⟨11455462201223871866586007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15273949601631829155448009 11455462201223871866586007)
              ·
                refine ⟨17183193301835807799879011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11455462201223871866586007 17183193301835807799879011)
                ·
                  refine ⟨25774789952753711699818517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17183193301835807799879011 25774789952753711699818517)
                  ·
                    refine ⟨1208193279035330235928993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25774789952753711699818517 1208193279035330235928993)
                    ·
                      rfl

theorem cell22_3529422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3529422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529422 prefixEnd_3529422 := by exact prefixLift 3529422
  have htrace : WordTrace (prefixWord ++ tailWord_3529422) baseStart_3529422 baseEnd_3529422 := by
    simpa [prefixWord, tailWord_3529422, baseEnd_3529422] using wordTrace_append hprefix tailTrace_3529422
  have hstable : (prefixWord ++ tailWord_3529422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529422).length < 2 ^ (prefixWord ++ tailWord_3529422).sum := by decide
  have hdescent : baseEnd_3529422 < baseStart_3529422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529458 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_3529458 : Nat := 118140960795 + 3529458 * 2 ^ 59
def prefixEnd_3529458 : Nat := 4983230072969 + 3 ^ 40 * 3529458 * 2
def baseEnd_3529458 : Nat := 1208205602571038142028883

theorem tailTrace_3529458 : CollatzResearch.WordTrace tailWord_3529458 prefixEnd_3529458 1208205602571038142028883 := by
  unfold tailWord_3529458
  simp only [CollatzResearch.WordTrace]
  refine ⟨32182477211845981070367257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85819939231589282854312685 32182477211845981070367257)
  ·
    refine ⟨24136857908884485802775443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32182477211845981070367257 24136857908884485802775443)
    ·
      refine ⟨36205286863326728704163165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24136857908884485802775443 36205286863326728704163165)
      ·
        refine ⟨13576982573747523264061187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36205286863326728704163165 13576982573747523264061187)
        ·
          refine ⟨20365473860621284896091781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576982573747523264061187 20365473860621284896091781)
          ·
            refine ⟨3818526348866490918017209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20365473860621284896091781 3818526348866490918017209)
            ·
              refine ⟨2863894761649868188512907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818526348866490918017209 2863894761649868188512907)
              ·
                refine ⟨4295842142474802282769361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863894761649868188512907 4295842142474802282769361)
                ·
                  refine ⟨3221881606856101712077021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4295842142474802282769361 3221881606856101712077021)
                  ·
                    refine ⟨1208205602571038142028883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3221881606856101712077021 1208205602571038142028883)
                    ·
                      rfl

theorem cell22_3529458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_3529458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529458 prefixEnd_3529458 := by exact prefixLift 3529458
  have htrace : WordTrace (prefixWord ++ tailWord_3529458) baseStart_3529458 baseEnd_3529458 := by
    simpa [prefixWord, tailWord_3529458, baseEnd_3529458] using wordTrace_append hprefix tailTrace_3529458
  have hstable : (prefixWord ++ tailWord_3529458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529458).length < 2 ^ (prefixWord ++ tailWord_3529458).sum := by decide
  have hdescent : baseEnd_3529458 < baseStart_3529458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529486 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3529486 : Nat := 118140960795 + 3529486 * 2 ^ 59
def prefixEnd_3529486 : Nat := 4983230072969 + 3 ^ 40 * 3529486 * 2
def baseEnd_3529486 : Nat := 1208215187543255402328797

theorem tailTrace_3529486 : CollatzResearch.WordTrace tailWord_3529486 prefixEnd_3529486 1208215187543255402328797 := by
  unfold tailWord_3529486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16091366261410310632936039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85820620060854990042325541 16091366261410310632936039)
  ·
    refine ⟨24137049392115465949404059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16091366261410310632936039 24137049392115465949404059)
    ·
      refine ⟨36205574088173198924106089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24137049392115465949404059 36205574088173198924106089)
      ·
        refine ⟨27154180566129899193079567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36205574088173198924106089 27154180566129899193079567)
        ·
          refine ⟨40731270849194848789619351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27154180566129899193079567 40731270849194848789619351)
          ·
            refine ⟨61096906273792273184429027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40731270849194848789619351 61096906273792273184429027)
            ·
              refine ⟨91645359410688409776643541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61096906273792273184429027 91645359410688409776643541)
              ·
                refine ⟨2147938111188009604140083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91645359410688409776643541 2147938111188009604140083)
                ·
                  refine ⟨3221907166782014406210125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147938111188009604140083 3221907166782014406210125)
                  ·
                    refine ⟨1208215187543255402328797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3221907166782014406210125 1208215187543255402328797)
                    ·
                      rfl

theorem cell22_3529486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3529486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529486 prefixEnd_3529486 := by exact prefixLift 3529486
  have htrace : WordTrace (prefixWord ++ tailWord_3529486) baseStart_3529486 baseEnd_3529486 := by
    simpa [prefixWord, tailWord_3529486, baseEnd_3529486] using wordTrace_append hprefix tailTrace_3529486
  have hstable : (prefixWord ++ tailWord_3529486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529486).length < 2 ^ (prefixWord ++ tailWord_3529486).sum := by decide
  have hdescent : baseEnd_3529486 < baseStart_3529486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529503 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 1, 3]
def baseStart_3529503 : Nat := 118140960795 + 3529503 * 2 ^ 59
def prefixEnd_3529503 : Nat := 4983230072969 + 3 ^ 40 * 3529503 * 2
def baseEnd_3529503 : Nat := 1208221006990673024653745

theorem tailTrace_3529503 : CollatzResearch.WordTrace tailWord_3529503 prefixEnd_3529503 1208221006990673024653745 := by
  unfold tailWord_3529503
  simp only [CollatzResearch.WordTrace]
  refine ⟨128731550132220896966857163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85821033421480597977904775 128731550132220896966857163)
  ·
    refine ⟨193097325198331345450285745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128731550132220896966857163 193097325198331345450285745)
    ·
      refine ⟨144822993898748509087714309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193097325198331345450285745 144822993898748509087714309)
      ·
        refine ⟨27154311356015345453946433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144822993898748509087714309 27154311356015345453946433)
        ·
          refine ⟨20365733517011509090459825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27154311356015345453946433 20365733517011509090459825)
          ·
            refine ⟨15274300137758631817844869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20365733517011509090459825 15274300137758631817844869)
            ·
              refine ⟨2863931275829743465845913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15274300137758631817844869 2863931275829743465845913)
              ·
                refine ⟨2147948456872307599384435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863931275829743465845913 2147948456872307599384435)
                ·
                  refine ⟨3221922685308461399076653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147948456872307599384435 3221922685308461399076653)
                  ·
                    refine ⟨1208221006990673024653745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3221922685308461399076653 1208221006990673024653745)
                    ·
                      rfl

theorem cell22_3529503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_3529503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529503 prefixEnd_3529503 := by exact prefixLift 3529503
  have htrace : WordTrace (prefixWord ++ tailWord_3529503) baseStart_3529503 baseEnd_3529503 := by
    simpa [prefixWord, tailWord_3529503, baseEnd_3529503] using wordTrace_append hprefix tailTrace_3529503
  have hstable : (prefixWord ++ tailWord_3529503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529503).length < 2 ^ (prefixWord ++ tailWord_3529503).sum := by decide
  have hdescent : baseEnd_3529503 < baseStart_3529503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529527 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 6]
def baseStart_3529527 : Nat := 118140960795 + 3529527 * 2 ^ 59
def prefixEnd_3529527 : Nat := 4983230072969 + 3 ^ 40 * 3529527 * 2
def baseEnd_3529527 : Nat := 402743074227048320684557

theorem tailTrace_3529527 : CollatzResearch.WordTrace tailWord_3529527 prefixEnd_3529527 402743074227048320684557 := by
  unfold tailWord_3529527
  simp only [CollatzResearch.WordTrace]
  refine ⟨128732425484133949065730835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85821616989422632710487223 128732425484133949065730835)
  ·
    refine ⟨193098638226200923598596253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128732425484133949065730835 193098638226200923598596253)
    ·
      refine ⟨72411989334825346349473595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193098638226200923598596253 72411989334825346349473595)
      ·
        refine ⟨108617984002238019524210393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72411989334825346349473595 108617984002238019524210393)
        ·
          refine ⟨81463488001678514643157795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108617984002238019524210393 81463488001678514643157795)
          ·
            refine ⟨122195232002517771964736693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81463488001678514643157795 122195232002517771964736693)
            ·
              refine ⟨11455803000236041121694065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122195232002517771964736693 11455803000236041121694065)
              ·
                refine ⟨8591852250177030841270549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11455803000236041121694065 8591852250177030841270549)
                ·
                  refine ⟨402743074227048320684557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8591852250177030841270549 402743074227048320684557)
                  ·
                    rfl

theorem cell22_3529527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 6].length) (baseStart_3529527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529527 prefixEnd_3529527 := by exact prefixLift 3529527
  have htrace : WordTrace (prefixWord ++ tailWord_3529527) baseStart_3529527 baseEnd_3529527 := by
    simpa [prefixWord, tailWord_3529527, baseEnd_3529527] using wordTrace_append hprefix tailTrace_3529527
  have hstable : (prefixWord ++ tailWord_3529527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529527).length < 2 ^ (prefixWord ++ tailWord_3529527).sum := by decide
  have hdescent : baseEnd_3529527 < baseStart_3529527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529576 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_3529576 : Nat := 118140960795 + 3529576 * 2 ^ 59
def prefixEnd_3529576 : Nat := 4983230072969 + 3 ^ 40 * 3529576 * 2
def baseEnd_3529576 : Nat := 1208245996382525167578521

theorem tailTrace_3529576 : CollatzResearch.WordTrace tailWord_3529576 prefixEnd_3529576 1208245996382525167578521 := by
  unfold tailWord_3529576
  simp only [CollatzResearch.WordTrace]
  refine ⟨64367106330478215217132291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85822808440637620289509721 64367106330478215217132291)
  ·
    refine ⟨96550659495717322825698437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64367106330478215217132291 96550659495717322825698437)
    ·
      refine ⟨18103248655446998029818457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96550659495717322825698437 18103248655446998029818457)
      ·
        refine ⟨13577436491585248522363843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18103248655446998029818457 13577436491585248522363843)
        ·
          refine ⟨20366154737377872783545765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13577436491585248522363843 20366154737377872783545765)
          ·
            refine ⟨3818654013258351146914831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20366154737377872783545765 3818654013258351146914831)
            ·
              refine ⟨5727981019887526720372247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818654013258351146914831 5727981019887526720372247)
              ·
                refine ⟨8591971529831290080558371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5727981019887526720372247 8591971529831290080558371)
                ·
                  refine ⟨12887957294746935120837557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591971529831290080558371 12887957294746935120837557)
                  ·
                    refine ⟨1208245996382525167578521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12887957294746935120837557 1208245996382525167578521)
                    ·
                      rfl

theorem cell22_3529576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_3529576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529576 prefixEnd_3529576 := by exact prefixLift 3529576
  have htrace : WordTrace (prefixWord ++ tailWord_3529576) baseStart_3529576 baseEnd_3529576 := by
    simpa [prefixWord, tailWord_3529576, baseEnd_3529576] using wordTrace_append hprefix tailTrace_3529576
  have hstable : (prefixWord ++ tailWord_3529576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529576).length < 2 ^ (prefixWord ++ tailWord_3529576).sum := by decide
  have hdescent : baseEnd_3529576 < baseStart_3529576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529589 : List Nat := [1, 3, 4, 1, 1, 3, 1, 8]
def baseStart_3529589 : Nat := 118140960795 + 3529589 * 2 ^ 59
def prefixEnd_3529589 : Nat := 4983230072969 + 3 ^ 40 * 3529589 * 2
def baseEnd_3529589 : Nat := 134250049616466385222609

theorem tailTrace_3529589 : CollatzResearch.WordTrace tailWord_3529589 prefixEnd_3529589 134250049616466385222609 := by
  unfold tailWord_3529589
  simp only [CollatzResearch.WordTrace]
  refine ⟨128734686809909333654487821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85823124539939555769658547 128734686809909333654487821)
  ·
    refine ⟨48275507553716000120432933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128734686809909333654487821 48275507553716000120432933)
    ·
      refine ⟨9051657666321750022581175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48275507553716000120432933 9051657666321750022581175)
      ·
        refine ⟨13577486499482625033871763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051657666321750022581175 13577486499482625033871763)
        ·
          refine ⟨20366229749223937550807645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13577486499482625033871763 20366229749223937550807645)
          ·
            refine ⟨7637336155958976581552867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20366229749223937550807645 7637336155958976581552867)
            ·
              refine ⟨11456004233938464872329301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637336155958976581552867 11456004233938464872329301)
              ·
                refine ⟨134250049616466385222609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11456004233938464872329301 134250049616466385222609)
                ·
                  rfl

theorem cell22_3529589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 8].length) (baseStart_3529589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529589 prefixEnd_3529589 := by exact prefixLift 3529589
  have htrace : WordTrace (prefixWord ++ tailWord_3529589) baseStart_3529589 baseEnd_3529589 := by
    simpa [prefixWord, tailWord_3529589, baseEnd_3529589] using wordTrace_append hprefix tailTrace_3529589
  have hstable : (prefixWord ++ tailWord_3529589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529589).length < 2 ^ (prefixWord ++ tailWord_3529589).sum := by decide
  have hdescent : baseEnd_3529589 < baseStart_3529589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529621 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3529621 : Nat := 118140960795 + 3529621 * 2 ^ 59
def prefixEnd_3529621 : Nat := 4983230072969 + 3 ^ 40 * 3529621 * 2
def baseEnd_3529621 : Nat := 1208261400802160050203383

theorem tailTrace_3529621 : CollatzResearch.WordTrace tailWord_3529621 prefixEnd_3529621 1208261400802160050203383 := by
  unfold tailWord_3529621
  simp only [CollatzResearch.WordTrace]
  refine ⟨128735853945793403119652717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85823902630528935413101811 128735853945793403119652717)
  ·
    refine ⟨48275945229672526169869769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128735853945793403119652717 48275945229672526169869769)
    ·
      refine ⟨36206958922254394627402327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48275945229672526169869769 36206958922254394627402327)
      ·
        refine ⟨54310438383381591941103491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36206958922254394627402327 54310438383381591941103491)
        ·
          refine ⟨81465657575072387911655237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54310438383381591941103491 81465657575072387911655237)
          ·
            refine ⟨15274810795326072733435357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81465657575072387911655237 15274810795326072733435357)
            ·
              refine ⟨5728054048247277275038259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15274810795326072733435357 5728054048247277275038259)
              ·
                refine ⟨8592081072370915912557389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728054048247277275038259 8592081072370915912557389)
                ·
                  refine ⟨3222030402139093467209021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8592081072370915912557389 3222030402139093467209021)
                  ·
                    refine ⟨1208261400802160050203383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222030402139093467209021 1208261400802160050203383)
                    ·
                      rfl

theorem cell22_3529621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3529621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529621 prefixEnd_3529621 := by exact prefixLift 3529621
  have htrace : WordTrace (prefixWord ++ tailWord_3529621) baseStart_3529621 baseEnd_3529621 := by
    simpa [prefixWord, tailWord_3529621, baseEnd_3529621] using wordTrace_append hprefix tailTrace_3529621
  have hstable : (prefixWord ++ tailWord_3529621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529621).length < 2 ^ (prefixWord ++ tailWord_3529621).sum := by decide
  have hdescent : baseEnd_3529621 < baseStart_3529621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529672 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 1, 3]
def baseStart_3529672 : Nat := 118140960795 + 3529672 * 2 ^ 59
def prefixEnd_3529672 : Nat := 4983230072969 + 3 ^ 40 * 3529672 * 2
def baseEnd_3529672 : Nat := 1208278859144412917178227

theorem tailTrace_3529672 : CollatzResearch.WordTrace tailWord_3529672 prefixEnd_3529672 1208278859144412917178227 := by
  unfold tailWord_3529672
  simp only [CollatzResearch.WordTrace]
  refine ⟨64368857034304319414879635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85825142712405759219839513 64368857034304319414879635)
  ·
    refine ⟨96553285551456479122319453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64368857034304319414879635 96553285551456479122319453)
    ·
      refine ⟨36207482081796179670869795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96553285551456479122319453 36207482081796179670869795)
      ·
        refine ⟨54311223122694269506304693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36207482081796179670869795 54311223122694269506304693)
        ·
          refine ⟨5091677167752587766216065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54311223122694269506304693 5091677167752587766216065)
          ·
            refine ⟨3818757875814440824662049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5091677167752587766216065 3818757875814440824662049)
            ·
              refine ⟨2864068406860830618496537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818757875814440824662049 2864068406860830618496537)
              ·
                refine ⟨2148051305145622963872403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2864068406860830618496537 2148051305145622963872403)
                ·
                  refine ⟨3222076957718434445808605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148051305145622963872403 3222076957718434445808605)
                  ·
                    refine ⟨1208278859144412917178227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222076957718434445808605 1208278859144412917178227)
                    ·
                      rfl

theorem cell22_3529672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_3529672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529672 prefixEnd_3529672 := by exact prefixLift 3529672
  have htrace : WordTrace (prefixWord ++ tailWord_3529672) baseStart_3529672 baseEnd_3529672 := by
    simpa [prefixWord, tailWord_3529672, baseEnd_3529672] using wordTrace_append hprefix tailTrace_3529672
  have hstable : (prefixWord ++ tailWord_3529672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529672).length < 2 ^ (prefixWord ++ tailWord_3529672).sum := by decide
  have hdescent : baseEnd_3529672 < baseStart_3529672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529698 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3529698 : Nat := 118140960795 + 3529698 * 2 ^ 59
def prefixEnd_3529698 : Nat := 4983230072969 + 3 ^ 40 * 3529698 * 2
def baseEnd_3529698 : Nat := 1208287759475757516028147

theorem tailTrace_3529698 : CollatzResearch.WordTrace tailWord_3529698 prefixEnd_3529698 1208287759475757516028147 := by
  unfold tailWord_3529698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32184665591628611317551437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85825774911009630180137165 32184665591628611317551437)
  ·
    refine ⟨12069249596860729244081789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32184665591628611317551437 12069249596860729244081789)
    ·
      refine ⟨4525968598822773466530671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12069249596860729244081789 4525968598822773466530671)
      ·
        refine ⟨6788952898234160199796007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525968598822773466530671 6788952898234160199796007)
        ·
          refine ⟨10183429347351240299694011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788952898234160199796007 10183429347351240299694011)
          ·
            refine ⟨15275144021026860449541017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183429347351240299694011 15275144021026860449541017)
            ·
              refine ⟨11456358015770145337155763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15275144021026860449541017 11456358015770145337155763)
              ·
                refine ⟨17184537023655218005733645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11456358015770145337155763 17184537023655218005733645)
                ·
                  refine ⟨6444201383870706752150117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17184537023655218005733645 6444201383870706752150117)
                  ·
                    refine ⟨1208287759475757516028147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444201383870706752150117 1208287759475757516028147)
                    ·
                      rfl

theorem cell22_3529698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3529698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529698 prefixEnd_3529698 := by exact prefixLift 3529698
  have htrace : WordTrace (prefixWord ++ tailWord_3529698) baseStart_3529698 baseEnd_3529698 := by
    simpa [prefixWord, tailWord_3529698, baseEnd_3529698] using wordTrace_append hprefix tailTrace_3529698
  have hstable : (prefixWord ++ tailWord_3529698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529698).length < 2 ^ (prefixWord ++ tailWord_3529698).sum := by decide
  have hdescent : baseEnd_3529698 < baseStart_3529698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529713 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 4]
def baseStart_3529713 : Nat := 118140960795 + 3529713 * 2 ^ 59
def prefixEnd_3529713 : Nat := 4983230072969 + 3 ^ 40 * 3529713 * 2
def baseEnd_3529713 : Nat := 402764298094100825634367

theorem tailTrace_3529713 : CollatzResearch.WordTrace tailWord_3529713 prefixEnd_3529713 402764298094100825634367 := by
  unfold tailWord_3529713
  simp only [CollatzResearch.WordTrace]
  refine ⟨128739209461460102832001793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85826139640973401888001195 128739209461460102832001793)
  ·
    refine ⟨96554407096095077124001345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128739209461460102832001793 96554407096095077124001345)
    ·
      refine ⟨72415805322071307843001009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96554407096095077124001345 72415805322071307843001009)
      ·
        refine ⟨54311853991553480882250757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72415805322071307843001009 54311853991553480882250757)
        ·
          refine ⟨10183472623416277665422017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54311853991553480882250757 10183472623416277665422017)
          ·
            refine ⟨7637604467562208249066513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10183472623416277665422017 7637604467562208249066513)
            ·
              refine ⟨5728203350671656186799885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7637604467562208249066513 5728203350671656186799885)
              ·
                refine ⟨2148076256501871070049957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5728203350671656186799885 2148076256501871070049957)
                ·
                  refine ⟨402764298094100825634367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2148076256501871070049957 402764298094100825634367)
                  ·
                    rfl

theorem cell22_3529713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_3529713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529713 prefixEnd_3529713 := by exact prefixLift 3529713
  have htrace : WordTrace (prefixWord ++ tailWord_3529713) baseStart_3529713 baseEnd_3529713 := by
    simpa [prefixWord, tailWord_3529713, baseEnd_3529713] using wordTrace_append hprefix tailTrace_3529713
  have hstable : (prefixWord ++ tailWord_3529713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529713).length < 2 ^ (prefixWord ++ tailWord_3529713).sum := by decide
  have hdescent : baseEnd_3529713 < baseStart_3529713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529724 : List Nat := [2, 2, 2, 1, 2, 4, 9]
def baseStart_3529724 : Nat := 118140960795 + 3529724 * 2 ^ 59
def prefixEnd_3529724 : Nat := 4983230072969 + 3 ^ 40 * 3529724 * 2
def baseEnd_3529724 : Nat := 44751728141003782032521

theorem tailTrace_3529724 : CollatzResearch.WordTrace tailWord_3529724 prefixEnd_3529724 44751728141003782032521 := by
  unfold tailWord_3529724
  simp only [CollatzResearch.WordTrace]
  refine ⟨64369805332210125855326113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85826407109613501140434817 64369805332210125855326113)
  ·
    refine ⟨48277353999157594391494585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64369805332210125855326113 48277353999157594391494585)
    ·
      refine ⟨36208015499368195793620939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48277353999157594391494585 36208015499368195793620939)
      ·
        refine ⟨54312023249052293690431409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36208015499368195793620939 54312023249052293690431409)
        ·
          refine ⟨40734017436789220267823557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54312023249052293690431409 40734017436789220267823557)
          ·
            refine ⟨7637628269397978800216917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40734017436789220267823557 7637628269397978800216917)
            ·
              refine ⟨44751728141003782032521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7637628269397978800216917 44751728141003782032521)
              ·
                rfl

theorem cell22_3529724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 9].length) (baseStart_3529724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529724 prefixEnd_3529724 := by exact prefixLift 3529724
  have htrace : WordTrace (prefixWord ++ tailWord_3529724) baseStart_3529724 baseEnd_3529724 := by
    simpa [prefixWord, tailWord_3529724, baseEnd_3529724] using wordTrace_append hprefix tailTrace_3529724
  have hstable : (prefixWord ++ tailWord_3529724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529724).length < 2 ^ (prefixWord ++ tailWord_3529724).sum := by decide
  have hdescent : baseEnd_3529724 < baseStart_3529724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529730 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3529730 : Nat := 118140960795 + 3529730 * 2 ^ 59
def prefixEnd_3529730 : Nat := 4983230072969 + 3 ^ 40 * 3529730 * 2
def baseEnd_3529730 : Nat := 402766237909906699742683

theorem tailTrace_3529730 : CollatzResearch.WordTrace tailWord_3529730 prefixEnd_3529730 402766237909906699742683 := by
  unfold tailWord_3529730
  simp only [CollatzResearch.WordTrace]
  refine ⟨32184957375599628683842661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85826553001599009823580429 32184957375599628683842661)
  ·
    refine ⟨6034679507924930378220499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32184957375599628683842661 6034679507924930378220499)
    ·
      refine ⟨9052019261887395567330749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034679507924930378220499 9052019261887395567330749)
      ·
        refine ⟨3394507223207773337749031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9052019261887395567330749 3394507223207773337749031)
        ·
          refine ⟨5091760834811660006623547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394507223207773337749031 5091760834811660006623547)
          ·
            refine ⟨7637641252217490009935321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091760834811660006623547 7637641252217490009935321)
            ·
              refine ⟨5728230939163117507451491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7637641252217490009935321 5728230939163117507451491)
              ·
                refine ⟨8592346408744676261177237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728230939163117507451491 8592346408744676261177237)
                ·
                  refine ⟨402766237909906699742683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8592346408744676261177237 402766237909906699742683)
                  ·
                    rfl

theorem cell22_3529730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3529730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529730 prefixEnd_3529730 := by exact prefixLift 3529730
  have htrace : WordTrace (prefixWord ++ tailWord_3529730) baseStart_3529730 baseEnd_3529730 := by
    simpa [prefixWord, tailWord_3529730, baseEnd_3529730] using wordTrace_append hprefix tailTrace_3529730
  have hstable : (prefixWord ++ tailWord_3529730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529730).length < 2 ^ (prefixWord ++ tailWord_3529730).sum := by decide
  have hdescent : baseEnd_3529730 < baseStart_3529730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529790 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3529790 : Nat := 118140960795 + 3529790 * 2 ^ 59
def prefixEnd_3529790 : Nat := 4983230072969 + 3 ^ 40 * 3529790 * 2
def baseEnd_3529790 : Nat := 1208319252955899942727865

theorem tailTrace_3529790 : CollatzResearch.WordTrace tailWord_3529790 prefixEnd_3529790 1208319252955899942727865 := by
  unfold tailWord_3529790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092752235272643122819353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85828011921454096655036549 16092752235272643122819353)
  ·
    refine ⟨12069564176454482342114515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16092752235272643122819353 12069564176454482342114515)
    ·
      refine ⟨18104346264681723513171773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12069564176454482342114515 18104346264681723513171773)
      ·
        refine ⟨6789129849255646317439415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18104346264681723513171773 6789129849255646317439415)
        ·
          refine ⟨10183694773883469476159123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789129849255646317439415 10183694773883469476159123)
          ·
            refine ⟨15275542160825204214238685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183694773883469476159123 15275542160825204214238685)
            ·
              refine ⟨5728328310309451580339507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15275542160825204214238685 5728328310309451580339507)
              ·
                refine ⟨8592492465464177370509261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728328310309451580339507 8592492465464177370509261)
                ·
                  refine ⟨3222184674549066513940973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8592492465464177370509261 3222184674549066513940973)
                  ·
                    refine ⟨1208319252955899942727865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222184674549066513940973 1208319252955899942727865)
                    ·
                      rfl

theorem cell22_3529790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3529790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529790 prefixEnd_3529790 := by exact prefixLift 3529790
  have htrace : WordTrace (prefixWord ++ tailWord_3529790) baseStart_3529790 baseEnd_3529790 := by
    simpa [prefixWord, tailWord_3529790, baseEnd_3529790] using wordTrace_append hprefix tailTrace_3529790
  have hstable : (prefixWord ++ tailWord_3529790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529790).length < 2 ^ (prefixWord ++ tailWord_3529790).sum := by decide
  have hdescent : baseEnd_3529790 < baseStart_3529790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529816 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_3529816 : Nat := 118140960795 + 3529816 * 2 ^ 59
def prefixEnd_3529816 : Nat := 4983230072969 + 3 ^ 40 * 3529816 * 2
def baseEnd_3529816 : Nat := 1208328153287244541577785

theorem tailTrace_3529816 : CollatzResearch.WordTrace tailWord_3529816 prefixEnd_3529816 1208328153287244541577785 := by
  unfold tailWord_3529816
  simp only [CollatzResearch.WordTrace]
  refine ⟨64371483090043475711500651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85828644120057967615334201 64371483090043475711500651)
  ·
    refine ⟨96557224635065213567250977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64371483090043475711500651 96557224635065213567250977)
    ·
      refine ⟨72417918476298910175438233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96557224635065213567250977 72417918476298910175438233)
      ·
        refine ⟨54313438857224182631578675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72417918476298910175438233 54313438857224182631578675)
        ·
          refine ⟨81470158285836273947368013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54313438857224182631578675 81470158285836273947368013)
          ·
            refine ⟨30551309357188602730263005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81470158285836273947368013 30551309357188602730263005)
            ·
              refine ⟨11456741008945726023848627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30551309357188602730263005 11456741008945726023848627)
              ·
                refine ⟨17185111513418589035772941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11456741008945726023848627 17185111513418589035772941)
                ·
                  refine ⟨6444416817531970888414853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17185111513418589035772941 6444416817531970888414853)
                  ·
                    refine ⟨1208328153287244541577785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444416817531970888414853 1208328153287244541577785)
                    ·
                      rfl

theorem cell22_3529816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_3529816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529816 prefixEnd_3529816 := by exact prefixLift 3529816
  have htrace : WordTrace (prefixWord ++ tailWord_3529816) baseStart_3529816 baseEnd_3529816 := by
    simpa [prefixWord, tailWord_3529816, baseEnd_3529816] using wordTrace_append hprefix tailTrace_3529816
  have hstable : (prefixWord ++ tailWord_3529816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529816).length < 2 ^ (prefixWord ++ tailWord_3529816).sum := by decide
  have hdescent : baseEnd_3529816 < baseStart_3529816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529959 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3529959 : Nat := 118140960795 + 3529959 * 2 ^ 59
def prefixEnd_3529959 : Nat := 4983230072969 + 3 ^ 40 * 3529959 * 2
def baseEnd_3529959 : Nat := 1208377105109639835252347

theorem tailTrace_3529959 : CollatzResearch.WordTrace tailWord_3529959 prefixEnd_3529959 1208377105109639835252347 := by
  unfold tailWord_3529959
  simp only [CollatzResearch.WordTrace]
  refine ⟨128748181818568886845456931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85832121212379257896971287 128748181818568886845456931)
  ·
    refine ⟨193122272727853330268185397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128748181818568886845456931 193122272727853330268185397)
    ·
      refine ⟨18105213068236249712642381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193122272727853330268185397 18105213068236249712642381)
      ·
        refine ⟨6789454900588593642240893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18105213068236249712642381 6789454900588593642240893)
        ·
          refine ⟨2546045587720722615840335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6789454900588593642240893 2546045587720722615840335)
          ·
            refine ⟨3819068381581083923760503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546045587720722615840335 3819068381581083923760503)
            ·
              refine ⟨5728602572371625885640755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819068381581083923760503 5728602572371625885640755)
              ·
                refine ⟨8592903858557438828461133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728602572371625885640755 8592903858557438828461133)
                ·
                  refine ⟨3222338946959039560672925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8592903858557438828461133 3222338946959039560672925)
                  ·
                    refine ⟨1208377105109639835252347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222338946959039560672925 1208377105109639835252347)
                    ·
                      rfl

theorem cell22_3529959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3529959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529959 prefixEnd_3529959 := by exact prefixLift 3529959
  have htrace : WordTrace (prefixWord ++ tailWord_3529959) baseStart_3529959 baseEnd_3529959 := by
    simpa [prefixWord, tailWord_3529959, baseEnd_3529959] using wordTrace_append hprefix tailTrace_3529959
  have hstable : (prefixWord ++ tailWord_3529959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529959).length < 2 ^ (prefixWord ++ tailWord_3529959).sum := by decide
  have hdescent : baseEnd_3529959 < baseStart_3529959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529985 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3529985 : Nat := 118140960795 + 3529985 * 2 ^ 59
def prefixEnd_3529985 : Nat := 4983230072969 + 3 ^ 40 * 3529985 * 2
def baseEnd_3529985 : Nat := 1208386005440984434102267

theorem tailTrace_3529985 : CollatzResearch.WordTrace tailWord_3529985 prefixEnd_3529985 1208386005440984434102267 := by
  unfold tailWord_3529985
  simp only [CollatzResearch.WordTrace]
  refine ⟨128749130116474693285903409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85832753410983128857268939 128749130116474693285903409)
  ·
    refine ⟨96561847587356019964427557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128749130116474693285903409 96561847587356019964427557)
    ·
      refine ⟨18105346422629253743330167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96561847587356019964427557 18105346422629253743330167)
      ·
        refine ⟨27158019633943880614995251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18105346422629253743330167 27158019633943880614995251)
        ·
          refine ⟨40737029450915820922492877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27158019633943880614995251 40737029450915820922492877)
          ·
            refine ⟨15276386044093432845934829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40737029450915820922492877 15276386044093432845934829)
            ·
              refine ⟨5728644766535037317225561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15276386044093432845934829 5728644766535037317225561)
              ·
                refine ⟨4296483574901277987919171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728644766535037317225561 4296483574901277987919171)
                ·
                  refine ⟨6444725362351916981878757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296483574901277987919171 6444725362351916981878757)
                  ·
                    refine ⟨1208386005440984434102267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444725362351916981878757 1208386005440984434102267)
                    ·
                      rfl

theorem cell22_3529985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3529985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529985 prefixEnd_3529985 := by exact prefixLift 3529985
  have htrace : WordTrace (prefixWord ++ tailWord_3529985) baseStart_3529985 baseEnd_3529985 := by
    simpa [prefixWord, tailWord_3529985, baseEnd_3529985] using wordTrace_append hprefix tailTrace_3529985
  have hstable : (prefixWord ++ tailWord_3529985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529985).length < 2 ^ (prefixWord ++ tailWord_3529985).sum := by decide
  have hdescent : baseEnd_3529985 < baseStart_3529985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529998 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3529998 : Nat := 118140960795 + 3529998 * 2 ^ 59
def prefixEnd_3529998 : Nat := 4983230072969 + 3 ^ 40 * 3529998 * 2
def baseEnd_3529998 : Nat := 1208390455606656733527227

theorem tailTrace_3529998 : CollatzResearch.WordTrace tailWord_3529998 prefixEnd_3529998 1208390455606656733527227 := by
  unfold tailWord_3529998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093700533178449563265831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85833069510285064337417765 16093700533178449563265831)
  ·
    refine ⟨24140550799767674344898747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16093700533178449563265831 24140550799767674344898747)
    ·
      refine ⟨36210826199651511517348121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24140550799767674344898747 36210826199651511517348121)
      ·
        refine ⟨27158119649738633638011091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36210826199651511517348121 27158119649738633638011091)
        ·
          refine ⟨40737179474607950457016637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27158119649738633638011091 40737179474607950457016637)
          ·
            refine ⟨15276442302977981421381239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40737179474607950457016637 15276442302977981421381239)
            ·
              refine ⟨22914663454466972132071859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15276442302977981421381239 22914663454466972132071859)
              ·
                refine ⟨34371995181700458198107789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22914663454466972132071859 34371995181700458198107789)
                ·
                  refine ⟨12889498193137671824290421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34371995181700458198107789 12889498193137671824290421)
                  ·
                    refine ⟨1208390455606656733527227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12889498193137671824290421 1208390455606656733527227)
                    ·
                      rfl

theorem cell22_3529998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3529998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3529998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3529998 prefixEnd_3529998 := by exact prefixLift 3529998
  have htrace : WordTrace (prefixWord ++ tailWord_3529998) baseStart_3529998 baseEnd_3529998 := by
    simpa [prefixWord, tailWord_3529998, baseEnd_3529998] using wordTrace_append hprefix tailTrace_3529998
  have hstable : (prefixWord ++ tailWord_3529998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529998).length < 2 ^ (prefixWord ++ tailWord_3529998).sum := by decide
  have hdescent : baseEnd_3529998 < baseStart_3529998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530180 : List Nat := [2, 3, 3, 2, 1, 11]
def baseStart_3530180 : Nat := 118140960795 + 3530180 * 2 ^ 59
def prefixEnd_3530180 : Nat := 4983230072969 + 3 ^ 40 * 3530180 * 2
def baseEnd_3530180 : Nat := 14919169850939122536749

theorem tailTrace_3530180 : CollatzResearch.WordTrace tailWord_3530180 prefixEnd_3530180 14919169850939122536749 := by
  unfold tailWord_3530180
  simp only [CollatzResearch.WordTrace]
  refine ⟨64378121175384120794625997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85837494900512161059501329 64378121175384120794625997)
  ·
    refine ⟨24141795440769045297984749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64378121175384120794625997 24141795440769045297984749)
    ·
      refine ⟨9053173290288391986744281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24141795440769045297984749 9053173290288391986744281)
      ·
        refine ⟨6789879967716293990058211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9053173290288391986744281 6789879967716293990058211)
        ·
          refine ⟨10184819951574440985087317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789879967716293990058211 10184819951574440985087317)
          ·
            refine ⟨14919169850939122536749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10184819951574440985087317 14919169850939122536749)
            ·
              rfl

theorem cell22_3530180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 11].length) (baseStart_3530180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530180 prefixEnd_3530180 := by exact prefixLift 3530180
  have htrace : WordTrace (prefixWord ++ tailWord_3530180) baseStart_3530180 baseEnd_3530180 := by
    simpa [prefixWord, tailWord_3530180, baseEnd_3530180] using wordTrace_append hprefix tailTrace_3530180
  have hstable : (prefixWord ++ tailWord_3530180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530180).length < 2 ^ (prefixWord ++ tailWord_3530180).sum := by decide
  have hdescent : baseEnd_3530180 < baseStart_3530180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530280 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3530280 : Nat := 118140960795 + 3530280 * 2 ^ 59
def prefixEnd_3530280 : Nat := 4983230072969 + 3 ^ 40 * 3530280 * 2
def baseEnd_3530280 : Nat := 1208486989969701997976363

theorem tailTrace_3530280 : CollatzResearch.WordTrace tailWord_3530280 prefixEnd_3530280 1208486989969701997976363 := by
  unfold tailWord_3530280
  simp only [CollatzResearch.WordTrace]
  refine ⟨64379944825202979333946147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85839926433603972445261529 64379944825202979333946147)
  ·
    refine ⟨96569917237804469000919221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64379944825202979333946147 96569917237804469000919221)
    ·
      refine ⟨9053429741044168968836177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96569917237804469000919221 9053429741044168968836177)
      ·
        refine ⟨6790072305783126726627133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9053429741044168968836177 6790072305783126726627133)
        ·
          refine ⟨2546277114668672522485175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6790072305783126726627133 2546277114668672522485175)
          ·
            refine ⟨3819415672003008783727763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546277114668672522485175 3819415672003008783727763)
            ·
              refine ⟨5729123508004513175591645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819415672003008783727763 5729123508004513175591645)
              ·
                refine ⟨2148421315501692440846867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5729123508004513175591645 2148421315501692440846867)
                ·
                  refine ⟨3222631973252538661270301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148421315501692440846867 3222631973252538661270301)
                  ·
                    refine ⟨1208486989969701997976363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222631973252538661270301 1208486989969701997976363)
                    ·
                      rfl

theorem cell22_3530280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3530280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530280 prefixEnd_3530280 := by exact prefixLift 3530280
  have htrace : WordTrace (prefixWord ++ tailWord_3530280) baseStart_3530280 baseEnd_3530280 := by
    simpa [prefixWord, tailWord_3530280, baseEnd_3530280] using wordTrace_append hprefix tailTrace_3530280
  have hstable : (prefixWord ++ tailWord_3530280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530280).length < 2 ^ (prefixWord ++ tailWord_3530280).sum := by decide
  have hdescent : baseEnd_3530280 < baseStart_3530280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530310 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3530310 : Nat := 118140960795 + 3530310 * 2 ^ 59
def prefixEnd_3530310 : Nat := 4983230072969 + 3 ^ 40 * 3530310 * 2
def baseEnd_3530310 : Nat := 402832419860930639908757

theorem tailTrace_3530310 : CollatzResearch.WordTrace tailWord_3530310 prefixEnd_3530310 402832419860930639908757 := by
  unfold tailWord_3530310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023780745009289805983887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85840655893531515860989589 4023780745009289805983887)
  ·
    refine ⟨6035671117513934708975831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023780745009289805983887 6035671117513934708975831)
    ·
      refine ⟨9053506676270902063463747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035671117513934708975831 9053506676270902063463747)
      ·
        refine ⟨13580260014406353095195621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053506676270902063463747 13580260014406353095195621)
        ·
          refine ⟨2546298752701191205349179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13580260014406353095195621 2546298752701191205349179)
          ·
            refine ⟨3819448129051786808023769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546298752701191205349179 3819448129051786808023769)
            ·
              refine ⟨2864586096788840106017827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819448129051786808023769 2864586096788840106017827)
              ·
                refine ⟨4296879145183260159026741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864586096788840106017827 4296879145183260159026741)
                ·
                  refine ⟨402832419860930639908757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4296879145183260159026741 402832419860930639908757)
                  ·
                    rfl

theorem cell22_3530310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3530310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530310 prefixEnd_3530310 := by exact prefixLift 3530310
  have htrace : WordTrace (prefixWord ++ tailWord_3530310) baseStart_3530310 baseEnd_3530310 := by
    simpa [prefixWord, tailWord_3530310, baseEnd_3530310] using wordTrace_append hprefix tailTrace_3530310
  have hstable : (prefixWord ++ tailWord_3530310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530310).length < 2 ^ (prefixWord ++ tailWord_3530310).sum := by decide
  have hdescent : baseEnd_3530310 < baseStart_3530310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530330 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_3530330 : Nat := 118140960795 + 3530330 * 2 ^ 59
def prefixEnd_3530330 : Nat := 4983230072969 + 3 ^ 40 * 3530330 * 2
def baseEnd_3530330 : Nat := 1208504105991518534226209

theorem tailTrace_3530330 : CollatzResearch.WordTrace tailWord_3530330 prefixEnd_3530330 1208504105991518534226209 := by
  unfold tailWord_3530330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32190428325056204301803111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85841142200149878138141629 32190428325056204301803111)
  ·
    refine ⟨48285642487584306452704667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32190428325056204301803111 48285642487584306452704667)
    ·
      refine ⟨72428463731376459679057001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48285642487584306452704667 72428463731376459679057001)
      ·
        refine ⟨54321347798532344759292751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72428463731376459679057001 54321347798532344759292751)
        ·
          refine ⟨81482021697798517138939127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54321347798532344759292751 81482021697798517138939127)
          ·
            refine ⟨122223032546697775708408691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81482021697798517138939127 122223032546697775708408691)
            ·
              refine ⟨183334548820046663562613037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122223032546697775708408691 183334548820046663562613037)
              ·
                refine ⟨68750455807517498835979889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183334548820046663562613037 68750455807517498835979889)
                ·
                  refine ⟨51562841855638124126984917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68750455807517498835979889 51562841855638124126984917)
                  ·
                    refine ⟨1208504105991518534226209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51562841855638124126984917 1208504105991518534226209)
                    ·
                      rfl

theorem cell22_3530330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_3530330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530330 prefixEnd_3530330 := by exact prefixLift 3530330
  have htrace : WordTrace (prefixWord ++ tailWord_3530330) baseStart_3530330 baseEnd_3530330 := by
    simpa [prefixWord, tailWord_3530330, baseEnd_3530330] using wordTrace_append hprefix tailTrace_3530330
  have hstable : (prefixWord ++ tailWord_3530330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530330).length < 2 ^ (prefixWord ++ tailWord_3530330).sum := by decide
  have hdescent : baseEnd_3530330 < baseStart_3530330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530332 : List Nat := [2, 2, 4, 1, 2, 1, 2, 8]
def baseStart_3530332 : Nat := 118140960795 + 3530332 * 2 ^ 59
def prefixEnd_3530332 : Nat := 4983230072969 + 3 ^ 40 * 3530332 * 2
def baseEnd_3530332 : Nat := 134278310070265688408467

theorem tailTrace_3530332 : CollatzResearch.WordTrace tailWord_3530332 prefixEnd_3530332 134278310070265688408467 := by
  unfold tailWord_3530332
  simp only [CollatzResearch.WordTrace]
  refine ⟨64380893123108785774392625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85841190830811714365856833 64380893123108785774392625)
  ·
    refine ⟨48285669842331589330794469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64380893123108785774392625 48285669842331589330794469)
    ·
      refine ⟨9053563095437172999523963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48285669842331589330794469 9053563095437172999523963)
      ·
        refine ⟨13580344643155759499285945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053563095437172999523963 13580344643155759499285945)
        ·
          refine ⟨10185258482366819624464459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13580344643155759499285945 10185258482366819624464459)
          ·
            refine ⟨15277887723550229436696689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10185258482366819624464459 15277887723550229436696689)
            ·
              refine ⟨11458415792662672077522517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15277887723550229436696689 11458415792662672077522517)
              ·
                refine ⟨134278310070265688408467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11458415792662672077522517 134278310070265688408467)
                ·
                  rfl

theorem cell22_3530332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_3530332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530332 prefixEnd_3530332 := by exact prefixLift 3530332
  have htrace : WordTrace (prefixWord ++ tailWord_3530332) baseStart_3530332 baseEnd_3530332 := by
    simpa [prefixWord, tailWord_3530332, baseEnd_3530332] using wordTrace_append hprefix tailTrace_3530332
  have hstable : (prefixWord ++ tailWord_3530332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530332).length < 2 ^ (prefixWord ++ tailWord_3530332).sum := by decide
  have hdescent : baseEnd_3530332 < baseStart_3530332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530377 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 5]
def baseStart_3530377 : Nat := 118140960795 + 3530377 * 2 ^ 59
def prefixEnd_3530377 : Nat := 4983230072969 + 3 ^ 40 * 3530377 * 2
def baseEnd_3530377 : Nat := 402840065017342026100355

theorem tailTrace_3530377 : CollatzResearch.WordTrace tailWord_3530377 prefixEnd_3530377 402840065017342026100355 := by
  unfold tailWord_3530377
  simp only [CollatzResearch.WordTrace]
  refine ⟨128763427531054544234173385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85842285020703029489448923 128763427531054544234173385)
  ·
    refine ⟨96572570648290908175630039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128763427531054544234173385 96572570648290908175630039)
    ·
      refine ⟨144858855972436362263445059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96572570648290908175630039 144858855972436362263445059)
      ·
        refine ⟨217288283958654543395167589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144858855972436362263445059 217288283958654543395167589)
        ·
          refine ⟨40741553242247726886593923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217288283958654543395167589 40741553242247726886593923)
          ·
            refine ⟨61112329863371590329890885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40741553242247726886593923 61112329863371590329890885)
            ·
              refine ⟨11458561849382173186854541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61112329863371590329890885 11458561849382173186854541)
              ·
                refine ⟨4296960693518314945070453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11458561849382173186854541 4296960693518314945070453)
                ·
                  refine ⟨402840065017342026100355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4296960693518314945070453 402840065017342026100355)
                  ·
                    rfl

theorem cell22_3530377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_3530377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530377 prefixEnd_3530377 := by exact prefixLift 3530377
  have htrace : WordTrace (prefixWord ++ tailWord_3530377) baseStart_3530377 baseEnd_3530377 := by
    simpa [prefixWord, tailWord_3530377, baseEnd_3530377] using wordTrace_append hprefix tailTrace_3530377
  have hstable : (prefixWord ++ tailWord_3530377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530377).length < 2 ^ (prefixWord ++ tailWord_3530377).sum := by decide
  have hdescent : baseEnd_3530377 < baseStart_3530377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530398 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3530398 : Nat := 118140960795 + 3530398 * 2 ^ 59
def prefixEnd_3530398 : Nat := 4983230072969 + 3 ^ 40 * 3530398 * 2
def baseEnd_3530398 : Nat := 1208527383781189023526001

theorem tailTrace_3530398 : CollatzResearch.WordTrace tailWord_3530398 prefixEnd_3530398 1208527383781189023526001 := by
  unfold tailWord_3530398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16095524182997308102585981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85842795642652309880458565 16095524182997308102585981)
  ·
    refine ⟨6035821568623990538469743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16095524182997308102585981 6035821568623990538469743)
    ·
      refine ⟨9053732352935985807704615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035821568623990538469743 9053732352935985807704615)
      ·
        refine ⟨13580598529403978711556923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053732352935985807704615 13580598529403978711556923)
        ·
          refine ⟨20370897794105968067335385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13580598529403978711556923 20370897794105968067335385)
          ·
            refine ⟨15278173345579476050501539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20370897794105968067335385 15278173345579476050501539)
            ·
              refine ⟨22917260018369214075752309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15278173345579476050501539 22917260018369214075752309)
              ·
                refine ⟨2148493126722113819601779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22917260018369214075752309 2148493126722113819601779)
                ·
                  refine ⟨3222739690083170729402669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148493126722113819601779 3222739690083170729402669)
                  ·
                    refine ⟨1208527383781189023526001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222739690083170729402669 1208527383781189023526001)
                    ·
                      rfl

theorem cell22_3530398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3530398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530398 prefixEnd_3530398 := by exact prefixLift 3530398
  have htrace : WordTrace (prefixWord ++ tailWord_3530398) baseStart_3530398 baseEnd_3530398 := by
    simpa [prefixWord, tailWord_3530398, baseEnd_3530398] using wordTrace_append hprefix tailTrace_3530398
  have hstable : (prefixWord ++ tailWord_3530398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530398).length < 2 ^ (prefixWord ++ tailWord_3530398).sum := by decide
  have hdescent : baseEnd_3530398 < baseStart_3530398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530469 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3530469 : Nat := 118140960795 + 3530469 * 2 ^ 59
def prefixEnd_3530469 : Nat := 4983230072969 + 3 ^ 40 * 3530469 * 2
def baseEnd_3530469 : Nat := 1208551688532168505000783

theorem tailTrace_3530469 : CollatzResearch.WordTrace tailWord_3530469 prefixEnd_3530469 1208551688532168505000783 := by
  unfold tailWord_3530469
  simp only [CollatzResearch.WordTrace]
  refine ⟨128766783046721243946522461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85844522031147495964348307 128766783046721243946522461)
  ·
    refine ⟨48287543642520466479945923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128766783046721243946522461 48287543642520466479945923)
    ·
      refine ⟨72431315463780699719918885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48287543642520466479945923 72431315463780699719918885)
      ·
        refine ⟨13580871649458881197484791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72431315463780699719918885 13580871649458881197484791)
        ·
          refine ⟨20371307474188321796227187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13580871649458881197484791 20371307474188321796227187)
          ·
            refine ⟨30556961211282482694340781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20371307474188321796227187 30556961211282482694340781)
            ·
              refine ⟨11458860454230931010377793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30556961211282482694340781 11458860454230931010377793)
              ·
                refine ⟨8594145340673198257783345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458860454230931010377793 8594145340673198257783345)
                ·
                  refine ⟨6445609005504898693337509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8594145340673198257783345 6445609005504898693337509)
                  ·
                    refine ⟨1208551688532168505000783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6445609005504898693337509 1208551688532168505000783)
                    ·
                      rfl

theorem cell22_3530469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3530469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530469 prefixEnd_3530469 := by exact prefixLift 3530469
  have htrace : WordTrace (prefixWord ++ tailWord_3530469) baseStart_3530469 baseEnd_3530469 := by
    simpa [prefixWord, tailWord_3530469, baseEnd_3530469] using wordTrace_append hprefix tailTrace_3530469
  have hstable : (prefixWord ++ tailWord_3530469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530469).length < 2 ^ (prefixWord ++ tailWord_3530469).sum := by decide
  have hdescent : baseEnd_3530469 < baseStart_3530469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530499 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 3, 3]
def baseStart_3530499 : Nat := 118140960795 + 3530499 * 2 ^ 59
def prefixEnd_3530499 : Nat := 4983230072969 + 3 ^ 40 * 3530499 * 2
def baseEnd_3530499 : Nat := 1208561958145258426750691

theorem tailTrace_3530499 : CollatzResearch.WordTrace tailWord_3530499 prefixEnd_3530499 1208561958145258426750691 := by
  unfold tailWord_3530499
  simp only [CollatzResearch.WordTrace]
  refine ⟨128767877236612559070114551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85845251491075039380076367 128767877236612559070114551)
  ·
    refine ⟨193151815854918838605171827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128767877236612559070114551 193151815854918838605171827)
    ·
      refine ⟨289727723782378257907757741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193151815854918838605171827 289727723782378257907757741)
      ·
        refine ⟨108647896418391846715409153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289727723782378257907757741 108647896418391846715409153)
        ·
          refine ⟨81485922313793885036556865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108647896418391846715409153 81485922313793885036556865)
          ·
            refine ⟨61114441735345413777417649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81485922313793885036556865 61114441735345413777417649)
            ·
              refine ⟨45835831301509060333063237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61114441735345413777417649 45835831301509060333063237)
              ·
                refine ⟨8594218369032948812449357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45835831301509060333063237 8594218369032948812449357)
                ·
                  refine ⟨3222831888387355804668509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8594218369032948812449357 3222831888387355804668509)
                  ·
                    refine ⟨1208561958145258426750691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222831888387355804668509 1208561958145258426750691)
                    ·
                      rfl

theorem cell22_3530499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 3].length) (baseStart_3530499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530499 prefixEnd_3530499 := by exact prefixLift 3530499
  have htrace : WordTrace (prefixWord ++ tailWord_3530499) baseStart_3530499 baseEnd_3530499 := by
    simpa [prefixWord, tailWord_3530499, baseEnd_3530499] using wordTrace_append hprefix tailTrace_3530499
  have hstable : (prefixWord ++ tailWord_3530499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530499).length < 2 ^ (prefixWord ++ tailWord_3530499).sum := by decide
  have hdescent : baseEnd_3530499 < baseStart_3530499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530509 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3530509 : Nat := 118140960795 + 3530509 * 2 ^ 59
def prefixEnd_3530509 : Nat := 4983230072969 + 3 ^ 40 * 3530509 * 2
def baseEnd_3530509 : Nat := 1208565381349621734000661

theorem tailTrace_3530509 : CollatzResearch.WordTrace tailWord_3530509 prefixEnd_3530509 1208565381349621734000661 := by
  unfold tailWord_3530509
  simp only [CollatzResearch.WordTrace]
  refine ⟨128768241966576330777978581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85845494644384220518652387 128768241966576330777978581)
  ·
    refine ⟨3018005671091632752608873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 128768241966576330777978581 3018005671091632752608873)
    ·
      refine ⟨2263504253318724564456655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3018005671091632752608873 2263504253318724564456655)
      ·
        refine ⟨3395256379978086846684983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263504253318724564456655 3395256379978086846684983)
        ·
          refine ⟨5092884569967130270027475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395256379978086846684983 5092884569967130270027475)
          ·
            refine ⟨7639326854950695405041213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092884569967130270027475 7639326854950695405041213)
            ·
              refine ⟨2864747570606510776890455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7639326854950695405041213 2864747570606510776890455)
              ·
                refine ⟨4297121355909766165335683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864747570606510776890455 4297121355909766165335683)
                ·
                  refine ⟨6445682033864649248003525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297121355909766165335683 6445682033864649248003525)
                  ·
                    refine ⟨1208565381349621734000661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6445682033864649248003525 1208565381349621734000661)
                    ·
                      rfl

theorem cell22_3530509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3530509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530509 prefixEnd_3530509 := by exact prefixLift 3530509
  have htrace : WordTrace (prefixWord ++ tailWord_3530509) baseStart_3530509 baseEnd_3530509 := by
    simpa [prefixWord, tailWord_3530509, baseEnd_3530509] using wordTrace_append hprefix tailTrace_3530509
  have hstable : (prefixWord ++ tailWord_3530509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530509).length < 2 ^ (prefixWord ++ tailWord_3530509).sum := by decide
  have hdescent : baseEnd_3530509 < baseStart_3530509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530529 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 5]
def baseStart_3530529 : Nat := 118140960795 + 3530529 * 2 ^ 59
def prefixEnd_3530529 : Nat := 4983230072969 + 3 ^ 40 * 3530529 * 2
def baseEnd_3530529 : Nat := 402857409252782782833533

theorem tailTrace_3530529 : CollatzResearch.WordTrace tailWord_3530529 prefixEnd_3530529 402857409252782782833533 := by
  unfold tailWord_3530529
  simp only [CollatzResearch.WordTrace]
  refine ⟨128768971426503874193706641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85845980951002582795804427 128768971426503874193706641)
  ·
    refine ⟨96576728569877905645279981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128768971426503874193706641 96576728569877905645279981)
    ·
      refine ⟨36216273213704214616979993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96576728569877905645279981 36216273213704214616979993)
      ·
        refine ⟨27162204910278160962734995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36216273213704214616979993 27162204910278160962734995)
        ·
          refine ⟨40743307365417241444102493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27162204910278160962734995 40743307365417241444102493)
          ·
            refine ⟨15278740262031465541538435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40743307365417241444102493 15278740262031465541538435)
            ·
              refine ⟨22918110393047198312307653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15278740262031465541538435 22918110393047198312307653)
              ·
                refine ⟨4297145698696349683557685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22918110393047198312307653 4297145698696349683557685)
                ·
                  refine ⟨402857409252782782833533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4297145698696349683557685 402857409252782782833533)
                  ·
                    rfl

theorem cell22_3530529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_3530529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530529 prefixEnd_3530529 := by exact prefixLift 3530529
  have htrace : WordTrace (prefixWord ++ tailWord_3530529) baseStart_3530529 baseEnd_3530529 := by
    simpa [prefixWord, tailWord_3530529, baseEnd_3530529] using wordTrace_append hprefix tailTrace_3530529
  have hstable : (prefixWord ++ tailWord_3530529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530529).length < 2 ^ (prefixWord ++ tailWord_3530529).sum := by decide
  have hdescent : baseEnd_3530529 < baseStart_3530529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530533 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_3530533 : Nat := 118140960795 + 3530533 * 2 ^ 59
def prefixEnd_3530533 : Nat := 4983230072969 + 3 ^ 40 * 3530533 * 2
def baseEnd_3530533 : Nat := 1208573597040093671400587

theorem tailTrace_3530533 : CollatzResearch.WordTrace tailWord_3530533 prefixEnd_3530533 1208573597040093671400587 := by
  unfold tailWord_3530533
  simp only [CollatzResearch.WordTrace]
  refine ⟨128769117318489382876852253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85846078212326255251234835 128769117318489382876852253)
  ·
    refine ⟨48288418994433518578819595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128769117318489382876852253 48288418994433518578819595)
    ·
      refine ⟨72432628491650277868229393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48288418994433518578819595 72432628491650277868229393)
      ·
        refine ⟨54324471368737708401172045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72432628491650277868229393 54324471368737708401172045)
        ·
          refine ⟨20371676763276640650439517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54324471368737708401172045 20371676763276640650439517)
          ·
            refine ⟨7639378786228740243914819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20371676763276640650439517 7639378786228740243914819)
            ·
              refine ⟨11459068179343110365872229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639378786228740243914819 11459068179343110365872229)
              ·
                refine ⟨2148575283626833193601043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11459068179343110365872229 2148575283626833193601043)
                ·
                  refine ⟨3222862925440249790401565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148575283626833193601043 3222862925440249790401565)
                  ·
                    refine ⟨1208573597040093671400587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222862925440249790401565 1208573597040093671400587)
                    ·
                      rfl

theorem cell22_3530533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_3530533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530533 prefixEnd_3530533 := by exact prefixLift 3530533
  have htrace : WordTrace (prefixWord ++ tailWord_3530533) baseStart_3530533 baseEnd_3530533 := by
    simpa [prefixWord, tailWord_3530533, baseEnd_3530533] using wordTrace_append hprefix tailTrace_3530533
  have hstable : (prefixWord ++ tailWord_3530533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530533).length < 2 ^ (prefixWord ++ tailWord_3530533).sum := by decide
  have hdescent : baseEnd_3530533 < baseStart_3530533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530591 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 4]
def baseStart_3530591 : Nat := 118140960795 + 3530591 * 2 ^ 59
def prefixEnd_3530591 : Nat := 4983230072969 + 3 ^ 40 * 3530591 * 2
def baseEnd_3530591 : Nat := 402864483875133617816803

theorem tailTrace_3530591 : CollatzResearch.WordTrace tailWord_3530591 prefixEnd_3530591 402864483875133617816803 := by
  unfold tailWord_3530591
  simp only [CollatzResearch.WordTrace]
  refine ⟨128771232752279258782463627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85847488501519505854975751 128771232752279258782463627)
  ·
    refine ⟨193156849128418888173695441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128771232752279258782463627 193156849128418888173695441)
    ·
      refine ⟨144867636846314166130271581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193156849128418888173695441 144867636846314166130271581)
      ·
        refine ⟨54325363817367812298851843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144867636846314166130271581 54325363817367812298851843)
        ·
          refine ⟨81488045726051718448277765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54325363817367812298851843 81488045726051718448277765)
          ·
            refine ⟨15279008573634697209052081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81488045726051718448277765 15279008573634697209052081)
            ·
              refine ⟨11459256430226022906789061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15279008573634697209052081 11459256430226022906789061)
              ·
                refine ⟨2148610580667379295022949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11459256430226022906789061 2148610580667379295022949)
                ·
                  refine ⟨402864483875133617816803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2148610580667379295022949 402864483875133617816803)
                  ·
                    rfl

theorem cell22_3530591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 4].length) (baseStart_3530591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530591 prefixEnd_3530591 := by exact prefixLift 3530591
  have htrace : WordTrace (prefixWord ++ tailWord_3530591) baseStart_3530591 baseEnd_3530591 := by
    simpa [prefixWord, tailWord_3530591, baseEnd_3530591] using wordTrace_append hprefix tailTrace_3530591
  have hstable : (prefixWord ++ tailWord_3530591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530591).length < 2 ^ (prefixWord ++ tailWord_3530591).sum := by decide
  have hdescent : baseEnd_3530591 < baseStart_3530591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530604 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_3530604 : Nat := 118140960795 + 3530604 * 2 ^ 59
def prefixEnd_3530604 : Nat := 4983230072969 + 3 ^ 40 * 3530604 * 2
def baseEnd_3530604 : Nat := 1208597901791073152875369

theorem tailTrace_3530604 : CollatzResearch.WordTrace tailWord_3530604 prefixEnd_3530604 1208597901791073152875369 := by
  unfold tailWord_3530604
  simp only [CollatzResearch.WordTrace]
  refine ⟨64385853450616081001343433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85847804600821441335124577 64385853450616081001343433)
  ·
    refine ⟨48289390087962060751007575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64385853450616081001343433 48289390087962060751007575)
    ·
      refine ⟨72434085131943091126511363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48289390087962060751007575 72434085131943091126511363)
      ·
        refine ⟨108651127697914636689767045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72434085131943091126511363 108651127697914636689767045)
        ·
          refine ⟨20372086443358994379331321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108651127697914636689767045 20372086443358994379331321)
          ·
            refine ⟨15279064832519245784498491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20372086443358994379331321 15279064832519245784498491)
            ·
              refine ⟨22918597248778868676747737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279064832519245784498491 22918597248778868676747737)
              ·
                refine ⟨17188947936584151507560803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22918597248778868676747737 17188947936584151507560803)
                ·
                  refine ⟨25783421904876227261341205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17188947936584151507560803 25783421904876227261341205)
                  ·
                    refine ⟨1208597901791073152875369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25783421904876227261341205 1208597901791073152875369)
                    ·
                      rfl

theorem cell22_3530604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_3530604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530604 prefixEnd_3530604 := by exact prefixLift 3530604
  have htrace : WordTrace (prefixWord ++ tailWord_3530604) baseStart_3530604 baseEnd_3530604 := by
    simpa [prefixWord, tailWord_3530604, baseEnd_3530604] using wordTrace_append hprefix tailTrace_3530604
  have hstable : (prefixWord ++ tailWord_3530604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530604).length < 2 ^ (prefixWord ++ tailWord_3530604).sum := by decide
  have hdescent : baseEnd_3530604 < baseStart_3530604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530657 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 2, 3]
def baseStart_3530657 : Nat := 118140960795 + 3530657 * 2 ^ 59
def prefixEnd_3530657 : Nat := 4983230072969 + 3 ^ 40 * 3530657 * 2
def baseEnd_3530657 : Nat := 1208616044774198681300207

theorem tailTrace_3530657 : CollatzResearch.WordTrace tailWord_3530657 prefixEnd_3530657 1208616044774198681300207 := by
  unfold tailWord_3530657
  simp only [CollatzResearch.WordTrace]
  refine ⟨128773639970040152054366225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85849093313360101369577483 128773639970040152054366225)
  ·
    refine ⟨96580229977530114040774669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128773639970040152054366225 96580229977530114040774669)
    ·
      refine ⟨36217586241573792765290501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96580229977530114040774669 36217586241573792765290501)
      ·
        refine ⟨6790797420295086143491969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36217586241573792765290501 6790797420295086143491969)
        ·
          refine ⟨5093098065221314607618977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6790797420295086143491969 5093098065221314607618977)
          ·
            refine ⟨3819823548915985955714233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5093098065221314607618977 3819823548915985955714233)
            ·
              refine ⟨2864867661686989466785675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819823548915985955714233 2864867661686989466785675)
              ·
                refine ⟨4297301492530484200178513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864867661686989466785675 4297301492530484200178513)
                ·
                  refine ⟨3222976119397863150133885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297301492530484200178513 3222976119397863150133885)
                  ·
                    refine ⟨1208616044774198681300207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222976119397863150133885 1208616044774198681300207)
                    ·
                      rfl

theorem cell22_3530657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_3530657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530657 prefixEnd_3530657 := by exact prefixLift 3530657
  have htrace : WordTrace (prefixWord ++ tailWord_3530657) baseStart_3530657 baseEnd_3530657 := by
    simpa [prefixWord, tailWord_3530657, baseEnd_3530657] using wordTrace_append hprefix tailTrace_3530657
  have hstable : (prefixWord ++ tailWord_3530657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530657).length < 2 ^ (prefixWord ++ tailWord_3530657).sum := by decide
  have hdescent : baseEnd_3530657 < baseStart_3530657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530679 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3530679 : Nat := 118140960795 + 3530679 * 2 ^ 59
def prefixEnd_3530679 : Nat := 4983230072969 + 3 ^ 40 * 3530679 * 2
def baseEnd_3530679 : Nat := 1208623575823797957250139

theorem tailTrace_3530679 : CollatzResearch.WordTrace tailWord_3530679 prefixEnd_3530679 1208623575823797957250139 := by
  unfold tailWord_3530679
  simp only [CollatzResearch.WordTrace]
  refine ⟨128774442375960449811667091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85849628250640299874444727 128774442375960449811667091)
  ·
    refine ⟨193161663563940674717500637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128774442375960449811667091 193161663563940674717500637)
    ·
      refine ⟨72435623836477753019062739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193161663563940674717500637 72435623836477753019062739)
      ·
        refine ⟨108653435754716629528594109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72435623836477753019062739 108653435754716629528594109)
        ·
          refine ⟨40745038408018736073222791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108653435754716629528594109 40745038408018736073222791)
          ·
            refine ⟨61117557612028104109834187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40745038408018736073222791 61117557612028104109834187)
            ·
              refine ⟨91676336418042156164751281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61117557612028104109834187 91676336418042156164751281)
              ·
                refine ⟨68757252313531617123563461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91676336418042156164751281 68757252313531617123563461)
                ·
                  refine ⟨12891984808787178210668149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68757252313531617123563461 12891984808787178210668149)
                  ·
                    refine ⟨1208623575823797957250139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12891984808787178210668149 1208623575823797957250139)
                    ·
                      rfl

theorem cell22_3530679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3530679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530679 prefixEnd_3530679 := by exact prefixLift 3530679
  have htrace : WordTrace (prefixWord ++ tailWord_3530679) baseStart_3530679 baseEnd_3530679 := by
    simpa [prefixWord, tailWord_3530679, baseEnd_3530679] using wordTrace_append hprefix tailTrace_3530679
  have hstable : (prefixWord ++ tailWord_3530679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530679).length < 2 ^ (prefixWord ++ tailWord_3530679).sum := by decide
  have hdescent : baseEnd_3530679 < baseStart_3530679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530745 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 1, 4]
def baseStart_3530745 : Nat := 118140960795 + 3530745 * 2 ^ 59
def prefixEnd_3530745 : Nat := 4983230072969 + 3 ^ 40 * 3530745 * 2
def baseEnd_3530745 : Nat := 1208646168972595785099937

theorem tailTrace_3530745 : CollatzResearch.WordTrace tailWord_3530745 prefixEnd_3530745 1208646168972595785099937 := by
  unfold tailWord_3530745
  simp only [CollatzResearch.WordTrace]
  refine ⟨128776849593721343083569689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85851233062480895389046459 128776849593721343083569689)
  ·
    refine ⟨96582637195291007312677267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128776849593721343083569689 96582637195291007312677267)
    ·
      refine ⟨144873955792936510969015901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96582637195291007312677267 144873955792936510969015901)
      ·
        refine ⟨54327733422351191613380963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144873955792936510969015901 54327733422351191613380963)
        ·
          refine ⟨81491600133526787420071445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54327733422351191613380963 81491600133526787420071445)
          ·
            refine ⟨3819918756259068160315849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81491600133526787420071445 3819918756259068160315849)
            ·
              refine ⟨2864939067194301120236887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819918756259068160315849 2864939067194301120236887)
              ·
                refine ⟨4297408600791451680355331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864939067194301120236887 4297408600791451680355331)
                ·
                  refine ⟨6446112901187177520532997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297408600791451680355331 6446112901187177520532997)
                  ·
                    refine ⟨1208646168972595785099937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446112901187177520532997 1208646168972595785099937)
                    ·
                      rfl

theorem cell22_3530745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_3530745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530745 prefixEnd_3530745 := by exact prefixLift 3530745
  have htrace : WordTrace (prefixWord ++ tailWord_3530745) baseStart_3530745 baseEnd_3530745 := by
    simpa [prefixWord, tailWord_3530745, baseEnd_3530745] using wordTrace_append hprefix tailTrace_3530745
  have hstable : (prefixWord ++ tailWord_3530745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530745).length < 2 ^ (prefixWord ++ tailWord_3530745).sum := by decide
  have hdescent : baseEnd_3530745 < baseStart_3530745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530775 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 1, 5]
def baseStart_3530775 : Nat := 118140960795 + 3530775 * 2 ^ 59
def prefixEnd_3530775 : Nat := 4983230072969 + 3 ^ 40 * 3530775 * 2
def baseEnd_3530775 : Nat := 1208656438585685706849845

theorem tailTrace_3530775 : CollatzResearch.WordTrace tailWord_3530775 prefixEnd_3530775 1208656438585685706849845 := by
  unfold tailWord_3530775
  simp only [CollatzResearch.WordTrace]
  refine ⟨128777943783612658207161779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85851962522408438804774519 128777943783612658207161779)
  ·
    refine ⟨193166915675418987310742669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128777943783612658207161779 193166915675418987310742669)
    ·
      refine ⟨72437593378282120241528501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193166915675418987310742669 72437593378282120241528501)
      ·
        refine ⟨6791024379213948772643297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72437593378282120241528501 6791024379213948772643297)
        ·
          refine ⟨5093268284410461579482473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6791024379213948772643297 5093268284410461579482473)
          ·
            refine ⟨3819951213307846184611855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5093268284410461579482473 3819951213307846184611855)
            ·
              refine ⟨5729926819961769276917783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819951213307846184611855 5729926819961769276917783)
              ·
                refine ⟨8594890229942653915376675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729926819961769276917783 8594890229942653915376675)
                ·
                  refine ⟨12892335344913980873065013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8594890229942653915376675 12892335344913980873065013)
                  ·
                    refine ⟨1208656438585685706849845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12892335344913980873065013 1208656438585685706849845)
                    ·
                      rfl

theorem cell22_3530775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_3530775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530775 prefixEnd_3530775 := by exact prefixLift 3530775
  have htrace : WordTrace (prefixWord ++ tailWord_3530775) baseStart_3530775 baseEnd_3530775 := by
    simpa [prefixWord, tailWord_3530775, baseEnd_3530775] using wordTrace_append hprefix tailTrace_3530775
  have hstable : (prefixWord ++ tailWord_3530775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530775).length < 2 ^ (prefixWord ++ tailWord_3530775).sum := by decide
  have hdescent : baseEnd_3530775 < baseStart_3530775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530786 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3530786 : Nat := 118140960795 + 3530786 * 2 ^ 59
def prefixEnd_3530786 : Nat := 4983230072969 + 3 ^ 40 * 3530786 * 2
def baseEnd_3530786 : Nat := 1208660204110485344824811

theorem tailTrace_3530786 : CollatzResearch.WordTrace tailWord_3530786 prefixEnd_3530786 1208660204110485344824811 := by
  unfold tailWord_3530786
  simp only [CollatzResearch.WordTrace]
  refine ⟨32194586246643201771453053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85852229991048538057208141 32194586246643201771453053)
  ·
    refine ⟨12072969842491200664294895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32194586246643201771453053 12072969842491200664294895)
    ·
      refine ⟨18109454763736800996442343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12072969842491200664294895 18109454763736800996442343)
      ·
        refine ⟨27164182145605201494663515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18109454763736800996442343 27164182145605201494663515)
        ·
          refine ⟨40746273218407802241995273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27164182145605201494663515 40746273218407802241995273)
          ·
            refine ⟨30559704913805851681496455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40746273218407802241995273 30559704913805851681496455)
            ·
              refine ⟨45839557370708777522244683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30559704913805851681496455 45839557370708777522244683)
              ·
                refine ⟨68759336056063166283367025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45839557370708777522244683 68759336056063166283367025)
                ·
                  refine ⟨51569502042047374712525269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68759336056063166283367025 51569502042047374712525269)
                  ·
                    refine ⟨1208660204110485344824811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51569502042047374712525269 1208660204110485344824811)
                    ·
                      rfl

theorem cell22_3530786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3530786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530786 prefixEnd_3530786 := by exact prefixLift 3530786
  have htrace : WordTrace (prefixWord ++ tailWord_3530786) baseStart_3530786 baseEnd_3530786 := by
    simpa [prefixWord, tailWord_3530786, baseEnd_3530786] using wordTrace_append hprefix tailTrace_3530786
  have hstable : (prefixWord ++ tailWord_3530786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530786).length < 2 ^ (prefixWord ++ tailWord_3530786).sum := by decide
  have hdescent : baseEnd_3530786 < baseStart_3530786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530788 : List Nat := [2, 3, 1, 4, 2, 1, 1, 8]
def baseStart_3530788 : Nat := 118140960795 + 3530788 * 2 ^ 59
def prefixEnd_3530788 : Nat := 4983230072969 + 3 ^ 40 * 3530788 * 2
def baseEnd_3530788 : Nat := 134295654305706445141645

theorem tailTrace_3530788 : CollatzResearch.WordTrace tailWord_3530788 prefixEnd_3530788 134295654305706445141645 := by
  unfold tailWord_3530788
  simp only [CollatzResearch.WordTrace]
  refine ⟨64389208966282780713692509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85852278621710374284923345 64389208966282780713692509)
  ·
    refine ⟨24145953362356042767634691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64389208966282780713692509 24145953362356042767634691)
    ·
      refine ⟨36218930043534064151452037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24145953362356042767634691 36218930043534064151452037)
      ·
        refine ⟨6791049383162637028397257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36218930043534064151452037 6791049383162637028397257)
        ·
          refine ⟨5093287037371977771297943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6791049383162637028397257 5093287037371977771297943)
          ·
            refine ⟨7639930556057966656946915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093287037371977771297943 7639930556057966656946915)
            ·
              refine ⟨11459895834086949985420373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639930556057966656946915 11459895834086949985420373)
              ·
                refine ⟨134295654305706445141645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11459895834086949985420373 134295654305706445141645)
                ·
                  rfl

theorem cell22_3530788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_3530788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530788 prefixEnd_3530788 := by exact prefixLift 3530788
  have htrace : WordTrace (prefixWord ++ tailWord_3530788) baseStart_3530788 baseEnd_3530788 := by
    simpa [prefixWord, tailWord_3530788, baseEnd_3530788] using wordTrace_append hprefix tailTrace_3530788
  have hstable : (prefixWord ++ tailWord_3530788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530788).length < 2 ^ (prefixWord ++ tailWord_3530788).sum := by decide
  have hdescent : baseEnd_3530788 < baseStart_3530788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530816 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_3530816 : Nat := 118140960795 + 3530816 * 2 ^ 59
def prefixEnd_3530816 : Nat := 4983230072969 + 3 ^ 40 * 3530816 * 2
def baseEnd_3530816 : Nat := 402890157907858422191573

theorem tailTrace_3530816 : CollatzResearch.WordTrace tailWord_3530816 prefixEnd_3530816 402890157907858422191573 := by
  unfold tailWord_3530816
  simp only [CollatzResearch.WordTrace]
  refine ⟨64389719588232061104702151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85852959450976081472936201 64389719588232061104702151)
  ·
    refine ⟨96584579382348091657053227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64389719588232061104702151 96584579382348091657053227)
    ·
      refine ⟨144876869073522137485579841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96584579382348091657053227 144876869073522137485579841)
      ·
        refine ⟨108657651805141603114184881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144876869073522137485579841 108657651805141603114184881)
        ·
          refine ⟨81493238853856202335638661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108657651805141603114184881 81493238853856202335638661)
          ·
            refine ⟨15279982285098037937932249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81493238853856202335638661 15279982285098037937932249)
            ·
              refine ⟨11459986713823528453449187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15279982285098037937932249 11459986713823528453449187)
              ·
                refine ⟨17189980070735292680173781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11459986713823528453449187 17189980070735292680173781)
                ·
                  refine ⟨402890157907858422191573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17189980070735292680173781 402890157907858422191573)
                  ·
                    rfl

theorem cell22_3530816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_3530816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530816 prefixEnd_3530816 := by exact prefixLift 3530816
  have htrace : WordTrace (prefixWord ++ tailWord_3530816) baseStart_3530816 baseEnd_3530816 := by
    simpa [prefixWord, tailWord_3530816, baseEnd_3530816] using wordTrace_append hprefix tailTrace_3530816
  have hstable : (prefixWord ++ tailWord_3530816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530816).length < 2 ^ (prefixWord ++ tailWord_3530816).sum := by decide
  have hdescent : baseEnd_3530816 < baseStart_3530816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530908 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3530908 : Nat := 118140960795 + 3530908 * 2 ^ 59
def prefixEnd_3530908 : Nat := 4983230072969 + 3 ^ 40 * 3530908 * 2
def baseEnd_3530908 : Nat := 1208701967203717693274437

theorem tailTrace_3530908 : CollatzResearch.WordTrace tailWord_3530908 prefixEnd_3530908 1208701967203717693274437 := by
  unfold tailWord_3530908
  simp only [CollatzResearch.WordTrace]
  refine ⟨64391397346065410960876689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85855196461420547947835585 64391397346065410960876689)
  ·
    refine ⟨48293548009549058220657517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64391397346065410960876689 48293548009549058220657517)
    ·
      refine ⟨18110080503580896832746569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48293548009549058220657517 18110080503580896832746569)
      ·
        refine ⟨13582560377685672624559927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18110080503580896832746569 13582560377685672624559927)
        ·
          refine ⟨20373840566528508936839891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582560377685672624559927 20373840566528508936839891)
          ·
            refine ⟨30560760849792763405259837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20373840566528508936839891 30560760849792763405259837)
            ·
              refine ⟨11460285318672286276972439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30560760849792763405259837 11460285318672286276972439)
              ·
                refine ⟨17190427978008429415458659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11460285318672286276972439 17190427978008429415458659)
                ·
                  refine ⟨25785641967012644123187989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17190427978008429415458659 25785641967012644123187989)
                  ·
                    refine ⟨1208701967203717693274437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25785641967012644123187989 1208701967203717693274437)
                    ·
                      rfl

theorem cell22_3530908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3530908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530908 prefixEnd_3530908 := by exact prefixLift 3530908
  have htrace : WordTrace (prefixWord ++ tailWord_3530908) baseStart_3530908 baseEnd_3530908 := by
    simpa [prefixWord, tailWord_3530908, baseEnd_3530908] using wordTrace_append hprefix tailTrace_3530908
  have hstable : (prefixWord ++ tailWord_3530908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530908).length < 2 ^ (prefixWord ++ tailWord_3530908).sum := by decide
  have hdescent : baseEnd_3530908 < baseStart_3530908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530914 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3530914 : Nat := 118140960795 + 3530914 * 2 ^ 59
def prefixEnd_3530914 : Nat := 4983230072969 + 3 ^ 40 * 3530914 * 2
def baseEnd_3530914 : Nat := 1208704021126335677624419

theorem tailTrace_3530914 : CollatzResearch.WordTrace tailWord_3530914 prefixEnd_3530914 1208704021126335677624419 := by
  unfold tailWord_3530914
  simp only [CollatzResearch.WordTrace]
  refine ⟨32195753382527271236617949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85855342353406056630981197 32195753382527271236617949)
  ·
    refine ⟨12073407518447726713731731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32195753382527271236617949 12073407518447726713731731)
    ·
      refine ⟨18110111277671590070597597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12073407518447726713731731 18110111277671590070597597)
      ·
        refine ⟨6791291729126846276474099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18110111277671590070597597 6791291729126846276474099)
        ·
          refine ⟨10186937593690269414711149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6791291729126846276474099 10186937593690269414711149)
          ·
            refine ⟨3820101597633851030516681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10186937593690269414711149 3820101597633851030516681)
            ·
              refine ⟨2865076198225388272887511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820101597633851030516681 2865076198225388272887511)
              ·
                refine ⟨4297614297338082409331267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865076198225388272887511 4297614297338082409331267)
                ·
                  refine ⟨6446421446007123613996901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297614297338082409331267 6446421446007123613996901)
                  ·
                    refine ⟨1208704021126335677624419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446421446007123613996901 1208704021126335677624419)
                    ·
                      rfl

theorem cell22_3530914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3530914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530914 prefixEnd_3530914 := by exact prefixLift 3530914
  have htrace : WordTrace (prefixWord ++ tailWord_3530914) baseStart_3530914 baseEnd_3530914 := by
    simpa [prefixWord, tailWord_3530914, baseEnd_3530914] using wordTrace_append hprefix tailTrace_3530914
  have hstable : (prefixWord ++ tailWord_3530914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530914).length < 2 ^ (prefixWord ++ tailWord_3530914).sum := by decide
  have hdescent : baseEnd_3530914 < baseStart_3530914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530968 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_3530968 : Nat := 118140960795 + 3530968 * 2 ^ 59
def prefixEnd_3530968 : Nat := 4983230072969 + 3 ^ 40 * 3530968 * 2
def baseEnd_3530968 : Nat := 402907502143299178924751

theorem tailTrace_3530968 : CollatzResearch.WordTrace tailWord_3530968 prefixEnd_3530968 402907502143299178924751 := by
  unfold tailWord_3530968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64392491535956726084468779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85856655381275634779291705 64392491535956726084468779)
  ·
    refine ⟨96588737303935089126703169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64392491535956726084468779 96588737303935089126703169)
    ·
      refine ⟨72441552977951316845027377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96588737303935089126703169 72441552977951316845027377)
      ·
        refine ⟨54331164733463487633770533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72441552977951316845027377 54331164733463487633770533)
        ·
          refine ⟨10187093387524403931331975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54331164733463487633770533 10187093387524403931331975)
          ·
            refine ⟨15280640081286605896997963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10187093387524403931331975 15280640081286605896997963)
            ·
              refine ⟨22920960121929908845496945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15280640081286605896997963 22920960121929908845496945)
              ·
                refine ⟨17190720091447431634122709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22920960121929908845496945 17190720091447431634122709)
                ·
                  refine ⟨402907502143299178924751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17190720091447431634122709 402907502143299178924751)
                  ·
                    rfl

theorem cell22_3530968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_3530968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530968 prefixEnd_3530968 := by exact prefixLift 3530968
  have htrace : WordTrace (prefixWord ++ tailWord_3530968) baseStart_3530968 baseEnd_3530968 := by
    simpa [prefixWord, tailWord_3530968, baseEnd_3530968] using wordTrace_append hprefix tailTrace_3530968
  have hstable : (prefixWord ++ tailWord_3530968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530968).length < 2 ^ (prefixWord ++ tailWord_3530968).sum := by decide
  have hdescent : baseEnd_3530968 < baseStart_3530968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530989 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3530989 : Nat := 118140960795 + 3530989 * 2 ^ 59
def prefixEnd_3530989 : Nat := 4983230072969 + 3 ^ 40 * 3530989 * 2
def baseEnd_3530989 : Nat := 1208729695159060481999189

theorem tailTrace_3530989 : CollatzResearch.WordTrace tailWord_3530989 prefixEnd_3530989 1208729695159060481999189 := by
  unfold tailWord_3530989
  simp only [CollatzResearch.WordTrace]
  refine ⟨128785749004837372755452021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85857166003224915170301347 128785749004837372755452021)
  ·
    refine ⟨12073663969203503695823627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128785749004837372755452021 12073663969203503695823627)
    ·
      refine ⟨18110495953805255543735441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12073663969203503695823627 18110495953805255543735441)
      ·
        refine ⟨13582871965353941657801581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18110495953805255543735441 13582871965353941657801581)
        ·
          refine ⟨5093576987007728121675593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13582871965353941657801581 5093576987007728121675593)
          ·
            refine ⟨3820182740255796091256695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5093576987007728121675593 3820182740255796091256695)
            ·
              refine ⟨5730274110383694136885043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820182740255796091256695 5730274110383694136885043)
              ·
                refine ⟨8595411165575541205327565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730274110383694136885043 8595411165575541205327565)
                ·
                  refine ⟨3223279187090827951997837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8595411165575541205327565 3223279187090827951997837)
                  ·
                    refine ⟨1208729695159060481999189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223279187090827951997837 1208729695159060481999189)
                    ·
                      rfl

theorem cell22_3530989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3530989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3530989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3530989 prefixEnd_3530989 := by exact prefixLift 3530989
  have htrace : WordTrace (prefixWord ++ tailWord_3530989) baseStart_3530989 baseEnd_3530989 := by
    simpa [prefixWord, tailWord_3530989, baseEnd_3530989] using wordTrace_append hprefix tailTrace_3530989
  have hstable : (prefixWord ++ tailWord_3530989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530989).length < 2 ^ (prefixWord ++ tailWord_3530989).sum := by decide
  have hdescent : baseEnd_3530989 < baseStart_3530989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531002 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_3531002 : Nat := 118140960795 + 3531002 * 2 ^ 59
def prefixEnd_3531002 : Nat := 4983230072969 + 3 ^ 40 * 3531002 * 2
def baseEnd_3531002 : Nat := 402911381774910927141383

theorem tailTrace_3531002 : CollatzResearch.WordTrace tailWord_3531002 prefixEnd_3531002 402911381774910927141383 := by
  unfold tailWord_3531002
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196555788447568993918815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85857482102526850650450173 32196555788447568993918815)
  ·
    refine ⟨48294833682671353490878223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32196555788447568993918815 48294833682671353490878223)
    ·
      refine ⟨72442250524007030236317335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48294833682671353490878223 72442250524007030236317335)
      ·
        refine ⟨108663375786010545354476003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72442250524007030236317335 108663375786010545354476003)
        ·
          refine ⟨162995063679015818031714005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108663375786010545354476003 162995063679015818031714005)
          ·
            refine ⟨3820196804976933235118297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 162995063679015818031714005 3820196804976933235118297)
            ·
              refine ⟨2865147603732699926338723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820196804976933235118297 2865147603732699926338723)
              ·
                refine ⟨4297721405599049889508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865147603732699926338723 4297721405599049889508085)
                ·
                  refine ⟨402911381774910927141383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4297721405599049889508085 402911381774910927141383)
                  ·
                    rfl

theorem cell22_3531002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_3531002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531002 prefixEnd_3531002 := by exact prefixLift 3531002
  have htrace : WordTrace (prefixWord ++ tailWord_3531002) baseStart_3531002 baseEnd_3531002 := by
    simpa [prefixWord, tailWord_3531002, baseEnd_3531002] using wordTrace_append hprefix tailTrace_3531002
  have hstable : (prefixWord ++ tailWord_3531002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531002).length < 2 ^ (prefixWord ++ tailWord_3531002).sum := by decide
  have hdescent : baseEnd_3531002 < baseStart_3531002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531032 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 1, 4]
def baseStart_3531032 : Nat := 118140960795 + 3531032 * 2 ^ 59
def prefixEnd_3531032 : Nat := 4983230072969 + 3 ^ 40 * 3531032 * 2
def baseEnd_3531032 : Nat := 1208744414937822703174057

theorem tailTrace_3531032 : CollatzResearch.WordTrace tailWord_3531032 prefixEnd_3531032 1208744414937822703174057 := by
  unfold tailWord_3531032
  simp only [CollatzResearch.WordTrace]
  refine ⟨64393658671840795549633675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85858211562454394066178233 64393658671840795549633675)
  ·
    refine ⟨96590488007761193324450513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64393658671840795549633675 96590488007761193324450513)
    ·
      refine ⟨72442866005820894993337885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96590488007761193324450513 72442866005820894993337885)
      ·
        refine ⟨27166074752182835622501707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72442866005820894993337885 27166074752182835622501707)
        ·
          refine ⟨40749112128274253433752561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27166074752182835622501707 40749112128274253433752561)
          ·
            refine ⟨30561834096205690075314421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40749112128274253433752561 30561834096205690075314421)
            ·
              refine ⟨2865171946519283444560727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30561834096205690075314421 2865171946519283444560727)
              ·
                refine ⟨4297757919778925166841091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865171946519283444560727 4297757919778925166841091)
                ·
                  refine ⟨6446636879668387750261637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297757919778925166841091 6446636879668387750261637)
                  ·
                    refine ⟨1208744414937822703174057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446636879668387750261637 1208744414937822703174057)
                    ·
                      rfl

theorem cell22_3531032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_3531032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531032 prefixEnd_3531032 := by exact prefixLift 3531032
  have htrace : WordTrace (prefixWord ++ tailWord_3531032) baseStart_3531032 baseEnd_3531032 := by
    simpa [prefixWord, tailWord_3531032, baseEnd_3531032] using wordTrace_append hprefix tailTrace_3531032
  have hstable : (prefixWord ++ tailWord_3531032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531032).length < 2 ^ (prefixWord ++ tailWord_3531032).sum := by decide
  have hdescent : baseEnd_3531032 < baseStart_3531032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531107 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 3, 3]
def baseStart_3531107 : Nat := 118140960795 + 3531107 * 2 ^ 59
def prefixEnd_3531107 : Nat := 4983230072969 + 3 ^ 40 * 3531107 * 2
def baseEnd_3531107 : Nat := 1208770088970547507548827

theorem tailTrace_3531107 : CollatzResearch.WordTrace tailWord_3531107 prefixEnd_3531107 1208770088970547507548827 := by
  unfold tailWord_3531107
  simp only [CollatzResearch.WordTrace]
  refine ⟨128790052818409878908247575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85860035212273252605498383 128790052818409878908247575)
  ·
    refine ⟨193185079227614818362371363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128790052818409878908247575 193185079227614818362371363)
    ·
      refine ⟨289777618841422227543557045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193185079227614818362371363 289777618841422227543557045)
      ·
        refine ⟨27166651766383333832208473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289777618841422227543557045 27166651766383333832208473)
        ·
          refine ⟨20374988824787500374156355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27166651766383333832208473 20374988824787500374156355)
          ·
            refine ⟨30562483237181250561234533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374988824787500374156355 30562483237181250561234533)
            ·
              refine ⟨5730465606971484480231475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30562483237181250561234533 5730465606971484480231475)
              ·
                refine ⟨8595698410457226720347213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730465606971484480231475 8595698410457226720347213)
                ·
                  refine ⟨3223386903921460020130205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8595698410457226720347213 3223386903921460020130205)
                  ·
                    refine ⟨1208770088970547507548827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223386903921460020130205 1208770088970547507548827)
                    ·
                      rfl

theorem cell22_3531107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 3].length) (baseStart_3531107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531107 prefixEnd_3531107 := by exact prefixLift 3531107
  have htrace : WordTrace (prefixWord ++ tailWord_3531107) baseStart_3531107 baseEnd_3531107 := by
    simpa [prefixWord, tailWord_3531107, baseEnd_3531107] using wordTrace_append hprefix tailTrace_3531107
  have hstable : (prefixWord ++ tailWord_3531107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531107).length < 2 ^ (prefixWord ++ tailWord_3531107).sum := by decide
  have hdescent : baseEnd_3531107 < baseStart_3531107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531126 : List Nat := [5, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3531126 : Nat := 118140960795 + 3531126 * 2 ^ 59
def prefixEnd_3531126 : Nat := 4983230072969 + 3 ^ 40 * 3531126 * 2
def baseEnd_3531126 : Nat := 134308510339870865702641

theorem tailTrace_3531126 : CollatzResearch.WordTrace tailWord_3531126 prefixEnd_3531126 134308510339870865702641 := by
  unfold tailWord_3531126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049421612833815322074327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85860497203560696768792821 8049421612833815322074327)
  ·
    refine ⟨12074132419250722983111491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8049421612833815322074327 12074132419250722983111491)
    ·
      refine ⟨18111198628876084474667237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074132419250722983111491 18111198628876084474667237)
      ·
        refine ⟨3395849742914265839000107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18111198628876084474667237 3395849742914265839000107)
        ·
          refine ⟨5093774614371398758500161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395849742914265839000107 5093774614371398758500161)
          ·
            refine ⟨3820330960778549068875121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5093774614371398758500161 3820330960778549068875121)
            ·
              refine ⟨2865248220583911801656341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820330960778549068875121 2865248220583911801656341)
              ·
                refine ⟨134308510339870865702641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2865248220583911801656341 134308510339870865702641)
                ·
                  rfl

theorem cell22_3531126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3531126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531126 prefixEnd_3531126 := by exact prefixLift 3531126
  have htrace : WordTrace (prefixWord ++ tailWord_3531126) baseStart_3531126 baseEnd_3531126 := by
    simpa [prefixWord, tailWord_3531126, baseEnd_3531126] using wordTrace_append hprefix tailTrace_3531126
  have hstable : (prefixWord ++ tailWord_3531126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531126).length < 2 ^ (prefixWord ++ tailWord_3531126).sum := by decide
  have hdescent : baseEnd_3531126 < baseStart_3531126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531180 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_3531180 : Nat := 118140960795 + 3531180 * 2 ^ 59
def prefixEnd_3531180 : Nat := 4983230072969 + 3 ^ 40 * 3531180 * 2
def baseEnd_3531180 : Nat := 1208795078362399650473603

theorem tailTrace_3531180 : CollatzResearch.WordTrace tailWord_3531180 prefixEnd_3531180 1208795078362399650473603 := by
  unfold tailWord_3531180
  simp only [CollatzResearch.WordTrace]
  refine ⟨64396357673572706187827497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85861810231430274917103329 64396357673572706187827497)
  ·
    refine ⟨48297268255179529640870623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64396357673572706187827497 48297268255179529640870623)
    ·
      refine ⟨72445902382769294461305935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48297268255179529640870623 72445902382769294461305935)
      ·
        refine ⟨108668853574153941691958903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72445902382769294461305935 108668853574153941691958903)
        ·
          refine ⟨163003280361230912537938355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108668853574153941691958903 163003280361230912537938355)
          ·
            refine ⟨244504920541846368806907533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163003280361230912537938355 244504920541846368806907533)
            ·
              refine ⟨91689345203192388302590325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244504920541846368806907533 91689345203192388302590325)
              ·
                refine ⟨8595876112799286403367843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91689345203192388302590325 8595876112799286403367843)
                ·
                  refine ⟨12893814169198929605051765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595876112799286403367843 12893814169198929605051765)
                  ·
                    refine ⟨1208795078362399650473603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12893814169198929605051765 1208795078362399650473603)
                    ·
                      rfl

theorem cell22_3531180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_3531180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531180 prefixEnd_3531180 := by exact prefixLift 3531180
  have htrace : WordTrace (prefixWord ++ tailWord_3531180) baseStart_3531180 baseEnd_3531180 := by
    simpa [prefixWord, tailWord_3531180, baseEnd_3531180] using wordTrace_append hprefix tailTrace_3531180
  have hstable : (prefixWord ++ tailWord_3531180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531180).length < 2 ^ (prefixWord ++ tailWord_3531180).sum := by decide
  have hdescent : baseEnd_3531180 < baseStart_3531180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531197 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3531197 : Nat := 118140960795 + 3531197 * 2 ^ 59
def prefixEnd_3531197 : Nat := 4983230072969 + 3 ^ 40 * 3531197 * 2
def baseEnd_3531197 : Nat := 1208800897809817272798551

theorem tailTrace_3531197 : CollatzResearch.WordTrace tailWord_3531197 prefixEnd_3531197 1208800897809817272798551 := by
  unfold tailWord_3531197
  simp only [CollatzResearch.WordTrace]
  refine ⟨128793335388083824279023845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85862223592055882852682563 128793335388083824279023845)
  ·
    refine ⟨24148750385265717052316971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128793335388083824279023845 24148750385265717052316971)
    ·
      refine ⟨36223125577898575578475457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24148750385265717052316971 36223125577898575578475457)
      ·
        refine ⟨27167344183423931683856593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36223125577898575578475457 27167344183423931683856593)
        ·
          refine ⟨20375508137567948762892445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27167344183423931683856593 20375508137567948762892445)
          ·
            refine ⟨7640815551587980786084667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20375508137567948762892445 7640815551587980786084667)
            ·
              refine ⟨11461223327381971179127001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640815551587980786084667 11461223327381971179127001)
              ·
                refine ⟨8595917495536478384345251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11461223327381971179127001 8595917495536478384345251)
                ·
                  refine ⟨12893876243304717576517877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595917495536478384345251 12893876243304717576517877)
                  ·
                    refine ⟨1208800897809817272798551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12893876243304717576517877 1208800897809817272798551)
                    ·
                      rfl

theorem cell22_3531197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3531197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531197 prefixEnd_3531197 := by exact prefixLift 3531197
  have htrace : WordTrace (prefixWord ++ tailWord_3531197) baseStart_3531197 baseEnd_3531197 := by
    simpa [prefixWord, tailWord_3531197, baseEnd_3531197] using wordTrace_append hprefix tailTrace_3531197
  have hstable : (prefixWord ++ tailWord_3531197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531197).length < 2 ^ (prefixWord ++ tailWord_3531197).sum := by decide
  have hdescent : baseEnd_3531197 < baseStart_3531197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531276 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_3531276 : Nat := 118140960795 + 3531276 * 2 ^ 59
def prefixEnd_3531276 : Nat := 4983230072969 + 3 ^ 40 * 3531276 * 2
def baseEnd_3531276 : Nat := 1208827941124287400073309

theorem tailTrace_3531276 : CollatzResearch.WordTrace tailWord_3531276 prefixEnd_3531276 1208827941124287400073309 := by
  unfold tailWord_3531276
  simp only [CollatzResearch.WordTrace]
  refine ⟨64398108377398810385574841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85864144503198413847433121 64398108377398810385574841)
  ·
    refine ⟨48298581283049107789181131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64398108377398810385574841 48298581283049107789181131)
    ·
      refine ⟨72447871924573661683771697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48298581283049107789181131 72447871924573661683771697)
      ·
        refine ⟨54335903943430246262828773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72447871924573661683771697 54335903943430246262828773)
        ·
          refine ⟨10187981989393171174280395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54335903943430246262828773 10187981989393171174280395)
          ·
            refine ⟨15281972984089756761420593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10187981989393171174280395 15281972984089756761420593)
            ·
              refine ⟨11461479738067317571065445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15281972984089756761420593 11461479738067317571065445)
              ·
                refine ⟨2149027450887622044574771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11461479738067317571065445 2149027450887622044574771)
                ·
                  refine ⟨3223541176331433066862157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149027450887622044574771 3223541176331433066862157)
                  ·
                    refine ⟨1208827941124287400073309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223541176331433066862157 1208827941124287400073309)
                    ·
                      rfl

theorem cell22_3531276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_3531276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531276 prefixEnd_3531276 := by exact prefixLift 3531276
  have htrace : WordTrace (prefixWord ++ tailWord_3531276) baseStart_3531276 baseEnd_3531276 := by
    simpa [prefixWord, tailWord_3531276, baseEnd_3531276] using wordTrace_append hprefix tailTrace_3531276
  have hstable : (prefixWord ++ tailWord_3531276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531276).length < 2 ^ (prefixWord ++ tailWord_3531276).sum := by decide
  have hdescent : baseEnd_3531276 < baseStart_3531276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531310 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3531310 : Nat := 118140960795 + 3531310 * 2 ^ 59
def prefixEnd_3531310 : Nat := 4983230072969 + 3 ^ 40 * 3531310 * 2
def baseEnd_3531310 : Nat := 1208839580019122644723205

theorem tailTrace_3531310 : CollatzResearch.WordTrace tailWord_3531310 prefixEnd_3531310 1208839580019122644723205 := by
  unfold tailWord_3531310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16099682104584305572235923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85864971224449629718591589 16099682104584305572235923)
  ·
    refine ⟨24149523156876458358353885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16099682104584305572235923 24149523156876458358353885)
    ·
      refine ⟨9056071183828671884382707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24149523156876458358353885 9056071183828671884382707)
      ·
        refine ⟨13584106775743007826574061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056071183828671884382707 13584106775743007826574061)
        ·
          refine ⟨5094040040903627934965273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13584106775743007826574061 5094040040903627934965273)
          ·
            refine ⟨3820530030677720951223955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5094040040903627934965273 3820530030677720951223955)
            ·
              refine ⟨5730795046016581426835933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820530030677720951223955 5730795046016581426835933)
              ·
                refine ⟨2149048142256218035063475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5730795046016581426835933 2149048142256218035063475)
                ·
                  refine ⟨3223572213384327052595213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149048142256218035063475 3223572213384327052595213)
                  ·
                    refine ⟨1208839580019122644723205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223572213384327052595213 1208839580019122644723205)
                    ·
                      rfl

theorem cell22_3531310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3531310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531310 prefixEnd_3531310 := by exact prefixLift 3531310
  have htrace : WordTrace (prefixWord ++ tailWord_3531310) baseStart_3531310 baseEnd_3531310 := by
    simpa [prefixWord, tailWord_3531310, baseEnd_3531310] using wordTrace_append hprefix tailTrace_3531310
  have hstable : (prefixWord ++ tailWord_3531310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531310).length < 2 ^ (prefixWord ++ tailWord_3531310).sum := by decide
  have hdescent : baseEnd_3531310 < baseStart_3531310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531364 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_3531364 : Nat := 118140960795 + 3531364 * 2 ^ 59
def prefixEnd_3531364 : Nat := 4983230072969 + 3 ^ 40 * 3531364 * 2
def baseEnd_3531364 : Nat := 1208858065322684503873039

theorem tailTrace_3531364 : CollatzResearch.WordTrace tailWord_3531364 prefixEnd_3531364 1208858065322684503873039 := by
  unfold tailWord_3531364
  simp only [CollatzResearch.WordTrace]
  refine ⟨64399713189239405900176573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85866284252319207866902097 64399713189239405900176573)
  ·
    refine ⟨24149892445964777212566215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64399713189239405900176573 24149892445964777212566215)
    ·
      refine ⟨36224838668947165818849323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24149892445964777212566215 36224838668947165818849323)
      ·
        refine ⟨54337258003420748728273985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36224838668947165818849323 54337258003420748728273985)
        ·
          refine ⟨40752943502565561546205489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54337258003420748728273985 40752943502565561546205489)
          ·
            refine ⟨30564707626924171159654117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40752943502565561546205489 30564707626924171159654117)
            ·
              refine ⟨5730882680048282092435147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30564707626924171159654117 5730882680048282092435147)
              ·
                refine ⟨8596324020072423138652721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730882680048282092435147 8596324020072423138652721)
                ·
                  refine ⟨6447243015054317353989541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8596324020072423138652721 6447243015054317353989541)
                  ·
                    refine ⟨1208858065322684503873039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447243015054317353989541 1208858065322684503873039)
                    ·
                      rfl

theorem cell22_3531364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_3531364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531364 prefixEnd_3531364 := by exact prefixLift 3531364
  have htrace : WordTrace (prefixWord ++ tailWord_3531364) baseStart_3531364 baseEnd_3531364 := by
    simpa [prefixWord, tailWord_3531364, baseEnd_3531364] using wordTrace_append hprefix tailTrace_3531364
  have hstable : (prefixWord ++ tailWord_3531364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531364).length < 2 ^ (prefixWord ++ tailWord_3531364).sum := by decide
  have hdescent : baseEnd_3531364 < baseStart_3531364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531392 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_3531392 : Nat := 118140960795 + 3531392 * 2 ^ 59
def prefixEnd_3531392 : Nat := 4983230072969 + 3 ^ 40 * 3531392 * 2
def baseEnd_3531392 : Nat := 1208867650294901764172953

theorem tailTrace_3531392 : CollatzResearch.WordTrace tailWord_3531392 prefixEnd_3531392 1208867650294901764172953 := by
  unfold tailWord_3531392
  simp only [CollatzResearch.WordTrace]
  refine ⟨64400223811188686291186215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85866965081584915054914953 64400223811188686291186215)
  ·
    refine ⟨96600335716783029436779323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64400223811188686291186215 96600335716783029436779323)
    ·
      refine ⟨144900503575174544155168985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96600335716783029436779323 144900503575174544155168985)
      ·
        refine ⟨108675377681380908116376739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144900503575174544155168985 108675377681380908116376739)
        ·
          refine ⟨163013066522071362174565109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108675377681380908116376739 163013066522071362174565109)
          ·
            refine ⟨15282474986444190203865479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163013066522071362174565109 15282474986444190203865479)
            ·
              refine ⟨22923712479666285305798219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15282474986444190203865479 22923712479666285305798219)
              ·
                refine ⟨34385568719499427958697329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22923712479666285305798219 34385568719499427958697329)
                ·
                  refine ⟨25789176539624570969022997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34385568719499427958697329 25789176539624570969022997)
                  ·
                    refine ⟨1208867650294901764172953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25789176539624570969022997 1208867650294901764172953)
                    ·
                      rfl

theorem cell22_3531392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_3531392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531392 prefixEnd_3531392 := by exact prefixLift 3531392
  have htrace : WordTrace (prefixWord ++ tailWord_3531392) baseStart_3531392 baseEnd_3531392 := by
    simpa [prefixWord, tailWord_3531392, baseEnd_3531392] using wordTrace_append hprefix tailTrace_3531392
  have hstable : (prefixWord ++ tailWord_3531392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531392).length < 2 ^ (prefixWord ++ tailWord_3531392).sum := by decide
  have hdescent : baseEnd_3531392 < baseStart_3531392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531428 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_3531428 : Nat := 118140960795 + 3531428 * 2 ^ 59
def prefixEnd_3531428 : Nat := 4983230072969 + 3 ^ 40 * 3531428 * 2
def baseEnd_3531428 : Nat := 1208879973830609670272843

theorem tailTrace_3531428 : CollatzResearch.WordTrace tailWord_3531428 prefixEnd_3531428 1208879973830609670272843 := by
  unfold tailWord_3531428
  simp only [CollatzResearch.WordTrace]
  refine ⟨64400880325123475365341469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85867840433497967153788625 64400880325123475365341469)
  ·
    refine ⟨24150330121921303262003051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64400880325123475365341469 24150330121921303262003051)
    ·
      refine ⟨36225495182881954893004577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24150330121921303262003051 36225495182881954893004577)
      ·
        refine ⟨27169121387161466169753433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36225495182881954893004577 27169121387161466169753433)
        ·
          refine ⟨20376841040371099627315075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27169121387161466169753433 20376841040371099627315075)
          ·
            refine ⟨30565261560556649440972613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20376841040371099627315075 30565261560556649440972613)
            ·
              refine ⟨5730986542604371770182365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30565261560556649440972613 5730986542604371770182365)
              ·
                refine ⟨2149119953476639413818387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5730986542604371770182365 2149119953476639413818387)
                ·
                  refine ⟨3223679930214959120727581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149119953476639413818387 3223679930214959120727581)
                  ·
                    refine ⟨1208879973830609670272843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223679930214959120727581 1208879973830609670272843)
                    ·
                      rfl

theorem cell22_3531428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_3531428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531428 prefixEnd_3531428 := by exact prefixLift 3531428
  have htrace : WordTrace (prefixWord ++ tailWord_3531428) baseStart_3531428 baseEnd_3531428 := by
    simpa [prefixWord, tailWord_3531428, baseEnd_3531428] using wordTrace_append hprefix tailTrace_3531428
  have hstable : (prefixWord ++ tailWord_3531428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531428).length < 2 ^ (prefixWord ++ tailWord_3531428).sum := by decide
  have hdescent : baseEnd_3531428 < baseStart_3531428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531441 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 7]
def baseStart_3531441 : Nat := 118140960795 + 3531441 * 2 ^ 59
def prefixEnd_3531441 : Nat := 4983230072969 + 3 ^ 40 * 3531441 * 2
def baseEnd_3531441 : Nat := 402961474665427323232601

theorem tailTrace_3531441 : CollatzResearch.WordTrace tailWord_3531441 prefixEnd_3531441 402961474665427323232601 := by
  unfold tailWord_3531441
  simp only [CollatzResearch.WordTrace]
  refine ⟨128802234799199853950906177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85868156532799902633937451 128802234799199853950906177)
  ·
    refine ⟨96601676099399890463179633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128802234799199853950906177 96601676099399890463179633)
    ·
      refine ⟨72451257074549917847384725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96601676099399890463179633 72451257074549917847384725)
      ·
        refine ⟨3396152675369527399096159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72451257074549917847384725 3396152675369527399096159)
        ·
          refine ⟨5094229013054291098644239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396152675369527399096159 5094229013054291098644239)
          ·
            refine ⟨7641343519581436647966359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094229013054291098644239 7641343519581436647966359)
            ·
              refine ⟨11462015279372154971949539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641343519581436647966359 11462015279372154971949539)
              ·
                refine ⟨17193022919058232457924309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462015279372154971949539 17193022919058232457924309)
                ·
                  refine ⟨402961474665427323232601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17193022919058232457924309 402961474665427323232601)
                  ·
                    rfl

theorem cell22_3531441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_3531441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531441 prefixEnd_3531441 := by exact prefixLift 3531441
  have htrace : WordTrace (prefixWord ++ tailWord_3531441) baseStart_3531441 baseEnd_3531441 := by
    simpa [prefixWord, tailWord_3531441, baseEnd_3531441] using wordTrace_append hprefix tailTrace_3531441
  have hstable : (prefixWord ++ tailWord_3531441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531441).length < 2 ^ (prefixWord ++ tailWord_3531441).sum := by decide
  have hdescent : baseEnd_3531441 < baseStart_3531441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531497 : List Nat := [1, 2, 1, 1, 1, 2, 14]
def baseStart_3531497 : Nat := 118140960795 + 3531497 * 2 ^ 59
def prefixEnd_3531497 : Nat := 4983230072969 + 3 ^ 40 * 3531497 * 2
def baseEnd_3531497 : Nat := 44774207182989499640653

theorem tailTrace_3531497 : CollatzResearch.WordTrace tailWord_3531497 prefixEnd_3531497 44774207182989499640653 := by
  unfold tailWord_3531497
  simp only [CollatzResearch.WordTrace]
  refine ⟨128804277286996975514944745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85869518191331317009963163 128804277286996975514944745)
  ·
    refine ⟨96603207965247731636208559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128804277286996975514944745 96603207965247731636208559)
    ·
      refine ⟨144904811947871597454312839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96603207965247731636208559 144904811947871597454312839)
      ·
        refine ⟨217357217921807396181469259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144904811947871597454312839 217357217921807396181469259)
        ·
          refine ⟨326035826882711094272203889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217357217921807396181469259 326035826882711094272203889)
          ·
            refine ⟨244526870162033320704152917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326035826882711094272203889 244526870162033320704152917)
            ·
              refine ⟨44774207182989499640653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 244526870162033320704152917 44774207182989499640653)
              ·
                rfl

theorem cell22_3531497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 14].length) (baseStart_3531497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531497 prefixEnd_3531497 := by exact prefixLift 3531497
  have htrace : WordTrace (prefixWord ++ tailWord_3531497) baseStart_3531497 baseEnd_3531497 := by
    simpa [prefixWord, tailWord_3531497, baseEnd_3531497] using wordTrace_append hprefix tailTrace_3531497
  have hstable : (prefixWord ++ tailWord_3531497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531497).length < 2 ^ (prefixWord ++ tailWord_3531497).sum := by decide
  have hdescent : baseEnd_3531497 < baseStart_3531497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531501 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_3531501 : Nat := 118140960795 + 3531501 * 2 ^ 59
def prefixEnd_3531501 : Nat := 4983230072969 + 3 ^ 40 * 3531501 * 2
def baseEnd_3531501 : Nat := 1208904963222461813197619

theorem tailTrace_3531501 : CollatzResearch.WordTrace tailWord_3531501 prefixEnd_3531501 1208904963222461813197619 := by
  unfold tailWord_3531501
  simp only [CollatzResearch.WordTrace]
  refine ⟨128804423178982484198090357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85869615452654989465393571 128804423178982484198090357)
  ·
    refine ⟨12075414673029607893570971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128804423178982484198090357 12075414673029607893570971)
    ·
      refine ⟨18113122009544411840356457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12075414673029607893570971 18113122009544411840356457)
      ·
        refine ⟨13584841507158308880267343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18113122009544411840356457 13584841507158308880267343)
        ·
          refine ⟨20377262260737463320401015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584841507158308880267343 20377262260737463320401015)
          ·
            refine ⟨30565893391106194980601523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20377262260737463320401015 30565893391106194980601523)
            ·
              refine ⟨45848840086659292470902285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30565893391106194980601523 45848840086659292470902285)
              ·
                refine ⟨17193315032497234676588357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45848840086659292470902285 17193315032497234676588357)
                ·
                  refine ⟨3223746568593231501860317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17193315032497234676588357 3223746568593231501860317)
                  ·
                    refine ⟨1208904963222461813197619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223746568593231501860317 1208904963222461813197619)
                    ·
                      rfl

theorem cell22_3531501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_3531501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531501 prefixEnd_3531501 := by exact prefixLift 3531501
  have htrace : WordTrace (prefixWord ++ tailWord_3531501) baseStart_3531501 baseEnd_3531501 := by
    simpa [prefixWord, tailWord_3531501, baseEnd_3531501] using wordTrace_append hprefix tailTrace_3531501
  have hstable : (prefixWord ++ tailWord_3531501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531501).length < 2 ^ (prefixWord ++ tailWord_3531501).sum := by decide
  have hdescent : baseEnd_3531501 < baseStart_3531501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531503 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 4]
def baseStart_3531503 : Nat := 118140960795 + 3531503 * 2 ^ 59
def prefixEnd_3531503 : Nat := 4983230072969 + 3 ^ 40 * 3531503 * 2
def baseEnd_3531503 : Nat := 402968549287778158215871

theorem tailTrace_3531503 : CollatzResearch.WordTrace tailWord_3531503 prefixEnd_3531503 402968549287778158215871 := by
  unfold tailWord_3531503
  simp only [CollatzResearch.WordTrace]
  refine ⟨128804496124975238539663163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85869664083316825693108775 128804496124975238539663163)
  ·
    refine ⟨193206744187462857809494745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128804496124975238539663163 193206744187462857809494745)
    ·
      refine ⟨144905058140597143357121059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193206744187462857809494745 144905058140597143357121059)
      ·
        refine ⟨217357587210895715035681589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144905058140597143357121059 217357587210895715035681589)
        ·
          refine ⟨20377273801021473284595149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217357587210895715035681589 20377273801021473284595149)
          ·
            refine ⟨7641477675383052481723181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20377273801021473284595149 7641477675383052481723181)
            ·
              refine ⟨2865554128268644680646193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7641477675383052481723181 2865554128268644680646193)
              ·
                refine ⟨2149165596201483510484645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865554128268644680646193 2149165596201483510484645)
                ·
                  refine ⟨402968549287778158215871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149165596201483510484645 402968549287778158215871)
                  ·
                    rfl

theorem cell22_3531503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 4].length) (baseStart_3531503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531503 prefixEnd_3531503 := by exact prefixLift 3531503
  have htrace : WordTrace (prefixWord ++ tailWord_3531503) baseStart_3531503 baseEnd_3531503 := by
    simpa [prefixWord, tailWord_3531503, baseEnd_3531503] using wordTrace_append hprefix tailTrace_3531503
  have hstable : (prefixWord ++ tailWord_3531503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531503).length < 2 ^ (prefixWord ++ tailWord_3531503).sum := by decide
  have hdescent : baseEnd_3531503 < baseStart_3531503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531509 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 5]
def baseStart_3531509 : Nat := 118140960795 + 3531509 * 2 ^ 59
def prefixEnd_3531509 : Nat := 4983230072969 + 3 ^ 40 * 3531509 * 2
def baseEnd_3531509 : Nat := 402969233928650819665865

theorem tailTrace_3531509 : CollatzResearch.WordTrace tailWord_3531509 prefixEnd_3531509 402969233928650819665865 := by
  unfold tailWord_3531509
  simp only [CollatzResearch.WordTrace]
  refine ⟨128804714962953501564381581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85869809975302334376254387 128804714962953501564381581)
  ·
    refine ⟨48301768111107563086643093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128804714962953501564381581 48301768111107563086643093)
    ·
      refine ⟨2264145380208167019686395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48301768111107563086643093 2264145380208167019686395)
      ·
        refine ⟨3396218070312250529529593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264145380208167019686395 3396218070312250529529593)
        ·
          refine ⟨2547163552734187897147195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3396218070312250529529593 2547163552734187897147195)
          ·
            refine ⟨3820745329101281845720793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547163552734187897147195 3820745329101281845720793)
            ·
              refine ⟨2865558996825961384290595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820745329101281845720793 2865558996825961384290595)
              ·
                refine ⟨4298338495238942076435893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865558996825961384290595 4298338495238942076435893)
                ·
                  refine ⟨402969233928650819665865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4298338495238942076435893 402969233928650819665865)
                  ·
                    rfl

theorem cell22_3531509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_3531509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531509 prefixEnd_3531509 := by exact prefixLift 3531509
  have htrace : WordTrace (prefixWord ++ tailWord_3531509) baseStart_3531509 baseEnd_3531509 := by
    simpa [prefixWord, tailWord_3531509, baseEnd_3531509] using wordTrace_append hprefix tailTrace_3531509
  have hstable : (prefixWord ++ tailWord_3531509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531509).length < 2 ^ (prefixWord ++ tailWord_3531509).sum := by decide
  have hdescent : baseEnd_3531509 < baseStart_3531509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531565 : List Nat := [1, 5, 3, 2, 1, 2, 1, 7]
def baseStart_3531565 : Nat := 118140960795 + 3531565 * 2 ^ 59
def prefixEnd_3531565 : Nat := 4983230072969 + 3 ^ 40 * 3531565 * 2
def baseEnd_3531565 : Nat := 134325207970042997733047

theorem tailTrace_3531565 : CollatzResearch.WordTrace tailWord_3531565 prefixEnd_3531565 134325207970042997733047 := by
  unfold tailWord_3531565
  simp only [CollatzResearch.WordTrace]
  refine ⟨128806757450750623128420149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85871171633833748752280099 128806757450750623128420149)
  ·
    refine ⟨12075633511007870918289389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128806757450750623128420149 12075633511007870918289389)
    ·
      refine ⟨4528362566627951594358521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12075633511007870918289389 4528362566627951594358521)
      ·
        refine ⟨3396271924970963695768891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4528362566627951594358521 3396271924970963695768891)
        ·
          refine ⟨5094407887456445543653337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396271924970963695768891 5094407887456445543653337)
          ·
            refine ⟨3820805915592334157740003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5094407887456445543653337 3820805915592334157740003)
            ·
              refine ⟨5731208873388501236610005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820805915592334157740003 5731208873388501236610005)
              ·
                refine ⟨134325207970042997733047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5731208873388501236610005 134325207970042997733047)
                ·
                  rfl

theorem cell22_3531565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 7].length) (baseStart_3531565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531565 prefixEnd_3531565 := by exact prefixLift 3531565
  have htrace : WordTrace (prefixWord ++ tailWord_3531565) baseStart_3531565 baseEnd_3531565 := by
    simpa [prefixWord, tailWord_3531565, baseEnd_3531565] using wordTrace_append hprefix tailTrace_3531565
  have hstable : (prefixWord ++ tailWord_3531565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531565).length < 2 ^ (prefixWord ++ tailWord_3531565).sum := by decide
  have hdescent : baseEnd_3531565 < baseStart_3531565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531638 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3531638 : Nat := 118140960795 + 3531638 * 2 ^ 59
def prefixEnd_3531638 : Nat := 4983230072969 + 3 ^ 40 * 3531638 * 2
def baseEnd_3531638 : Nat := 402983953707413040840733

theorem tailTrace_3531638 : CollatzResearch.WordTrace tailWord_3531638 prefixEnd_3531638 402983953707413040840733 := by
  unfold tailWord_3531638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050588748717884787239223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85872946652990771063885045 8050588748717884787239223)
  ·
    refine ⟨12075883123076827180858835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8050588748717884787239223 12075883123076827180858835)
    ·
      refine ⟨18113824684615240771288253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12075883123076827180858835 18113824684615240771288253)
      ·
        refine ⟨6792684256730715289233095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18113824684615240771288253 6792684256730715289233095)
        ·
          refine ⟨10189026385096072933849643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792684256730715289233095 10189026385096072933849643)
          ·
            refine ⟨15283539577644109400774465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189026385096072933849643 15283539577644109400774465)
            ·
              refine ⟨11462654683233082050580849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15283539577644109400774465 11462654683233082050580849)
              ·
                refine ⟨8596991012424811537935637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11462654683233082050580849 8596991012424811537935637)
                ·
                  refine ⟨402983953707413040840733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8596991012424811537935637 402983953707413040840733)
                  ·
                    rfl

theorem cell22_3531638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3531638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531638 prefixEnd_3531638 := by exact prefixLift 3531638
  have htrace : WordTrace (prefixWord ++ tailWord_3531638) baseStart_3531638 baseEnd_3531638 := by
    simpa [prefixWord, tailWord_3531638, baseEnd_3531638] using wordTrace_append hprefix tailTrace_3531638
  have hstable : (prefixWord ++ tailWord_3531638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531638).length < 2 ^ (prefixWord ++ tailWord_3531638).sum := by decide
  have hdescent : baseEnd_3531638 < baseStart_3531638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531651 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 2, 4]
def baseStart_3531651 : Nat := 118140960795 + 3531651 * 2 ^ 59
def prefixEnd_3531651 : Nat := 4983230072969 + 3 ^ 40 * 3531651 * 2
def baseEnd_3531651 : Nat := 1208956311287911421947159

theorem tailTrace_3531651 : CollatzResearch.WordTrace tailWord_3531651 prefixEnd_3531651 1208956311287911421947159 := by
  unfold tailWord_3531651
  simp only [CollatzResearch.WordTrace]
  refine ⟨128809894128439059816050807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85873262752292706544033871 128809894128439059816050807)
  ·
    refine ⟨193214841192658589724076211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128809894128439059816050807 193214841192658589724076211)
    ·
      refine ⟨289822261788987884586114317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193214841192658589724076211 289822261788987884586114317)
      ·
        refine ⟨108683348170870456719792869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289822261788987884586114317 108683348170870456719792869)
        ·
          refine ⟨20378127782038210634961163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108683348170870456719792869 20378127782038210634961163)
          ·
            refine ⟨30567191673057315952441745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20378127782038210634961163 30567191673057315952441745)
            ·
              refine ⟨22925393754792986964331309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30567191673057315952441745 22925393754792986964331309)
              ·
                refine ⟨8597022658047370111624241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22925393754792986964331309 8597022658047370111624241)
                ·
                  refine ⟨6447766993535527583718181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8597022658047370111624241 6447766993535527583718181)
                  ·
                    refine ⟨1208956311287911421947159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447766993535527583718181 1208956311287911421947159)
                    ·
                      rfl

theorem cell22_3531651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_3531651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531651 prefixEnd_3531651 := by exact prefixLift 3531651
  have htrace : WordTrace (prefixWord ++ tailWord_3531651) baseStart_3531651 baseEnd_3531651 := by
    simpa [prefixWord, tailWord_3531651, baseEnd_3531651] using wordTrace_append hprefix tailTrace_3531651
  have hstable : (prefixWord ++ tailWord_3531651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531651).length < 2 ^ (prefixWord ++ tailWord_3531651).sum := by decide
  have hdescent : baseEnd_3531651 < baseStart_3531651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531655 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 4]
def baseStart_3531655 : Nat := 118140960795 + 3531655 * 2 ^ 59
def prefixEnd_3531655 : Nat := 4983230072969 + 3 ^ 40 * 3531655 * 2
def baseEnd_3531655 : Nat := 402985893523218914949049

theorem tailTrace_3531655 : CollatzResearch.WordTrace tailWord_3531655 prefixEnd_3531655 402985893523218914949049 := by
  unfold tailWord_3531655
  simp only [CollatzResearch.WordTrace]
  refine ⟨128810040020424568499196419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85873360013616378999464279 128810040020424568499196419)
  ·
    refine ⟨193215060030636852748794629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128810040020424568499196419 193215060030636852748794629)
    ·
      refine ⟨36227823755744409890398993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193215060030636852748794629 36227823755744409890398993)
      ·
        refine ⟨27170867816808307417799245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36227823755744409890398993 27170867816808307417799245)
        ·
          refine ⟨10189075431303115281674717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27170867816808307417799245 10189075431303115281674717)
          ·
            refine ⟨3820903286738668230628019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10189075431303115281674717 3820903286738668230628019)
            ·
              refine ⟨5731354930108002345942029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820903286738668230628019 5731354930108002345942029)
              ·
                refine ⟨2149258098790500879728261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5731354930108002345942029 2149258098790500879728261)
                ·
                  refine ⟨402985893523218914949049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149258098790500879728261 402985893523218914949049)
                  ·
                    rfl

theorem cell22_3531655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 4].length) (baseStart_3531655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531655 prefixEnd_3531655 := by exact prefixLift 3531655
  have htrace : WordTrace (prefixWord ++ tailWord_3531655) baseStart_3531655 baseEnd_3531655 := by
    simpa [prefixWord, tailWord_3531655, baseEnd_3531655] using wordTrace_append hprefix tailTrace_3531655
  have hstable : (prefixWord ++ tailWord_3531655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531655).length < 2 ^ (prefixWord ++ tailWord_3531655).sum := by decide
  have hdescent : baseEnd_3531655 < baseStart_3531655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531664 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_3531664 : Nat := 118140960795 + 3531664 * 2 ^ 59
def prefixEnd_3531664 : Nat := 4983230072969 + 3 ^ 40 * 3531664 * 2
def baseEnd_3531664 : Nat := 1208960761453583721372119

theorem tailTrace_3531664 : CollatzResearch.WordTrace tailWord_3531664 prefixEnd_3531664 1208960761453583721372119 := by
  unfold tailWord_3531664
  simp only [CollatzResearch.WordTrace]
  refine ⟨64405184138695981518137023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85873578851594642024182697 64405184138695981518137023)
  ·
    refine ⟨96607776208043972277205535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64405184138695981518137023 96607776208043972277205535)
    ·
      refine ⟨144911664312065958415808303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96607776208043972277205535 144911664312065958415808303)
      ·
        refine ⟨217367496468098937623712455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144911664312065958415808303 217367496468098937623712455)
        ·
          refine ⟨326051244702148406435568683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217367496468098937623712455 326051244702148406435568683)
          ·
            refine ⟨489076867053222609653353025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326051244702148406435568683 489076867053222609653353025)
            ·
              refine ⟨366807650289916957240014769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489076867053222609653353025 366807650289916957240014769)
              ·
                refine ⟨275105737717437717930011077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366807650289916957240014769 275105737717437717930011077)
                ·
                  refine ⟨51582325822019572111877077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275105737717437717930011077 51582325822019572111877077)
                  ·
                    refine ⟨1208960761453583721372119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51582325822019572111877077 1208960761453583721372119)
                    ·
                      rfl

theorem cell22_3531664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_3531664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531664 prefixEnd_3531664 := by exact prefixLift 3531664
  have htrace : WordTrace (prefixWord ++ tailWord_3531664) baseStart_3531664 baseEnd_3531664 := by
    simpa [prefixWord, tailWord_3531664, baseEnd_3531664] using wordTrace_append hprefix tailTrace_3531664
  have hstable : (prefixWord ++ tailWord_3531664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531664).length < 2 ^ (prefixWord ++ tailWord_3531664).sum := by decide
  have hdescent : baseEnd_3531664 < baseStart_3531664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531668 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3531668 : Nat := 118140960795 + 3531668 * 2 ^ 59
def prefixEnd_3531668 : Nat := 4983230072969 + 3 ^ 40 * 3531668 * 2
def baseEnd_3531668 : Nat := 1208962130735329044272107

theorem tailTrace_3531668 : CollatzResearch.WordTrace tailWord_3531668 prefixEnd_3531668 1208962130735329044272107 := by
  unfold tailWord_3531668
  simp only [CollatzResearch.WordTrace]
  refine ⟨64405257084688735859709829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85873676112918314479613105 64405257084688735859709829)
  ·
    refine ⟨12075985703379137973695593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64405257084688735859709829 12075985703379137973695593)
    ·
      refine ⟨9056989277534353480271695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12075985703379137973695593 9056989277534353480271695)
      ·
        refine ⟨13585483916301530220407543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056989277534353480271695 13585483916301530220407543)
        ·
          refine ⟨20378225874452295330611315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13585483916301530220407543 20378225874452295330611315)
          ·
            refine ⟨30567338811678442995916973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20378225874452295330611315 30567338811678442995916973)
            ·
              refine ⟨11462752054379416123468865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30567338811678442995916973 11462752054379416123468865)
              ·
                refine ⟨8597064040784562092601649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11462752054379416123468865 8597064040784562092601649)
                ·
                  refine ⟨6447798030588421569451237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8597064040784562092601649 6447798030588421569451237)
                  ·
                    refine ⟨1208962130735329044272107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6447798030588421569451237 1208962130735329044272107)
                    ·
                      rfl

theorem cell22_3531668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3531668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531668 prefixEnd_3531668 := by exact prefixLift 3531668
  have htrace : WordTrace (prefixWord ++ tailWord_3531668) baseStart_3531668 baseEnd_3531668 := by
    simpa [prefixWord, tailWord_3531668, baseEnd_3531668] using wordTrace_append hprefix tailTrace_3531668
  have hstable : (prefixWord ++ tailWord_3531668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531668).length < 2 ^ (prefixWord ++ tailWord_3531668).sum := by decide
  have hdescent : baseEnd_3531668 < baseStart_3531668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531732 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3531732 : Nat := 118140960795 + 3531732 * 2 ^ 59
def prefixEnd_3531732 : Nat := 4983230072969 + 3 ^ 40 * 3531732 * 2
def baseEnd_3531732 : Nat := 1208984039243254210671911

theorem tailTrace_3531732 : CollatzResearch.WordTrace tailWord_3531732 prefixEnd_3531732 1208984039243254210671911 := by
  unfold tailWord_3531732
  simp only [CollatzResearch.WordTrace]
  refine ⟨64406424220572805324874725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85875232294097073766499633 64406424220572805324874725)
  ·
    refine ⟨12076204541357400998414011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64406424220572805324874725 12076204541357400998414011)
    ·
      refine ⟨18114306812036101497621017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12076204541357400998414011 18114306812036101497621017)
      ·
        refine ⟨13585730109027076123215763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18114306812036101497621017 13585730109027076123215763)
        ·
          refine ⟨20378595163540614184823645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13585730109027076123215763 20378595163540614184823645)
          ·
            refine ⟨7641973186327730319308867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20378595163540614184823645 7641973186327730319308867)
            ·
              refine ⟨11462959779491595478963301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641973186327730319308867 11462959779491595478963301)
              ·
                refine ⟨2149304958654674152305619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11462959779491595478963301 2149304958654674152305619)
                ·
                  refine ⟨3223957437982011228458429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149304958654674152305619 3223957437982011228458429)
                  ·
                    refine ⟨1208984039243254210671911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3223957437982011228458429 1208984039243254210671911)
                    ·
                      rfl

theorem cell22_3531732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3531732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531732 prefixEnd_3531732 := by exact prefixLift 3531732
  have htrace : WordTrace (prefixWord ++ tailWord_3531732) baseStart_3531732 baseEnd_3531732 := by
    simpa [prefixWord, tailWord_3531732, baseEnd_3531732] using wordTrace_append hprefix tailTrace_3531732
  have hstable : (prefixWord ++ tailWord_3531732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531732).length < 2 ^ (prefixWord ++ tailWord_3531732).sum := by decide
  have hdescent : baseEnd_3531732 < baseStart_3531732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531743 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 2, 5]
def baseStart_3531743 : Nat := 118140960795 + 3531743 * 2 ^ 59
def prefixEnd_3531743 : Nat := 4983230072969 + 3 ^ 40 * 3531743 * 2
def baseEnd_3531743 : Nat := 1208987804768053848646877

theorem tailTrace_3531743 : CollatzResearch.WordTrace tailWord_3531743 prefixEnd_3531743 1208987804768053848646877 := by
  unfold tailWord_3531743
  simp only [CollatzResearch.WordTrace]
  refine ⟨128813249644105759528399883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85875499762737173018933255 128813249644105759528399883)
  ·
    refine ⟨193219874466158639292599825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128813249644105759528399883 193219874466158639292599825)
    ·
      refine ⟨144914905849618979469449869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193219874466158639292599825 144914905849618979469449869)
      ·
        refine ⟨54343089693607117301043701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144914905849618979469449869 54343089693607117301043701)
        ·
          refine ⟨5094664658775667246972847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54343089693607117301043701 5094664658775667246972847)
          ·
            refine ⟨7641996988163500870459271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094664658775667246972847 7641996988163500870459271)
            ·
              refine ⟨11462995482245251305688907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641996988163500870459271 11462995482245251305688907)
              ·
                refine ⟨17194493223367876958533361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462995482245251305688907 17194493223367876958533361)
                ·
                  refine ⟨12895869917525907718900021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17194493223367876958533361 12895869917525907718900021)
                  ·
                    refine ⟨1208987804768053848646877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12895869917525907718900021 1208987804768053848646877)
                    ·
                      rfl

theorem cell22_3531743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_3531743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531743 prefixEnd_3531743 := by exact prefixLift 3531743
  have htrace : WordTrace (prefixWord ++ tailWord_3531743) baseStart_3531743 baseEnd_3531743 := by
    simpa [prefixWord, tailWord_3531743, baseEnd_3531743] using wordTrace_append hprefix tailTrace_3531743
  have hstable : (prefixWord ++ tailWord_3531743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531743).length < 2 ^ (prefixWord ++ tailWord_3531743).sum := by decide
  have hdescent : baseEnd_3531743 < baseStart_3531743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531790 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3531790 : Nat := 118140960795 + 3531790 * 2 ^ 59
def prefixEnd_3531790 : Nat := 4983230072969 + 3 ^ 40 * 3531790 * 2
def baseEnd_3531790 : Nat := 403001297942853797573911

theorem tailTrace_3531790 : CollatzResearch.WordTrace tailWord_3531790 prefixEnd_3531790 403001297942853797573911 := by
  unfold tailWord_3531790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101870484366935819420103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85876642583290324370240549 16101870484366935819420103)
  ·
    refine ⟨24152805726550403729130155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16101870484366935819420103 24152805726550403729130155)
    ·
      refine ⟨36229208589825605593695233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24152805726550403729130155 36229208589825605593695233)
      ·
        refine ⟨27171906442369204195271425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36229208589825605593695233 27171906442369204195271425)
        ·
          refine ⟨20378929831776903146453569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27171906442369204195271425 20378929831776903146453569)
          ·
            refine ⟨15284197373832677359840177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20378929831776903146453569 15284197373832677359840177)
            ·
              refine ⟨11463148030374508019880133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15284197373832677359840177 11463148030374508019880133)
              ·
                refine ⟨2149340255695220253727525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11463148030374508019880133 2149340255695220253727525)
                ·
                  refine ⟨403001297942853797573911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149340255695220253727525 403001297942853797573911)
                  ·
                    rfl

theorem cell22_3531790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3531790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531790 prefixEnd_3531790 := by exact prefixLift 3531790
  have htrace : WordTrace (prefixWord ++ tailWord_3531790) baseStart_3531790 baseEnd_3531790 := by
    simpa [prefixWord, tailWord_3531790, baseEnd_3531790] using wordTrace_append hprefix tailTrace_3531790
  have hstable : (prefixWord ++ tailWord_3531790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531790).length < 2 ^ (prefixWord ++ tailWord_3531790).sum := by decide
  have hdescent : baseEnd_3531790 < baseStart_3531790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531831 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3531831 : Nat := 118140960795 + 3531831 * 2 ^ 59
def prefixEnd_3531831 : Nat := 4983230072969 + 3 ^ 40 * 3531831 * 2
def baseEnd_3531831 : Nat := 1209017928966450952446607

theorem tailTrace_3531831 : CollatzResearch.WordTrace tailWord_3531831 prefixEnd_3531831 1209017928966450952446607 := by
  unfold tailWord_3531831
  simp only [CollatzResearch.WordTrace]
  refine ⟨128816459267786950557603347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85877639511857967038402231 128816459267786950557603347)
  ·
    refine ⟨193224688901680425836405021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128816459267786950557603347 193224688901680425836405021)
    ·
      refine ⟨72459258338130159688651883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193224688901680425836405021 72459258338130159688651883)
      ·
        refine ⟨108688887507195239532977825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72459258338130159688651883 108688887507195239532977825)
        ·
          refine ⟨81516665630396429649733369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108688887507195239532977825 81516665630396429649733369)
          ·
            refine ⟨61137499222797322237300027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81516665630396429649733369 61137499222797322237300027)
            ·
              refine ⟨91706248834195983355950041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61137499222797322237300027 91706248834195983355950041)
              ·
                refine ⟨68779686625646987516962531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91706248834195983355950041 68779686625646987516962531)
                ·
                  refine ⟨103169529938470481275443797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68779686625646987516962531 103169529938470481275443797)
                  ·
                    refine ⟨1209017928966450952446607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103169529938470481275443797 1209017928966450952446607)
                    ·
                      rfl

theorem cell22_3531831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3531831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531831 prefixEnd_3531831 := by exact prefixLift 3531831
  have htrace : WordTrace (prefixWord ++ tailWord_3531831) baseStart_3531831 baseEnd_3531831 := by
    simpa [prefixWord, tailWord_3531831, baseEnd_3531831] using wordTrace_append hprefix tailTrace_3531831
  have hstable : (prefixWord ++ tailWord_3531831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531831).length < 2 ^ (prefixWord ++ tailWord_3531831).sum := by decide
  have hdescent : baseEnd_3531831 < baseStart_3531831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531850 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_3531850 : Nat := 118140960795 + 3531850 * 2 ^ 59
def prefixEnd_3531850 : Nat := 4983230072969 + 3 ^ 40 * 3531850 * 2
def baseEnd_3531850 : Nat := 1209024433054741236221549

theorem tailTrace_3531850 : CollatzResearch.WordTrace tailWord_3531850 prefixEnd_3531850 1209024433054741236221549 := by
  unfold tailWord_3531850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204288063679529200636251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85878101503145411201696669 32204288063679529200636251)
  ·
    refine ⟨48306432095519293800954377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32204288063679529200636251 48306432095519293800954377)
    ·
      refine ⟨36229824071639470350715783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48306432095519293800954377 36229824071639470350715783)
      ·
        refine ⟨54344736107459205526073675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36229824071639470350715783 54344736107459205526073675)
        ·
          refine ⟨81517104161188808289110513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54344736107459205526073675 81517104161188808289110513)
          ·
            refine ⟨61137828120891606216832885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81517104161188808289110513 61137828120891606216832885)
            ·
              refine ⟨5731671386333588082828083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61137828120891606216832885 5731671386333588082828083)
              ·
                refine ⟨8597507079500382124242125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731671386333588082828083 8597507079500382124242125)
                ·
                  refine ⟨3224065154812643296590797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8597507079500382124242125 3224065154812643296590797)
                  ·
                    refine ⟨1209024433054741236221549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224065154812643296590797 1209024433054741236221549)
                    ·
                      rfl

theorem cell22_3531850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_3531850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531850 prefixEnd_3531850 := by exact prefixLift 3531850
  have htrace : WordTrace (prefixWord ++ tailWord_3531850) baseStart_3531850 baseEnd_3531850 := by
    simpa [prefixWord, tailWord_3531850, baseEnd_3531850] using wordTrace_append hprefix tailTrace_3531850
  have hstable : (prefixWord ++ tailWord_3531850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531850).length < 2 ^ (prefixWord ++ tailWord_3531850).sum := by decide
  have hdescent : baseEnd_3531850 < baseStart_3531850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531923 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 1, 5]
def baseStart_3531923 : Nat := 118140960795 + 3531923 * 2 ^ 59
def prefixEnd_3531923 : Nat := 4983230072969 + 3 ^ 40 * 3531923 * 2
def baseEnd_3531923 : Nat := 1209049422446593379146325

theorem tailTrace_3531923 : CollatzResearch.WordTrace tailWord_3531923 prefixEnd_3531923 1209049422446593379146325 := by
  unfold tailWord_3531923
  simp only [CollatzResearch.WordTrace]
  refine ⟨128819814783453650269952423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85879876522302433513301615 128819814783453650269952423)
  ·
    refine ⟨193229722175180475404928635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128819814783453650269952423 193229722175180475404928635)
    ·
      refine ⟨289844583262770713107392953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193229722175180475404928635 289844583262770713107392953)
      ·
        refine ⟨217383437447078034830544715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289844583262770713107392953 217383437447078034830544715)
        ·
          refine ⟨326075156170617052245817073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217383437447078034830544715 326075156170617052245817073)
          ·
            refine ⟨244556367127962789184362805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326075156170617052245817073 244556367127962789184362805)
            ·
              refine ⟨22927159418246511486034013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244556367127962789184362805 22927159418246511486034013)
              ·
                refine ⟨8597684781842441807262755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22927159418246511486034013 8597684781842441807262755)
                ·
                  refine ⟨12896527172763662710894133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8597684781842441807262755 12896527172763662710894133)
                  ·
                    refine ⟨1209049422446593379146325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12896527172763662710894133 1209049422446593379146325)
                    ·
                      rfl

theorem cell22_3531923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_3531923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531923 prefixEnd_3531923 := by exact prefixLift 3531923
  have htrace : WordTrace (prefixWord ++ tailWord_3531923) baseStart_3531923 baseEnd_3531923 := by
    simpa [prefixWord, tailWord_3531923, baseEnd_3531923] using wordTrace_append hprefix tailTrace_3531923
  have hstable : (prefixWord ++ tailWord_3531923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531923).length < 2 ^ (prefixWord ++ tailWord_3531923).sum := by decide
  have hdescent : baseEnd_3531923 < baseStart_3531923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531940 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3531940 : Nat := 118140960795 + 3531940 * 2 ^ 59
def prefixEnd_3531940 : Nat := 4983230072969 + 3 ^ 40 * 3531940 * 2
def baseEnd_3531940 : Nat := 1209055241894011001471273

theorem tailTrace_3531940 : CollatzResearch.WordTrace tailWord_3531940 prefixEnd_3531940 1209055241894011001471273 := by
  unfold tailWord_3531940
  simp only [CollatzResearch.WordTrace]
  refine ⟨64410217412196031086660637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85880289882928041448880849 64410217412196031086660637)
  ·
    refine ⟨24153831529573511657497739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64410217412196031086660637 24153831529573511657497739)
    ·
      refine ⟨36230747294360267486246609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24153831529573511657497739 36230747294360267486246609)
      ·
        refine ⟨27173060470770200614684957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36230747294360267486246609 27173060470770200614684957)
        ·
          refine ⟨10189897676538825230506859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27173060470770200614684957 10189897676538825230506859)
          ·
            refine ⟨15284846514808237845760289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189897676538825230506859 15284846514808237845760289)
            ·
              refine ⟨11463634886106178384320217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15284846514808237845760289 11463634886106178384320217)
              ·
                refine ⟨8597726164579633788240163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11463634886106178384320217 8597726164579633788240163)
                ·
                  refine ⟨12896589246869450682360245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8597726164579633788240163 12896589246869450682360245)
                  ·
                    refine ⟨1209055241894011001471273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12896589246869450682360245 1209055241894011001471273)
                    ·
                      rfl

theorem cell22_3531940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3531940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3531940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3531940 prefixEnd_3531940 := by exact prefixLift 3531940
  have htrace : WordTrace (prefixWord ++ tailWord_3531940) baseStart_3531940 baseEnd_3531940 := by
    simpa [prefixWord, tailWord_3531940, baseEnd_3531940] using wordTrace_append hprefix tailTrace_3531940
  have hstable : (prefixWord ++ tailWord_3531940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531940).length < 2 ^ (prefixWord ++ tailWord_3531940).sum := by decide
  have hdescent : baseEnd_3531940 < baseStart_3531940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532090 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_3532090 : Nat := 118140960795 + 3532090 * 2 ^ 59
def prefixEnd_3532090 : Nat := 4983230072969 + 3 ^ 40 * 3532090 * 2
def baseEnd_3532090 : Nat := 1209106589959460610220813

theorem tailTrace_3532090 : CollatzResearch.WordTrace tailWord_3532090 prefixEnd_3532090 1209106589959460610220813 := by
  unfold tailWord_3532090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32206476443462159447820431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85883937182565758527521149 32206476443462159447820431)
  ·
    refine ⟨48309714665193239171730647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32206476443462159447820431 48309714665193239171730647)
    ·
      refine ⟨72464571997789858757595971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48309714665193239171730647 72464571997789858757595971)
      ·
        refine ⟨108696857996684788136393957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72464571997789858757595971 108696857996684788136393957)
        ·
          refine ⟨20380660874378397775573867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108696857996684788136393957 20380660874378397775573867)
          ·
            refine ⟨30570991311567596663360801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20380660874378397775573867 30570991311567596663360801)
            ·
              refine ⟨22928243483675697497520601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30570991311567596663360801 22928243483675697497520601)
              ·
                refine ⟨17196182612756773123140451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22928243483675697497520601 17196182612756773123140451)
                ·
                  refine ⟨25794273919135159684710677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17196182612756773123140451 25794273919135159684710677)
                  ·
                    refine ⟨1209106589959460610220813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25794273919135159684710677 1209106589959460610220813)
                    ·
                      rfl

theorem cell22_3532090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_3532090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532090 prefixEnd_3532090 := by exact prefixLift 3532090
  have htrace : WordTrace (prefixWord ++ tailWord_3532090) baseStart_3532090 baseEnd_3532090 := by
    simpa [prefixWord, tailWord_3532090, baseEnd_3532090] using wordTrace_append hprefix tailTrace_3532090
  have hstable : (prefixWord ++ tailWord_3532090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532090).length < 2 ^ (prefixWord ++ tailWord_3532090).sum := by decide
  have hdescent : baseEnd_3532090 < baseStart_3532090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532092 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3532092 : Nat := 118140960795 + 3532092 * 2 ^ 59
def prefixEnd_3532092 : Nat := 4983230072969 + 3 ^ 40 * 3532092 * 2
def baseEnd_3532092 : Nat := 1209107274600333271670807

theorem tailTrace_3532092 : CollatzResearch.WordTrace tailWord_3532092 prefixEnd_3532092 1209107274600333271670807 := by
  unfold tailWord_3532092
  simp only [CollatzResearch.WordTrace]
  refine ⟨64412989359920696066427265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85883985813227594755236353 64412989359920696066427265)
  ·
    refine ⟨48309742019940522049820449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64412989359920696066427265 48309742019940522049820449)
    ·
      refine ⟨36232306514955391537365337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48309742019940522049820449 36232306514955391537365337)
      ·
        refine ⟨27174229886216543653024003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36232306514955391537365337 27174229886216543653024003)
        ·
          refine ⟨40761344829324815479536005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27174229886216543653024003 40761344829324815479536005)
          ·
            refine ⟨7642752155498402902413001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40761344829324815479536005 7642752155498402902413001)
            ·
              refine ⟨5732064116623802176809751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7642752155498402902413001 5732064116623802176809751)
              ·
                refine ⟨8598096174935703265214627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732064116623802176809751 8598096174935703265214627)
                ·
                  refine ⟨12897144262403554897821941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8598096174935703265214627 12897144262403554897821941)
                  ·
                    refine ⟨1209107274600333271670807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12897144262403554897821941 1209107274600333271670807)
                    ·
                      rfl

theorem cell22_3532092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3532092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532092 prefixEnd_3532092 := by exact prefixLift 3532092
  have htrace : WordTrace (prefixWord ++ tailWord_3532092) baseStart_3532092 baseEnd_3532092 := by
    simpa [prefixWord, tailWord_3532092, baseEnd_3532092] using wordTrace_append hprefix tailTrace_3532092
  have hstable : (prefixWord ++ tailWord_3532092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532092).length < 2 ^ (prefixWord ++ tailWord_3532092).sum := by decide
  have hdescent : baseEnd_3532092 < baseStart_3532092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532165 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3532165 : Nat := 118140960795 + 3532165 * 2 ^ 59
def prefixEnd_3532165 : Nat := 4983230072969 + 3 ^ 40 * 3532165 * 2
def baseEnd_3532165 : Nat := 1209132263992185414595583

theorem tailTrace_3532165 : CollatzResearch.WordTrace tailWord_3532165 prefixEnd_3532165 1209132263992185414595583 := by
  unfold tailWord_3532165
  simp only [CollatzResearch.WordTrace]
  refine ⟨128828641248576925600261949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85885760832384617066841299 128828641248576925600261949)
  ·
    refine ⟨48310740468216347100098231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128828641248576925600261949 48310740468216347100098231)
    ·
      refine ⟨72466110702324520650147347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48310740468216347100098231 72466110702324520650147347)
      ·
        refine ⟨108699166053486780975221021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72466110702324520650147347 108699166053486780975221021)
        ·
          refine ⟨40762187270057542865707883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108699166053486780975221021 40762187270057542865707883)
          ·
            refine ⟨61143280905086314298561825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40762187270057542865707883 61143280905086314298561825)
            ·
              refine ⟨45857460678814735723921369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61143280905086314298561825 45857460678814735723921369)
              ·
                refine ⟨34393095509111051792941027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45857460678814735723921369 34393095509111051792941027)
                ·
                  refine ⟨51589643263666577689411541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34393095509111051792941027 51589643263666577689411541)
                  ·
                    refine ⟨1209132263992185414595583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51589643263666577689411541 1209132263992185414595583)
                    ·
                      rfl

theorem cell22_3532165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3532165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532165 prefixEnd_3532165 := by exact prefixLift 3532165
  have htrace : WordTrace (prefixWord ++ tailWord_3532165) baseStart_3532165 baseEnd_3532165 := by
    simpa [prefixWord, tailWord_3532165, baseEnd_3532165] using wordTrace_append hprefix tailTrace_3532165
  have hstable : (prefixWord ++ tailWord_3532165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532165).length < 2 ^ (prefixWord ++ tailWord_3532165).sum := by decide
  have hdescent : baseEnd_3532165 < baseStart_3532165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532188 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_3532188 : Nat := 118140960795 + 3532188 * 2 ^ 59
def prefixEnd_3532188 : Nat := 4983230072969 + 3 ^ 40 * 3532188 * 2
def baseEnd_3532188 : Nat := 1209140137362221021270513

theorem tailTrace_3532188 : CollatzResearch.WordTrace tailWord_3532188 prefixEnd_3532188 1209140137362221021270513 := by
  unfold tailWord_3532188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64414740063746800264174609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85886320084995733685566145 64414740063746800264174609)
  ·
    refine ⟨48311055047810100198130957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64414740063746800264174609 48311055047810100198130957)
    ·
      refine ⟨18116645642928787574299109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48311055047810100198130957 18116645642928787574299109)
      ·
        refine ⟨3396871058049147670181083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18116645642928787574299109 3396871058049147670181083)
        ·
          refine ⟨5095306587073721505271625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396871058049147670181083 5095306587073721505271625)
          ·
            refine ⟨3821479940305291128953719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5095306587073721505271625 3821479940305291128953719)
            ·
              refine ⟨5732219910457936693430579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821479940305291128953719 5732219910457936693430579)
              ·
                refine ⟨8598329865686905040145869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732219910457936693430579 8598329865686905040145869)
                ·
                  refine ⟨3224373699632589390054701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8598329865686905040145869 3224373699632589390054701)
                  ·
                    refine ⟨1209140137362221021270513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224373699632589390054701 1209140137362221021270513)
                    ·
                      rfl

theorem cell22_3532188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_3532188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532188 prefixEnd_3532188 := by exact prefixLift 3532188
  have htrace : WordTrace (prefixWord ++ tailWord_3532188) baseStart_3532188 baseEnd_3532188 := by
    simpa [prefixWord, tailWord_3532188, baseEnd_3532188] using wordTrace_append hprefix tailTrace_3532188
  have hstable : (prefixWord ++ tailWord_3532188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532188).length < 2 ^ (prefixWord ++ tailWord_3532188).sum := by decide
  have hdescent : baseEnd_3532188 < baseStart_3532188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532227 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 6, 3]
def baseStart_3532227 : Nat := 118140960795 + 3532227 * 2 ^ 59
def prefixEnd_3532227 : Nat := 4983230072969 + 3 ^ 40 * 3532227 * 2
def baseEnd_3532227 : Nat := 1209153487859237919545393

theorem tailTrace_3532227 : CollatzResearch.WordTrace tailWord_3532227 prefixEnd_3532227 1209153487859237919545393 := by
  unfold tailWord_3532227
  simp only [CollatzResearch.WordTrace]
  refine ⟨128830902574352310189018935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85887268382901540126012623 128830902574352310189018935)
  ·
    refine ⟨193246353861528465283528403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128830902574352310189018935 193246353861528465283528403)
    ·
      refine ⟨289869530792292697925292605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193246353861528465283528403 289869530792292697925292605)
      ·
        refine ⟨108701074047109761721984727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289869530792292697925292605 108701074047109761721984727)
        ·
          refine ⟨163051611070664642582977091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108701074047109761721984727 163051611070664642582977091)
          ·
            refine ⟨244577416605996963874465637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163051611070664642582977091 244577416605996963874465637)
            ·
              refine ⟨45858265613624430726462307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244577416605996963874465637 45858265613624430726462307)
              ·
                refine ⟨68787398420436646089693461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45858265613624430726462307 68787398420436646089693461)
                ·
                  refine ⟨3224409300957967785454381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68787398420436646089693461 3224409300957967785454381)
                  ·
                    refine ⟨1209153487859237919545393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224409300957967785454381 1209153487859237919545393)
                    ·
                      rfl

theorem cell22_3532227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 3].length) (baseStart_3532227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532227 prefixEnd_3532227 := by exact prefixLift 3532227
  have htrace : WordTrace (prefixWord ++ tailWord_3532227) baseStart_3532227 baseEnd_3532227 := by
    simpa [prefixWord, tailWord_3532227, baseEnd_3532227] using wordTrace_append hprefix tailTrace_3532227
  have hstable : (prefixWord ++ tailWord_3532227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532227).length < 2 ^ (prefixWord ++ tailWord_3532227).sum := by decide
  have hdescent : baseEnd_3532227 < baseStart_3532227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532257 : List Nat := [1, 2, 3, 1, 2, 3, 3, 7]
def baseStart_3532257 : Nat := 118140960795 + 3532257 * 2 ^ 59
def prefixEnd_3532257 : Nat := 4983230072969 + 3 ^ 40 * 3532257 * 2
def baseEnd_3532257 : Nat := 134351528608036426810589

theorem tailTrace_3532257 : CollatzResearch.WordTrace tailWord_3532257 prefixEnd_3532257 134351528608036426810589 := by
  unfold tailWord_3532257
  simp only [CollatzResearch.WordTrace]
  refine ⟨128831996764243625312611025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85887997842829083541740683 128831996764243625312611025)
  ·
    refine ⟨96623997573182718984458269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128831996764243625312611025 96623997573182718984458269)
    ·
      refine ⟨36233999089943519619171851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96623997573182718984458269 36233999089943519619171851)
      ·
        refine ⟨54350998634915279428757777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36233999089943519619171851 54350998634915279428757777)
        ·
          refine ⟨40763248976186459571568333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54350998634915279428757777 40763248976186459571568333)
          ·
            refine ⟨15286218366069922339338125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40763248976186459571568333 15286218366069922339338125)
            ·
              refine ⟨5732331887276220877251797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15286218366069922339338125 5732331887276220877251797)
              ·
                refine ⟨134351528608036426810589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5732331887276220877251797 134351528608036426810589)
                ·
                  rfl

theorem cell22_3532257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 7].length) (baseStart_3532257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532257 prefixEnd_3532257 := by exact prefixLift 3532257
  have htrace : WordTrace (prefixWord ++ tailWord_3532257) baseStart_3532257 baseEnd_3532257 := by
    simpa [prefixWord, tailWord_3532257, baseEnd_3532257] using wordTrace_append hprefix tailTrace_3532257
  have hstable : (prefixWord ++ tailWord_3532257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532257).length < 2 ^ (prefixWord ++ tailWord_3532257).sum := by decide
  have hdescent : baseEnd_3532257 < baseStart_3532257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532261 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_3532261 : Nat := 118140960795 + 3532261 * 2 ^ 59
def prefixEnd_3532261 : Nat := 4983230072969 + 3 ^ 40 * 3532261 * 2
def baseEnd_3532261 : Nat := 1209165126754073164195289

theorem tailTrace_3532261 : CollatzResearch.WordTrace tailWord_3532261 prefixEnd_3532261 1209165126754073164195289 := by
  unfold tailWord_3532261
  simp only [CollatzResearch.WordTrace]
  refine ⟨128832142656229133995756637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85888095104152755997171091 128832142656229133995756637)
  ·
    refine ⟨48312053496085925248408739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128832142656229133995756637 48312053496085925248408739)
    ·
      refine ⟨72468080244128887872613109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48312053496085925248408739 72468080244128887872613109)
      ·
        refine ⟨6793882522887083238057479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72468080244128887872613109 6793882522887083238057479)
        ·
          refine ⟨10190823784330624857086219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793882522887083238057479 10190823784330624857086219)
          ·
            refine ⟨15286235676495937285629329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10190823784330624857086219 15286235676495937285629329)
            ·
              refine ⟨11464676757371952964221997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15286235676495937285629329 11464676757371952964221997)
              ·
                refine ⟨4299253784014482361583249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11464676757371952964221997 4299253784014482361583249)
                ·
                  refine ⟨3224440338010861771187437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299253784014482361583249 3224440338010861771187437)
                  ·
                    refine ⟨1209165126754073164195289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224440338010861771187437 1209165126754073164195289)
                    ·
                      rfl

theorem cell22_3532261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_3532261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532261 prefixEnd_3532261 := by exact prefixLift 3532261
  have htrace : WordTrace (prefixWord ++ tailWord_3532261) baseStart_3532261 baseEnd_3532261 := by
    simpa [prefixWord, tailWord_3532261, baseEnd_3532261] using wordTrace_append hprefix tailTrace_3532261
  have hstable : (prefixWord ++ tailWord_3532261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532261).length < 2 ^ (prefixWord ++ tailWord_3532261).sum := by decide
  have hdescent : baseEnd_3532261 < baseStart_3532261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532364 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_3532364 : Nat := 118140960795 + 3532364 * 2 ^ 59
def prefixEnd_3532364 : Nat := 4983230072969 + 3 ^ 40 * 3532364 * 2
def baseEnd_3532364 : Nat := 403066795253005076289991

theorem tailTrace_3532364 : CollatzResearch.WordTrace tailWord_3532364 prefixEnd_3532364 403066795253005076289991 := by
  unfold tailWord_3532364
  simp only [CollatzResearch.WordTrace]
  refine ⟨64417949687427991293378073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85890599583237321724504097 64417949687427991293378073)
  ·
    refine ⟨48313462265570993470033555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64417949687427991293378073 48313462265570993470033555)
    ·
      refine ⟨72470193398356490205050333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48313462265570993470033555 72470193398356490205050333)
      ·
        refine ⟨27176322524383683826893875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72470193398356490205050333 27176322524383683826893875)
        ·
          refine ⟨40764483786575525740340813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27176322524383683826893875 40764483786575525740340813)
          ·
            refine ⟨15286681419965822152627805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40764483786575525740340813 15286681419965822152627805)
            ·
              refine ⟨5732505532487183307235427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15286681419965822152627805 5732505532487183307235427)
              ·
                refine ⟨8598758298730774960853141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732505532487183307235427 8598758298730774960853141)
                ·
                  refine ⟨403066795253005076289991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8598758298730774960853141 403066795253005076289991)
                  ·
                    rfl

theorem cell22_3532364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_3532364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532364 prefixEnd_3532364 := by exact prefixLift 3532364
  have htrace : WordTrace (prefixWord ++ tailWord_3532364) baseStart_3532364 baseEnd_3532364 := by
    simpa [prefixWord, tailWord_3532364, baseEnd_3532364] using wordTrace_append hprefix tailTrace_3532364
  have hstable : (prefixWord ++ tailWord_3532364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532364).length < 2 ^ (prefixWord ++ tailWord_3532364).sum := by decide
  have hdescent : baseEnd_3532364 < baseStart_3532364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532377 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_3532377 : Nat := 118140960795 + 3532377 * 2 ^ 59
def prefixEnd_3532377 : Nat := 4983230072969 + 3 ^ 40 * 3532377 * 2
def baseEnd_3532377 : Nat := 1209204835924687528294933

theorem tailTrace_3532377 : CollatzResearch.WordTrace tailWord_3532377 prefixEnd_3532377 1209204835924687528294933 := by
  unfold tailWord_3532377
  simp only [CollatzResearch.WordTrace]
  refine ⟨128836373523808885806979385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85890915682539257204652923 128836373523808885806979385)
  ·
    refine ⟨96627280142856664355234539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128836373523808885806979385 96627280142856664355234539)
    ·
      refine ⟨144940920214284996532851809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96627280142856664355234539 144940920214284996532851809)
      ·
        refine ⟨108705690160713747399638857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144940920214284996532851809 108705690160713747399638857)
        ·
          refine ⟨81529267620535310549729143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108705690160713747399638857 81529267620535310549729143)
          ·
            refine ⟨122293901430802965824593715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81529267620535310549729143 122293901430802965824593715)
            ·
              refine ⟨183440852146204448736890573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122293901430802965824593715 183440852146204448736890573)
              ·
                refine ⟨68790319554826668276333965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183440852146204448736890573 68790319554826668276333965)
                ·
                  refine ⟨25796369833060000603625237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68790319554826668276333965 25796369833060000603625237)
                  ·
                    refine ⟨1209204835924687528294933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25796369833060000603625237 1209204835924687528294933)
                    ·
                      rfl

theorem cell22_3532377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_3532377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532377 prefixEnd_3532377 := by exact prefixLift 3532377
  have htrace : WordTrace (prefixWord ++ tailWord_3532377) baseStart_3532377 baseEnd_3532377 := by
    simpa [prefixWord, tailWord_3532377, baseEnd_3532377] using wordTrace_append hprefix tailTrace_3532377
  have hstable : (prefixWord ++ tailWord_3532377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532377).length < 2 ^ (prefixWord ++ tailWord_3532377).sum := by decide
  have hdescent : baseEnd_3532377 < baseStart_3532377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532413 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_3532413 : Nat := 118140960795 + 3532413 * 2 ^ 59
def prefixEnd_3532413 : Nat := 4983230072969 + 3 ^ 40 * 3532413 * 2
def baseEnd_3532413 : Nat := 1209217159460395434394823

theorem tailTrace_3532413 : CollatzResearch.WordTrace tailWord_3532413 prefixEnd_3532413 1209217159460395434394823 := by
  unfold tailWord_3532413
  simp only [CollatzResearch.WordTrace]
  refine ⟨128837686551678463955289893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85891791034452309303526595 128837686551678463955289893)
  ·
    refine ⟨24157066228439711991616855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128837686551678463955289893 24157066228439711991616855)
    ·
      refine ⟨36235599342659567987425283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24157066228439711991616855 36235599342659567987425283)
      ·
        refine ⟨54353399013989351981137925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36235599342659567987425283 54353399013989351981137925)
        ·
          refine ⟨10191262315123003496463361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54353399013989351981137925 10191262315123003496463361)
          ·
            refine ⟨7643446736342252622347521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10191262315123003496463361 7643446736342252622347521)
            ·
              refine ⟨5732585052256689466760641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7643446736342252622347521 5732585052256689466760641)
              ·
                refine ⟨4299438789192517100070481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5732585052256689466760641 4299438789192517100070481)
                ·
                  refine ⟨3224579091894387825052861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299438789192517100070481 3224579091894387825052861)
                  ·
                    refine ⟨1209217159460395434394823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224579091894387825052861 1209217159460395434394823)
                    ·
                      rfl

theorem cell22_3532413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_3532413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532413 prefixEnd_3532413 := by exact prefixLift 3532413
  have htrace : WordTrace (prefixWord ++ tailWord_3532413) baseStart_3532413 baseEnd_3532413 := by
    simpa [prefixWord, tailWord_3532413, baseEnd_3532413] using wordTrace_append hprefix tailTrace_3532413
  have hstable : (prefixWord ++ tailWord_3532413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532413).length < 2 ^ (prefixWord ++ tailWord_3532413).sum := by decide
  have hdescent : baseEnd_3532413 < baseStart_3532413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532426 : List Nat := [3, 1, 2, 3, 2, 3, 1, 7]
def baseStart_3532426 : Nat := 118140960795 + 3532426 * 2 ^ 59
def prefixEnd_3532426 : Nat := 4983230072969 + 3 ^ 40 * 3532426 * 2
def baseEnd_3532426 : Nat := 134357956625118637091087

theorem tailTrace_3532426 : CollatzResearch.WordTrace tailWord_3532426 prefixEnd_3532426 134357956625118637091087 := by
  unfold tailWord_3532426
  simp only [CollatzResearch.WordTrace]
  refine ⟨32209540175157841793878283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85892107133754244783675421 32209540175157841793878283)
  ·
    refine ⟨48314310262736762690817425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32209540175157841793878283 48314310262736762690817425)
    ·
      refine ⟨36235732697052572018113069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48314310262736762690817425 36235732697052572018113069)
      ·
        refine ⟨13588399761394714506792401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36235732697052572018113069 13588399761394714506792401)
        ·
          refine ⟨10191299821046035880094301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13588399761394714506792401 10191299821046035880094301)
          ·
            refine ⟨3821737432892263455035363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10191299821046035880094301 3821737432892263455035363)
            ·
              refine ⟨5732606149338395182553045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821737432892263455035363 5732606149338395182553045)
              ·
                refine ⟨134357956625118637091087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5732606149338395182553045 134357956625118637091087)
                ·
                  rfl

theorem cell22_3532426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_3532426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532426 prefixEnd_3532426 := by exact prefixLift 3532426
  have htrace : WordTrace (prefixWord ++ tailWord_3532426) baseStart_3532426 baseEnd_3532426 := by
    simpa [prefixWord, tailWord_3532426, baseEnd_3532426] using wordTrace_append hprefix tailTrace_3532426
  have hstable : (prefixWord ++ tailWord_3532426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532426).length < 2 ^ (prefixWord ++ tailWord_3532426).sum := by decide
  have hdescent : baseEnd_3532426 < baseStart_3532426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532471 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 5]
def baseStart_3532471 : Nat := 118140960795 + 3532471 * 2 ^ 59
def prefixEnd_3532471 : Nat := 4983230072969 + 3 ^ 40 * 3532471 * 2
def baseEnd_3532471 : Nat := 403079004681900872148215

theorem tailTrace_3532471 : CollatzResearch.WordTrace tailWord_3532471 prefixEnd_3532471 403079004681900872148215 := by
  unfold tailWord_3532471
  simp only [CollatzResearch.WordTrace]
  refine ⟨128839801985468339860901267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85893201323645559907267511 128839801985468339860901267)
  ·
    refine ⟨193259702978202509791351901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128839801985468339860901267 193259702978202509791351901)
    ·
      refine ⟨72472388616825941171756963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193259702978202509791351901 72472388616825941171756963)
      ·
        refine ⟨108708582925238911757635445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72472388616825941171756963 108708582925238911757635445)
        ·
          refine ⟨10191429649241147977278323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108708582925238911757635445 10191429649241147977278323)
          ·
            refine ⟨15287144473861721965917485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191429649241147977278323 15287144473861721965917485)
            ·
              refine ⟨5732679177698145737219057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15287144473861721965917485 5732679177698145737219057)
              ·
                refine ⟨4299509383273609302914293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5732679177698145737219057 4299509383273609302914293)
                ·
                  refine ⟨403079004681900872148215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4299509383273609302914293 403079004681900872148215)
                  ·
                    rfl

theorem cell22_3532471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 5].length) (baseStart_3532471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532471 prefixEnd_3532471 := by exact prefixLift 3532471
  have htrace : WordTrace (prefixWord ++ tailWord_3532471) baseStart_3532471 baseEnd_3532471 := by
    simpa [prefixWord, tailWord_3532471, baseEnd_3532471] using wordTrace_append hprefix tailTrace_3532471
  have hstable : (prefixWord ++ tailWord_3532471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532471).length < 2 ^ (prefixWord ++ tailWord_3532471).sum := by decide
  have hdescent : baseEnd_3532471 < baseStart_3532471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532509 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3532509 : Nat := 118140960795 + 3532509 * 2 ^ 59
def prefixEnd_3532509 : Nat := 4983230072969 + 3 ^ 40 * 3532509 * 2
def baseEnd_3532509 : Nat := 1209250022222283183994529

theorem tailTrace_3532509 : CollatzResearch.WordTrace tailWord_3532509 prefixEnd_3532509 1209250022222283183994529 := by
  unfold tailWord_3532509
  simp only [CollatzResearch.WordTrace]
  refine ⟨128841187959330672350784581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85894125306220448233856387 128841187959330672350784581)
  ·
    refine ⟨24157722742374501065772109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128841187959330672350784581 24157722742374501065772109)
    ·
      refine ⟨9059146028390437899664541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24157722742374501065772109 9059146028390437899664541)
      ·
        refine ⟨3397179760646414212374203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9059146028390437899664541 3397179760646414212374203)
        ·
          refine ⟨5095769640969621318561305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397179760646414212374203 5095769640969621318561305)
          ·
            refine ⟨3821827230727215988920979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5095769640969621318561305 3821827230727215988920979)
            ·
              refine ⟨5732740846090823983381469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821827230727215988920979 5732740846090823983381469)
              ·
                refine ⟨2149777817284058993768051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5732740846090823983381469 2149777817284058993768051)
                ·
                  refine ⟨3224666725926088490652077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149777817284058993768051 3224666725926088490652077)
                  ·
                    refine ⟨1209250022222283183994529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224666725926088490652077 1209250022222283183994529)
                    ·
                      rfl

theorem cell22_3532509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3532509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532509 prefixEnd_3532509 := by exact prefixLift 3532509
  have htrace : WordTrace (prefixWord ++ tailWord_3532509) baseStart_3532509 baseEnd_3532509 := by
    simpa [prefixWord, tailWord_3532509, baseEnd_3532509] using wordTrace_append hprefix tailTrace_3532509
  have hstable : (prefixWord ++ tailWord_3532509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532509).length < 2 ^ (prefixWord ++ tailWord_3532509).sum := by decide
  have hdescent : baseEnd_3532509 < baseStart_3532509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532531 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 4, 3]
def baseStart_3532531 : Nat := 118140960795 + 3532531 * 2 ^ 59
def prefixEnd_3532531 : Nat := 4983230072969 + 3 ^ 40 * 3532531 * 2
def baseEnd_3532531 : Nat := 1209257553271882459944461

theorem tailTrace_3532531 : CollatzResearch.WordTrace tailWord_3532531 prefixEnd_3532531 1209257553271882459944461 := by
  unfold tailWord_3532531
  simp only [CollatzResearch.WordTrace]
  refine ⟨128841990365250970108085447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85894660243500646738723631 128841990365250970108085447)
  ·
    refine ⟨193262985547876455162128171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128841990365250970108085447 193262985547876455162128171)
    ·
      refine ⟨289894478321814682743192257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193262985547876455162128171 289894478321814682743192257)
      ·
        refine ⟨217420858741361012057394193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289894478321814682743192257 217420858741361012057394193)
        ·
          refine ⟨163065644056020759043045645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217420858741361012057394193 163065644056020759043045645)
          ·
            refine ⟨61149616521007784641142117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163065644056020759043045645 61149616521007784641142117)
            ·
              refine ⟨11465553097688959620214147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61149616521007784641142117 11465553097688959620214147)
              ·
                refine ⟨17198329646533439430321221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11465553097688959620214147 17198329646533439430321221)
                ·
                  refine ⟨3224686808725019893185229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17198329646533439430321221 3224686808725019893185229)
                  ·
                    refine ⟨1209257553271882459944461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224686808725019893185229 1209257553271882459944461)
                    ·
                      rfl

theorem cell22_3532531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 3].length) (baseStart_3532531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532531 prefixEnd_3532531 := by exact prefixLift 3532531
  have htrace : WordTrace (prefixWord ++ tailWord_3532531) baseStart_3532531 baseEnd_3532531 := by
    simpa [prefixWord, tailWord_3532531, baseEnd_3532531] using wordTrace_append hprefix tailTrace_3532531
  have hstable : (prefixWord ++ tailWord_3532531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532531).length < 2 ^ (prefixWord ++ tailWord_3532531).sum := by decide
  have hdescent : baseEnd_3532531 < baseStart_3532531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532681 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_3532681 : Nat := 118140960795 + 3532681 * 2 ^ 59
def prefixEnd_3532681 : Nat := 4983230072969 + 3 ^ 40 * 3532681 * 2
def baseEnd_3532681 : Nat := 1209308901337332068694001

theorem tailTrace_3532681 : CollatzResearch.WordTrace tailWord_3532681 prefixEnd_3532681 1209308901337332068694001 := by
  unfold tailWord_3532681
  simp only [CollatzResearch.WordTrace]
  refine ⟨128847461314707545726045897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85898307543138363817363931 128847461314707545726045897)
  ·
    refine ⟨96635595986030659294534423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128847461314707545726045897 96635595986030659294534423)
    ·
      refine ⟨144953393979045988941801635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96635595986030659294534423 144953393979045988941801635)
      ·
        refine ⟨217430090968568983412702453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144953393979045988941801635 217430090968568983412702453)
        ·
          refine ⟨20384071028303342194940855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217430090968568983412702453 20384071028303342194940855)
          ·
            refine ⟨30576106542455013292411283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20384071028303342194940855 30576106542455013292411283)
            ·
              refine ⟨45864159813682519938616925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30576106542455013292411283 45864159813682519938616925)
              ·
                refine ⟨17199059930130944976981347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45864159813682519938616925 17199059930130944976981347)
                ·
                  refine ⟨25798589895196417465472021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17199059930130944976981347 25798589895196417465472021)
                  ·
                    refine ⟨1209308901337332068694001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25798589895196417465472021 1209308901337332068694001)
                    ·
                      rfl

theorem cell22_3532681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_3532681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532681 prefixEnd_3532681 := by exact prefixLift 3532681
  have htrace : WordTrace (prefixWord ++ tailWord_3532681) baseStart_3532681 baseEnd_3532681 := by
    simpa [prefixWord, tailWord_3532681, baseEnd_3532681] using wordTrace_append hprefix tailTrace_3532681
  have hstable : (prefixWord ++ tailWord_3532681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532681).length < 2 ^ (prefixWord ++ tailWord_3532681).sum := by decide
  have hdescent : baseEnd_3532681 < baseStart_3532681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532698 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_3532698 : Nat := 118140960795 + 3532698 * 2 ^ 59
def prefixEnd_3532698 : Nat := 4983230072969 + 3 ^ 40 * 3532698 * 2
def baseEnd_3532698 : Nat := 1209314720784749691018949

theorem tailTrace_3532698 : CollatzResearch.WordTrace tailWord_3532698 prefixEnd_3532698 1209314720784749691018949 := by
  unfold tailWord_3532698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32212020338911489407353687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85898720903763971752943165 32212020338911489407353687)
  ·
    refine ⟨48318030508367234111030531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32212020338911489407353687 48318030508367234111030531)
    ·
      refine ⟨72477045762550851166545797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48318030508367234111030531 72477045762550851166545797)
      ·
        refine ⟨13589446080478284593727337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72477045762550851166545797 13589446080478284593727337)
        ·
          refine ⟨10192084560358713445295503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13589446080478284593727337 10192084560358713445295503)
          ·
            refine ⟨15288126840538070167943255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192084560358713445295503 15288126840538070167943255)
            ·
              refine ⟨22932190260807105251914883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15288126840538070167943255 22932190260807105251914883)
              ·
                refine ⟨34398285391210657877872325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22932190260807105251914883 34398285391210657877872325)
                ·
                  refine ⟨6449678510851998352101061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34398285391210657877872325 6449678510851998352101061)
                  ·
                    refine ⟨1209314720784749691018949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6449678510851998352101061 1209314720784749691018949)
                    ·
                      rfl

theorem cell22_3532698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_3532698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532698 prefixEnd_3532698 := by exact prefixLift 3532698
  have htrace : WordTrace (prefixWord ++ tailWord_3532698) baseStart_3532698 baseEnd_3532698 := by
    simpa [prefixWord, tailWord_3532698, baseEnd_3532698] using wordTrace_append hprefix tailTrace_3532698
  have hstable : (prefixWord ++ tailWord_3532698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532698).length < 2 ^ (prefixWord ++ tailWord_3532698).sum := by decide
  have hdescent : baseEnd_3532698 < baseStart_3532698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532700 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3532700 : Nat := 118140960795 + 3532700 * 2 ^ 59
def prefixEnd_3532700 : Nat := 4983230072969 + 3 ^ 40 * 3532700 * 2
def baseEnd_3532700 : Nat := 1209315405425622352468943

theorem tailTrace_3532700 : CollatzResearch.WordTrace tailWord_3532700 prefixEnd_3532700 1209315405425622352468943 := by
  unfold tailWord_3532700
  simp only [CollatzResearch.WordTrace]
  refine ⟨64424077150819355985493777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85898769534425807980658369 64424077150819355985493777)
  ·
    refine ⟨48318057863114516989120333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64424077150819355985493777 48318057863114516989120333)
    ·
      refine ⟨18119271698667943870920125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48318057863114516989120333 18119271698667943870920125)
      ·
        refine ⟨6794726887000478951595047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18119271698667943870920125 6794726887000478951595047)
        ·
          refine ⟨10192090330500718427392571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794726887000478951595047 10192090330500718427392571)
          ·
            refine ⟨15288135495751077641088857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192090330500718427392571 15288135495751077641088857)
            ·
              refine ⟨11466101621813308230816643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15288135495751077641088857 11466101621813308230816643)
              ·
                refine ⟨17199152432719962346224965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11466101621813308230816643 17199152432719962346224965)
                ·
                  refine ⟨3224841081134992939917181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17199152432719962346224965 3224841081134992939917181)
                  ·
                    refine ⟨1209315405425622352468943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224841081134992939917181 1209315405425622352468943)
                    ·
                      rfl

theorem cell22_3532700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3532700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532700 prefixEnd_3532700 := by exact prefixLift 3532700
  have htrace : WordTrace (prefixWord ++ tailWord_3532700) baseStart_3532700 baseEnd_3532700 := by
    simpa [prefixWord, tailWord_3532700, baseEnd_3532700] using wordTrace_append hprefix tailTrace_3532700
  have hstable : (prefixWord ++ tailWord_3532700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532700).length < 2 ^ (prefixWord ++ tailWord_3532700).sum := by decide
  have hdescent : baseEnd_3532700 < baseStart_3532700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532728 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_3532728 : Nat := 118140960795 + 3532728 * 2 ^ 59
def prefixEnd_3532728 : Nat := 4983230072969 + 3 ^ 40 * 3532728 * 2
def baseEnd_3532728 : Nat := 1209324990397839612768857

theorem tailTrace_3532728 : CollatzResearch.WordTrace tailWord_3532728 prefixEnd_3532728 1209324990397839612768857 := by
  unfold tailWord_3532728
  simp only [CollatzResearch.WordTrace]
  refine ⟨64424587772768636376503419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85899450363691515168671225 64424587772768636376503419)
  ·
    refine ⟨96636881659152954564755129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64424587772768636376503419 96636881659152954564755129)
    ·
      refine ⟨72477661244364715923566347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96636881659152954564755129 72477661244364715923566347)
      ·
        refine ⟨108716491866547073885349521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72477661244364715923566347 108716491866547073885349521)
        ·
          refine ⟨81537368899910305414012141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108716491866547073885349521 81537368899910305414012141)
          ·
            refine ⟨30576513337466364530254553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81537368899910305414012141 30576513337466364530254553)
            ·
              refine ⟨22932385003099773397690915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30576513337466364530254553 22932385003099773397690915)
              ·
                refine ⟨34398577504649660096536373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22932385003099773397690915 34398577504649660096536373)
                ·
                  refine ⟨3224866641060905634050285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34398577504649660096536373 3224866641060905634050285)
                  ·
                    refine ⟨1209324990397839612768857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3224866641060905634050285 1209324990397839612768857)
                    ·
                      rfl

theorem cell22_3532728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_3532728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532728 prefixEnd_3532728 := by exact prefixLift 3532728
  have htrace : WordTrace (prefixWord ++ tailWord_3532728) baseStart_3532728 baseEnd_3532728 := by
    simpa [prefixWord, tailWord_3532728, baseEnd_3532728] using wordTrace_append hprefix tailTrace_3532728
  have hstable : (prefixWord ++ tailWord_3532728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532728).length < 2 ^ (prefixWord ++ tailWord_3532728).sum := by decide
  have hdescent : baseEnd_3532728 < baseStart_3532728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532732 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_3532732 : Nat := 118140960795 + 3532732 * 2 ^ 59
def prefixEnd_3532732 : Nat := 4983230072969 + 3 ^ 40 * 3532732 * 2
def baseEnd_3532732 : Nat := 1209326359679584935668845

theorem tailTrace_3532732 : CollatzResearch.WordTrace tailWord_3532732 prefixEnd_3532732 1209326359679584935668845 := by
  unfold tailWord_3532732
  simp only [CollatzResearch.WordTrace]
  refine ⟨64424660718761390718076225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85899547625015187624101633 64424660718761390718076225)
  ·
    refine ⟨48318495539071043038557169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64424660718761390718076225 48318495539071043038557169)
    ·
      refine ⟨36238871654303282278917877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48318495539071043038557169 36238871654303282278917877)
      ·
        refine ⟨3397394217590932713648551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36238871654303282278917877 3397394217590932713648551)
        ·
          refine ⟨5096091326386399070472827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397394217590932713648551 5096091326386399070472827)
          ·
            refine ⟨7644136989579598605709241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096091326386399070472827 7644136989579598605709241)
            ·
              refine ⟨5733102742184698954281931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644136989579598605709241 5733102742184698954281931)
              ·
                refine ⟨8599654113277048431422897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733102742184698954281931 8599654113277048431422897)
                ·
                  refine ⟨6449740584957786323567173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599654113277048431422897 6449740584957786323567173)
                  ·
                    refine ⟨1209326359679584935668845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6449740584957786323567173 1209326359679584935668845)
                    ·
                      rfl

theorem cell22_3532732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_3532732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532732 prefixEnd_3532732 := by exact prefixLift 3532732
  have htrace : WordTrace (prefixWord ++ tailWord_3532732) baseStart_3532732 baseEnd_3532732 := by
    simpa [prefixWord, tailWord_3532732, baseEnd_3532732] using wordTrace_append hprefix tailTrace_3532732
  have hstable : (prefixWord ++ tailWord_3532732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532732).length < 2 ^ (prefixWord ++ tailWord_3532732).sum := by decide
  have hdescent : baseEnd_3532732 < baseStart_3532732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532741 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 7]
def baseStart_3532741 : Nat := 118140960795 + 3532741 * 2 ^ 59
def prefixEnd_3532741 : Nat := 4983230072969 + 3 ^ 40 * 3532741 * 2
def baseEnd_3532741 : Nat := 403109813521170637397939

theorem tailTrace_3532741 : CollatzResearch.WordTrace tailWord_3532741 prefixEnd_3532741 403109813521170637397939 := by
  unfold tailWord_3532741
  simp only [CollatzResearch.WordTrace]
  refine ⟨128849649694490175973230077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85899766462993450648820051 128849649694490175973230077)
  ·
    refine ⟨48318618635433815989961279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128849649694490175973230077 48318618635433815989961279)
    ·
      refine ⟨72477927953150723984941919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48318618635433815989961279 72477927953150723984941919)
      ·
        refine ⟨108716891929726085977412879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72477927953150723984941919 108716891929726085977412879)
        ·
          refine ⟨163075337894589128966119319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108716891929726085977412879 163075337894589128966119319)
          ·
            refine ⟨244613006841883693449178979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163075337894589128966119319 244613006841883693449178979)
            ·
              refine ⟨366919510262825540173768469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244613006841883693449178979 366919510262825540173768469)
              ·
                refine ⟨17199352043569947195645397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 366919510262825540173768469 17199352043569947195645397)
                ·
                  refine ⟨403109813521170637397939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17199352043569947195645397 403109813521170637397939)
                  ·
                    rfl

theorem cell22_3532741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_3532741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532741 prefixEnd_3532741 := by exact prefixLift 3532741
  have htrace : WordTrace (prefixWord ++ tailWord_3532741) baseStart_3532741 baseEnd_3532741 := by
    simpa [prefixWord, tailWord_3532741, baseEnd_3532741] using wordTrace_append hprefix tailTrace_3532741
  have hstable : (prefixWord ++ tailWord_3532741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532741).length < 2 ^ (prefixWord ++ tailWord_3532741).sum := by decide
  have hdescent : baseEnd_3532741 < baseStart_3532741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
