import V185TrunkScan20Chunk094

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_577224 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_577224 : Nat := 118140960795 + 577224 * 2 ^ 59
def prefixEnd_577224 : Nat := 4983230072969 + 3 ^ 40 * 577224 * 2
def baseEnd_577224 : Nat := 263460762054182081907023

theorem tailTrace_577224 : CollatzResearch.WordTrace tailWord_577224 prefixEnd_577224 263460762054182081907023 := by
  unfold tailWord_577224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526544430411752427897363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14035392573882336570529817 10526544430411752427897363)
  ·
    refine ⟨15789816645617628641846045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10526544430411752427897363 15789816645617628641846045)
    ·
      refine ⟨5921181242106610740692267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15789816645617628641846045 5921181242106610740692267)
      ·
        refine ⟨8881771863159916111038401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5921181242106610740692267 8881771863159916111038401)
        ·
          refine ⟨6661328897369937083278801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8881771863159916111038401 6661328897369937083278801)
          ·
            refine ⟨4995996673027452812459101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6661328897369937083278801 4995996673027452812459101)
            ·
              refine ⟨1873498752385294804672163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4995996673027452812459101 1873498752385294804672163)
              ·
                refine ⟨2810248128577942207008245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873498752385294804672163 2810248128577942207008245)
                ·
                  refine ⟨263460762054182081907023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2810248128577942207008245 263460762054182081907023)
                  ·
                    rfl

theorem cell20_577224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_577224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577224 prefixEnd_577224 := by exact prefixLift 577224
  have htrace : WordTrace (prefixWord ++ tailWord_577224) baseStart_577224 baseEnd_577224 := by
    simpa [prefixWord, tailWord_577224, baseEnd_577224] using wordTrace_append hprefix tailTrace_577224
  have hstable : (prefixWord ++ tailWord_577224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577224).length < 2 ^ (prefixWord ++ tailWord_577224).sum := by decide
  have hdescent : baseEnd_577224 < baseStart_577224 := by decide
  rcases family_descends (prefixWord ++ tailWord_577224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577251 : List Nat := [1, 1, 1, 7, 2, 2, 2, 4]
def baseStart_577251 : Nat := 118140960795 + 577251 * 2 ^ 59
def prefixEnd_577251 : Nat := 4983230072969 + 3 ^ 40 * 577251 * 2
def baseEnd_577251 : Nat := 87824361863296662668971

theorem tailTrace_577251 : CollatzResearch.WordTrace tailWord_577251 prefixEnd_577251 87824361863296662668971 := by
  unfold tailWord_577251
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054073631725688467027607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14036049087817125644685071 21054073631725688467027607)
  ·
    refine ⟨31581110447588532700541411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21054073631725688467027607 31581110447588532700541411)
    ·
      refine ⟨47371665671382799050812117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31581110447588532700541411 47371665671382799050812117)
      ·
        refine ⟨1110273414173034352753409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 47371665671382799050812117 1110273414173034352753409)
        ·
          refine ⟨832705060629775764565057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110273414173034352753409 832705060629775764565057)
          ·
            refine ⟨624528795472331823423793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832705060629775764565057 624528795472331823423793)
            ·
              refine ⟨468396596604248867567845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624528795472331823423793 468396596604248867567845)
              ·
                refine ⟨87824361863296662668971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468396596604248867567845 87824361863296662668971)
                ·
                  rfl

theorem cell20_577251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_577251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577251 prefixEnd_577251 := by exact prefixLift 577251
  have htrace : WordTrace (prefixWord ++ tailWord_577251) baseStart_577251 baseEnd_577251 := by
    simpa [prefixWord, tailWord_577251, baseEnd_577251] using wordTrace_append hprefix tailTrace_577251
  have hstable : (prefixWord ++ tailWord_577251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577251).length < 2 ^ (prefixWord ++ tailWord_577251).sum := by decide
  have hdescent : baseEnd_577251 < baseStart_577251 := by decide
  rcases family_descends (prefixWord ++ tailWord_577251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577262 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_577262 : Nat := 118140960795 + 577262 * 2 ^ 59
def prefixEnd_577262 : Nat := 4983230072969 + 3 ^ 40 * 577262 * 2
def baseEnd_577262 : Nat := 263478106289622838640201

theorem tailTrace_577262 : CollatzResearch.WordTrace tailWord_577262 prefixEnd_577262 263478106289622838640201 := by
  unfold tailWord_577262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631809354335729668209755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14036316556457224897118693 2631809354335729668209755)
  ·
    refine ⟨3947714031503594502314633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2631809354335729668209755 3947714031503594502314633)
    ·
      refine ⟨2960785523627695876735975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3947714031503594502314633 2960785523627695876735975)
      ·
        refine ⟨4441178285441543815103963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960785523627695876735975 4441178285441543815103963)
        ·
          refine ⟨6661767428162315722655945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441178285441543815103963 6661767428162315722655945)
          ·
            refine ⟨4996325571121736791991959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6661767428162315722655945 4996325571121736791991959)
            ·
              refine ⟨7494488356682605187987939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996325571121736791991959 7494488356682605187987939)
              ·
                refine ⟨11241732535023907781981909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7494488356682605187987939 11241732535023907781981909)
                ·
                  refine ⟨263478106289622838640201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11241732535023907781981909 263478106289622838640201)
                  ·
                    rfl

theorem cell20_577262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_577262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577262 prefixEnd_577262 := by exact prefixLift 577262
  have htrace : WordTrace (prefixWord ++ tailWord_577262) baseStart_577262 baseEnd_577262 := by
    simpa [prefixWord, tailWord_577262, baseEnd_577262] using wordTrace_append hprefix tailTrace_577262
  have hstable : (prefixWord ++ tailWord_577262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577262).length < 2 ^ (prefixWord ++ tailWord_577262).sum := by decide
  have hdescent : baseEnd_577262 < baseStart_577262 := by decide
  rcases family_descends (prefixWord ++ tailWord_577262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577265 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 2]
def baseStart_577265 : Nat := 118140960795 + 577265 * 2 ^ 59
def prefixEnd_577265 : Nat := 4983230072969 + 3 ^ 40 * 577265 * 2
def baseEnd_577265 : Nat := 263479475571368161540189

theorem tailTrace_577265 : CollatzResearch.WordTrace tailWord_577265 prefixEnd_577265 263479475571368161540189 := by
  unfold tailWord_577265
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054584253674968858037249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14036389502449979238691499 21054584253674968858037249)
  ·
    refine ⟨15790938190256226643527937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21054584253674968858037249 15790938190256226643527937)
    ·
      refine ⟨11843203642692169982645953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15790938190256226643527937 11843203642692169982645953)
      ·
        refine ⟨8882402732019127486984465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11843203642692169982645953 8882402732019127486984465)
        ·
          refine ⟨6661802049014345615238349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8882402732019127486984465 6661802049014345615238349)
          ·
            refine ⟨2498175768380379605714381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6661802049014345615238349 2498175768380379605714381)
            ·
              refine ⟨936815913142642352142893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2498175768380379605714381 936815913142642352142893)
              ·
                refine ⟨351305967428490882053585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 936815913142642352142893 351305967428490882053585)
                ·
                  refine ⟨263479475571368161540189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351305967428490882053585 263479475571368161540189)
                  ·
                    rfl

theorem cell20_577265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_577265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577265 prefixEnd_577265 := by exact prefixLift 577265
  have htrace : WordTrace (prefixWord ++ tailWord_577265) baseStart_577265 baseEnd_577265 := by
    simpa [prefixWord, tailWord_577265, baseEnd_577265] using wordTrace_append hprefix tailTrace_577265
  have hstable : (prefixWord ++ tailWord_577265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577265).length < 2 ^ (prefixWord ++ tailWord_577265).sum := by decide
  have hdescent : baseEnd_577265 < baseStart_577265 := by decide
  rcases family_descends (prefixWord ++ tailWord_577265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577331 : List Nat := [1, 1, 1, 2, 8, 7]
def baseStart_577331 : Nat := 118140960795 + 577331 * 2 ^ 59
def prefixEnd_577331 : Nat := 4983230072969 + 3 ^ 40 * 577331 * 2
def baseEnd_577331 : Nat := 9759614806287602419997

theorem tailTrace_577331 : CollatzResearch.WordTrace tailWord_577331 prefixEnd_577331 9759614806287602419997 := by
  unfold tailWord_577331
  simp only [CollatzResearch.WordTrace]
  refine ⟨21056991471435862129939847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14037994314290574753293231 21056991471435862129939847)
  ·
    refine ⟨31585487207153793194909771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21056991471435862129939847 31585487207153793194909771)
    ·
      refine ⟨47378230810730689792364657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31585487207153793194909771 47378230810730689792364657)
      ·
        refine ⟨35533673108048017344273493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47378230810730689792364657 35533673108048017344273493)
        ·
          refine ⟨416410231734937703253205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 35533673108048017344273493 416410231734937703253205)
          ·
            refine ⟨9759614806287602419997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 416410231734937703253205 9759614806287602419997)
            ·
              rfl

theorem cell20_577331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 7].length) (baseStart_577331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577331 prefixEnd_577331 := by exact prefixLift 577331
  have htrace : WordTrace (prefixWord ++ tailWord_577331) baseStart_577331 baseEnd_577331 := by
    simpa [prefixWord, tailWord_577331, baseEnd_577331] using wordTrace_append hprefix tailTrace_577331
  have hstable : (prefixWord ++ tailWord_577331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577331).length < 2 ^ (prefixWord ++ tailWord_577331).sum := by decide
  have hdescent : baseEnd_577331 < baseStart_577331 := by decide
  rcases family_descends (prefixWord ++ tailWord_577331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577334 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_577334 : Nat := 118140960795 + 577334 * 2 ^ 59
def prefixEnd_577334 : Nat := 4983230072969 + 3 ^ 40 * 577334 * 2
def baseEnd_577334 : Nat := 263510969051510588239907

theorem tailTrace_577334 : CollatzResearch.WordTrace tailWord_577334 prefixEnd_577334 263510969051510588239907 := by
  unfold tailWord_577334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316068805651562102643691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14038067260283329094866037 1316068805651562102643691)
  ·
    refine ⟨1974103208477343153965537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316068805651562102643691 1974103208477343153965537)
    ·
      refine ⟨1480577406358007365474153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1974103208477343153965537 1480577406358007365474153)
      ·
        refine ⟨1110433054768505524105615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1480577406358007365474153 1110433054768505524105615)
        ·
          refine ⟨1665649582152758286158423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110433054768505524105615 1665649582152758286158423)
          ·
            refine ⟨2498474373229137429237635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665649582152758286158423 2498474373229137429237635)
            ·
              refine ⟨3747711559843706143856453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498474373229137429237635 3747711559843706143856453)
              ·
                refine ⟨702695917470694901973085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3747711559843706143856453 702695917470694901973085)
                ·
                  refine ⟨263510969051510588239907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702695917470694901973085 263510969051510588239907)
                  ·
                    rfl

theorem cell20_577334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_577334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577334 prefixEnd_577334 := by exact prefixLift 577334
  have htrace : WordTrace (prefixWord ++ tailWord_577334) baseStart_577334 baseEnd_577334 := by
    simpa [prefixWord, tailWord_577334, baseEnd_577334] using wordTrace_append hprefix tailTrace_577334
  have hstable : (prefixWord ++ tailWord_577334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577334).length < 2 ^ (prefixWord ++ tailWord_577334).sum := by decide
  have hdescent : baseEnd_577334 < baseStart_577334 := by decide
  rcases family_descends (prefixWord ++ tailWord_577334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577362 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_577362 : Nat := 118140960795 + 577362 * 2 ^ 59
def prefixEnd_577362 : Nat := 4983230072969 + 3 ^ 40 * 577362 * 2
def baseEnd_577362 : Nat := 263523749014466935306459

theorem tailTrace_577362 : CollatzResearch.WordTrace tailWord_577362 prefixEnd_577362 263523749014466935306459 := by
  unfold tailWord_577362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5264530533580888606079585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14038748089549036282878893 5264530533580888606079585)
  ·
    refine ⟨3948397900185666454559689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5264530533580888606079585 3948397900185666454559689)
    ·
      refine ⟨2961298425139249840919767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3948397900185666454559689 2961298425139249840919767)
      ·
        refine ⟨4441947637708874761379651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961298425139249840919767 4441947637708874761379651)
        ·
          refine ⟨6662921456563312142069477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441947637708874761379651 6662921456563312142069477)
          ·
            refine ⟨1249297773105621026638027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6662921456563312142069477 1249297773105621026638027)
            ·
              refine ⟨1873946659658431539957041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249297773105621026638027 1873946659658431539957041)
              ·
                refine ⟨1405459994743823654967781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873946659658431539957041 1405459994743823654967781)
                ·
                  refine ⟨263523749014466935306459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405459994743823654967781 263523749014466935306459)
                  ·
                    rfl

theorem cell20_577362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_577362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577362 prefixEnd_577362 := by exact prefixLift 577362
  have htrace : WordTrace (prefixWord ++ tailWord_577362) baseStart_577362 baseEnd_577362 := by
    simpa [prefixWord, tailWord_577362, baseEnd_577362] using wordTrace_append hprefix tailTrace_577362
  have hstable : (prefixWord ++ tailWord_577362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577362).length < 2 ^ (prefixWord ++ tailWord_577362).sum := by decide
  have hdescent : baseEnd_577362 < baseStart_577362 := by decide
  rcases family_descends (prefixWord ++ tailWord_577362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577369 : List Nat := [1, 2, 1, 2, 2, 3, 5, 4]
def baseStart_577369 : Nat := 118140960795 + 577369 * 2 ^ 59
def prefixEnd_577369 : Nat := 4983230072969 + 3 ^ 40 * 577369 * 2
def baseEnd_577369 : Nat := 87842314668402007357699

theorem tailTrace_577369 : CollatzResearch.WordTrace tailWord_577369 prefixEnd_577369 87842314668402007357699 := by
  unfold tailWord_577369
  simp only [CollatzResearch.WordTrace]
  refine ⟨21058377445298194619823161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14038918296865463079882107 21058377445298194619823161)
  ·
    refine ⟨15793783083973645964867371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21058377445298194619823161 15793783083973645964867371)
    ·
      refine ⟨23690674625960468947301057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15793783083973645964867371 23690674625960468947301057)
      ·
        refine ⟨17768005969470351710475793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23690674625960468947301057 17768005969470351710475793)
        ·
          refine ⟨13326004477102763782856845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17768005969470351710475793 13326004477102763782856845)
          ·
            refine ⟨4997251678913536418571317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13326004477102763782856845 4997251678913536418571317)
            ·
              refine ⟨468492344898144039241061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4997251678913536418571317 468492344898144039241061)
              ·
                refine ⟨87842314668402007357699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468492344898144039241061 87842314668402007357699)
                ·
                  rfl

theorem cell20_577369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_577369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577369 prefixEnd_577369 := by exact prefixLift 577369
  have htrace : WordTrace (prefixWord ++ tailWord_577369) baseStart_577369 baseEnd_577369 := by
    simpa [prefixWord, tailWord_577369, baseEnd_577369] using wordTrace_append hprefix tailTrace_577369
  have hstable : (prefixWord ++ tailWord_577369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577369).length < 2 ^ (prefixWord ++ tailWord_577369).sum := by decide
  have hdescent : baseEnd_577369 < baseStart_577369 := by decide
  rcases family_descends (prefixWord ++ tailWord_577369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577383 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_577383 : Nat := 118140960795 + 577383 * 2 ^ 59
def prefixEnd_577383 : Nat := 4983230072969 + 3 ^ 40 * 577383 * 2
def baseEnd_577383 : Nat := 263533333986684195606373

theorem tailTrace_577383 : CollatzResearch.WordTrace tailWord_577383 prefixEnd_577383 263533333986684195606373 := by
  unfold tailWord_577383
  simp only [CollatzResearch.WordTrace]
  refine ⟨21058888067247475010832803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14039258711498316673888535 21058888067247475010832803)
  ·
    refine ⟨31588332100871212516249205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21058888067247475010832803 31588332100871212516249205)
    ·
      refine ⟨2961406134456676173398363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31588332100871212516249205 2961406134456676173398363)
      ·
        refine ⟨4442109201685014260097545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961406134456676173398363 4442109201685014260097545)
        ·
          refine ⟨3331581901263760695073159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4442109201685014260097545 3331581901263760695073159)
          ·
            refine ⟨4997372851895641042609739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3331581901263760695073159 4997372851895641042609739)
            ·
              refine ⟨7496059277843461563914609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997372851895641042609739 7496059277843461563914609)
              ·
                refine ⟨5622044458382596172935957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7496059277843461563914609 5622044458382596172935957)
                ·
                  refine ⟨263533333986684195606373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5622044458382596172935957 263533333986684195606373)
                  ·
                    rfl

theorem cell20_577383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_577383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577383 prefixEnd_577383 := by exact prefixLift 577383
  have htrace : WordTrace (prefixWord ++ tailWord_577383) baseStart_577383 baseEnd_577383 := by
    simpa [prefixWord, tailWord_577383, baseEnd_577383] using wordTrace_append hprefix tailTrace_577383
  have hstable : (prefixWord ++ tailWord_577383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577383).length < 2 ^ (prefixWord ++ tailWord_577383).sum := by decide
  have hdescent : baseEnd_577383 < baseStart_577383 := by decide
  rcases family_descends (prefixWord ++ tailWord_577383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577386 : List Nat := [3, 1, 3, 4, 1, 1, 7]
def baseStart_577386 : Nat := 118140960795 + 577386 * 2 ^ 59
def prefixEnd_577386 : Nat := 4983230072969 + 3 ^ 40 * 577386 * 2
def baseEnd_577386 : Nat := 29281633696492168722929

theorem tailTrace_577386 : CollatzResearch.WordTrace tailWord_577386 prefixEnd_577386 29281633696492168722929 := by
  unfold tailWord_577386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5264749371559151630798003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14039331657491071015461341 5264749371559151630798003)
  ·
    refine ⟨7897124057338727446197005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5264749371559151630798003 7897124057338727446197005)
    ·
      refine ⟨2961421521502022792323877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7897124057338727446197005 2961421521502022792323877)
      ·
        refine ⟨555266535281629273560727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2961421521502022792323877 555266535281629273560727)
        ·
          refine ⟨832899802922443910341091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555266535281629273560727 832899802922443910341091)
          ·
            refine ⟨1249349704383665865511637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832899802922443910341091 1249349704383665865511637)
            ·
              refine ⟨29281633696492168722929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1249349704383665865511637 29281633696492168722929)
              ·
                rfl

theorem cell20_577386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 7].length) (baseStart_577386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577386 prefixEnd_577386 := by exact prefixLift 577386
  have htrace : WordTrace (prefixWord ++ tailWord_577386) baseStart_577386 baseEnd_577386 := by
    simpa [prefixWord, tailWord_577386, baseEnd_577386] using wordTrace_append hprefix tailTrace_577386
  have hstable : (prefixWord ++ tailWord_577386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577386).length < 2 ^ (prefixWord ++ tailWord_577386).sum := by decide
  have hdescent : baseEnd_577386 < baseStart_577386 := by decide
  rcases family_descends (prefixWord ++ tailWord_577386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577434 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_577434 : Nat := 118140960795 + 577434 * 2 ^ 59
def prefixEnd_577434 : Nat := 4983230072969 + 3 ^ 40 * 577434 * 2
def baseEnd_577434 : Nat := 263556611776354684906165

theorem tailTrace_577434 : CollatzResearch.WordTrace tailWord_577434 prefixEnd_577434 263556611776354684906165 := by
  unfold tailWord_577434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265187047515677680234839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14040498793375140480626237 5265187047515677680234839)
  ·
    refine ⟨7897780571273516520352259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5265187047515677680234839 7897780571273516520352259)
    ·
      refine ⟨11846670856910274780528389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7897780571273516520352259 11846670856910274780528389)
      ·
        refine ⟨2221250785670676521349073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11846670856910274780528389 2221250785670676521349073)
        ·
          refine ⟨1665938089253007391011805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221250785670676521349073 1665938089253007391011805)
          ·
            refine ⟨624726783469877771629427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1665938089253007391011805 624726783469877771629427)
            ·
              refine ⟨937090175204816657444141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624726783469877771629427 937090175204816657444141)
              ·
                refine ⟨351408815701806246541553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 937090175204816657444141 351408815701806246541553)
                ·
                  refine ⟨263556611776354684906165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351408815701806246541553 263556611776354684906165)
                  ·
                    rfl

theorem cell20_577434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_577434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577434 prefixEnd_577434 := by exact prefixLift 577434
  have htrace : WordTrace (prefixWord ++ tailWord_577434) baseStart_577434 baseEnd_577434 := by
    simpa [prefixWord, tailWord_577434, baseEnd_577434] using wordTrace_append hprefix tailTrace_577434
  have hstable : (prefixWord ++ tailWord_577434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577434).length < 2 ^ (prefixWord ++ tailWord_577434).sum := by decide
  have hdescent : baseEnd_577434 < baseStart_577434 := by decide
  rcases family_descends (prefixWord ++ tailWord_577434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577455 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 2]
def baseStart_577455 : Nat := 118140960795 + 577455 * 2 ^ 59
def prefixEnd_577455 : Nat := 4983230072969 + 3 ^ 40 * 577455 * 2
def baseEnd_577455 : Nat := 263566196748571945206079

theorem tailTrace_577455 : CollatzResearch.WordTrace tailWord_577455 prefixEnd_577455 263566196748571945206079 := by
  unfold tailWord_577455
  simp only [CollatzResearch.WordTrace]
  refine ⟨21061514122986631307453819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14041009415324420871635879 21061514122986631307453819)
  ·
    refine ⟨31592271184479946961180729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21061514122986631307453819 31592271184479946961180729)
    ·
      refine ⟨23694203388359960220885547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31592271184479946961180729 23694203388359960220885547)
      ·
        refine ⟨35541305082539940331328321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23694203388359960220885547 35541305082539940331328321)
        ·
          refine ⟨26655978811904955248496241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35541305082539940331328321 26655978811904955248496241)
          ·
            refine ⟨19991984108928716436372181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26655978811904955248496241 19991984108928716436372181)
            ·
              refine ⟨468562127553016791477473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19991984108928716436372181 468562127553016791477473)
              ·
                refine ⟨351421595664762593608105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468562127553016791477473 351421595664762593608105)
                ·
                  refine ⟨263566196748571945206079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351421595664762593608105 263566196748571945206079)
                  ·
                    rfl

theorem cell20_577455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 2].length) (baseStart_577455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577455 prefixEnd_577455 := by exact prefixLift 577455
  have htrace : WordTrace (prefixWord ++ tailWord_577455) baseStart_577455 baseEnd_577455 := by
    simpa [prefixWord, tailWord_577455, baseEnd_577455] using wordTrace_append hprefix tailTrace_577455
  have hstable : (prefixWord ++ tailWord_577455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577455).length < 2 ^ (prefixWord ++ tailWord_577455).sum := by decide
  have hdescent : baseEnd_577455 < baseStart_577455 := by decide
  rcases family_descends (prefixWord ++ tailWord_577455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577469 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_577469 : Nat := 118140960795 + 577469 * 2 ^ 59
def prefixEnd_577469 : Nat := 4983230072969 + 3 ^ 40 * 577469 * 2
def baseEnd_577469 : Nat := 263572586730050118739355

theorem tailTrace_577469 : CollatzResearch.WordTrace tailWord_577469 prefixEnd_577469 263572586730050118739355 := by
  unfold tailWord_577469
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062024744935911698463461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14041349829957274465642307 21062024744935911698463461)
  ·
    refine ⟨3949129639675483443461899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21062024744935911698463461 3949129639675483443461899)
    ·
      refine ⟨5923694459513225165192849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3949129639675483443461899 5923694459513225165192849)
      ·
        refine ⟨4442770844634918873894637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5923694459513225165192849 4442770844634918873894637)
        ·
          refine ⟨1666039066738094577710489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4442770844634918873894637 1666039066738094577710489)
          ·
            refine ⟨1249529300053570933282867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666039066738094577710489 1249529300053570933282867)
            ·
              refine ⟨1874293950080356399924301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249529300053570933282867 1874293950080356399924301)
              ·
                refine ⟨702860231280133649971613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1874293950080356399924301 702860231280133649971613)
                ·
                  refine ⟨263572586730050118739355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702860231280133649971613 263572586730050118739355)
                  ·
                    rfl

theorem cell20_577469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_577469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577469 prefixEnd_577469 := by exact prefixLift 577469
  have htrace : WordTrace (prefixWord ++ tailWord_577469) baseStart_577469 baseEnd_577469 := by
    simpa [prefixWord, tailWord_577469, baseEnd_577469] using wordTrace_append hprefix tailTrace_577469
  have hstable : (prefixWord ++ tailWord_577469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577469).length < 2 ^ (prefixWord ++ tailWord_577469).sum := by decide
  have hdescent : baseEnd_577469 < baseStart_577469 := by decide
  rcases family_descends (prefixWord ++ tailWord_577469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577500 : List Nat := [2, 2, 6, 1, 9]
def baseStart_577500 : Nat := 118140960795 + 577500 * 2 ^ 59
def prefixEnd_577500 : Nat := 4983230072969 + 3 ^ 40 * 577500 * 2
def baseEnd_577500 : Nat := 3254157234256194922295

theorem tailTrace_577500 : CollatzResearch.WordTrace tailWord_577500 prefixEnd_577500 3254157234256194922295 := by
  unfold tailWord_577500
  simp only [CollatzResearch.WordTrace]
  refine ⟨10531577703911801996420977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14042103605215735995227969 10531577703911801996420977)
  ·
    refine ⟨7898683277933851497315733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10531577703911801996420977 7898683277933851497315733)
    ·
      refine ⟨370250778653149288936675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7898683277933851497315733 370250778653149288936675)
      ·
        refine ⟨555376167979723933405013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370250778653149288936675 555376167979723933405013)
        ·
          refine ⟨3254157234256194922295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 555376167979723933405013 3254157234256194922295)
          ·
            rfl

theorem cell20_577500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 9].length) (baseStart_577500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577500 prefixEnd_577500 := by exact prefixLift 577500
  have htrace : WordTrace (prefixWord ++ tailWord_577500) baseStart_577500 baseEnd_577500 := by
    simpa [prefixWord, tailWord_577500, baseEnd_577500] using wordTrace_append hprefix tailTrace_577500
  have hstable : (prefixWord ++ tailWord_577500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577500).length < 2 ^ (prefixWord ++ tailWord_577500).sum := by decide
  have hdescent : baseEnd_577500 < baseStart_577500 := by decide
  rcases family_descends (prefixWord ++ tailWord_577500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577506 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_577506 : Nat := 118140960795 + 577506 * 2 ^ 59
def prefixEnd_577506 : Nat := 4983230072969 + 3 ^ 40 * 577506 * 2
def baseEnd_577506 : Nat := 263589474538242434505871

theorem tailTrace_577506 : CollatzResearch.WordTrace tailWord_577506 prefixEnd_577506 263589474538242434505871 := by
  unfold tailWord_577506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265843561450466754390093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14042249497201244678373581 5265843561450466754390093)
  ·
    refine ⟨1974691335543925032896285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5265843561450466754390093 1974691335543925032896285)
    ·
      refine ⟨740509250828971887336107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1974691335543925032896285 740509250828971887336107)
      ·
        refine ⟨1110763876243457831004161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740509250828971887336107 1110763876243457831004161)
        ·
          refine ⟨833072907182593373253121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110763876243457831004161 833072907182593373253121)
          ·
            refine ⟨624804680386945029939841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833072907182593373253121 624804680386945029939841)
            ·
              refine ⟨468603510290208772454881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624804680386945029939841 468603510290208772454881)
              ·
                refine ⟨351452632717656579341161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468603510290208772454881 351452632717656579341161)
                ·
                  refine ⟨263589474538242434505871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351452632717656579341161 263589474538242434505871)
                  ·
                    rfl

theorem cell20_577506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_577506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577506 prefixEnd_577506 := by exact prefixLift 577506
  have htrace : WordTrace (prefixWord ++ tailWord_577506) baseStart_577506 baseEnd_577506 := by
    simpa [prefixWord, tailWord_577506, baseEnd_577506] using wordTrace_append hprefix tailTrace_577506
  have hstable : (prefixWord ++ tailWord_577506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577506).length < 2 ^ (prefixWord ++ tailWord_577506).sum := by decide
  have hdescent : baseEnd_577506 < baseStart_577506 := by decide
  rcases family_descends (prefixWord ++ tailWord_577506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577507 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_577507 : Nat := 118140960795 + 577507 * 2 ^ 59
def prefixEnd_577507 : Nat := 4983230072969 + 3 ^ 40 * 577507 * 2
def baseEnd_577507 : Nat := 263589930965490875472533

theorem tailTrace_577507 : CollatzResearch.WordTrace tailWord_577507 prefixEnd_577507 263589930965490875472533 := by
  unfold tailWord_577507
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063410718798244188346775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14042273812532162792231183 21063410718798244188346775)
  ·
    refine ⟨31595116078197366282520163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21063410718798244188346775 31595116078197366282520163)
    ·
      refine ⟨47392674117296049423780245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31595116078197366282520163 47392674117296049423780245)
      ·
        refine ⟨2221531599248252316739699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47392674117296049423780245 2221531599248252316739699)
        ·
          refine ⟨3332297398872378475109549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221531599248252316739699 3332297398872378475109549)
          ·
            refine ⟨1249611524577141928166081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3332297398872378475109549 1249611524577141928166081)
            ·
              refine ⟨937208643432856446124561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249611524577141928166081 937208643432856446124561)
              ·
                refine ⟨702906482574642334593421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937208643432856446124561 702906482574642334593421)
                ·
                  refine ⟨263589930965490875472533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702906482574642334593421 263589930965490875472533)
                  ·
                    rfl

theorem cell20_577507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_577507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577507 prefixEnd_577507 := by exact prefixLift 577507
  have htrace : WordTrace (prefixWord ++ tailWord_577507) baseStart_577507 baseEnd_577507 := by
    simpa [prefixWord, tailWord_577507, baseEnd_577507] using wordTrace_append hprefix tailTrace_577507
  have hstable : (prefixWord ++ tailWord_577507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577507).length < 2 ^ (prefixWord ++ tailWord_577507).sum := by decide
  have hdescent : baseEnd_577507 < baseStart_577507 := by decide
  rcases family_descends (prefixWord ++ tailWord_577507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577517 : List Nat := [1, 5, 1, 4, 1, 2, 1, 5]
def baseStart_577517 : Nat := 118140960795 + 577517 * 2 ^ 59
def prefixEnd_577517 : Nat := 4983230072969 + 3 ^ 40 * 577517 * 2
def baseEnd_577517 : Nat := 87864831745991761713053

theorem tailTrace_577517 : CollatzResearch.WordTrace tailWord_577517 prefixEnd_577517 87864831745991761713053 := by
  unfold tailWord_577517
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063775448762015896210805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14042516965841343930807203 21063775448762015896210805)
  ·
    refine ⟨1974728948321438990269763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21063775448762015896210805 1974728948321438990269763)
    ·
      refine ⟨2962093422482158485404645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974728948321438990269763 2962093422482158485404645)
      ·
        refine ⟨555392516715404716013371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2962093422482158485404645 555392516715404716013371)
        ·
          refine ⟨833088775073107074020057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555392516715404716013371 833088775073107074020057)
          ·
            refine ⟨624816581304830305515043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833088775073107074020057 624816581304830305515043)
            ·
              refine ⟨937224871957245458272565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624816581304830305515043 937224871957245458272565)
              ·
                refine ⟨87864831745991761713053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 937224871957245458272565 87864831745991761713053)
                ·
                  rfl

theorem cell20_577517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_577517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577517 prefixEnd_577517 := by exact prefixLift 577517
  have htrace : WordTrace (prefixWord ++ tailWord_577517) baseStart_577517 baseEnd_577517 := by
    simpa [prefixWord, tailWord_577517, baseEnd_577517] using wordTrace_append hprefix tailTrace_577517
  have hstable : (prefixWord ++ tailWord_577517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577517).length < 2 ^ (prefixWord ++ tailWord_577517).sum := by decide
  have hdescent : baseEnd_577517 < baseStart_577517 := by decide
  rcases family_descends (prefixWord ++ tailWord_577517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577528 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_577528 : Nat := 118140960795 + 577528 * 2 ^ 59
def prefixEnd_577528 : Nat := 4983230072969 + 3 ^ 40 * 577528 * 2
def baseEnd_577528 : Nat := 263599515937708135772447

theorem tailTrace_577528 : CollatzResearch.WordTrace tailWord_577528 prefixEnd_577528 263599515937708135772447 := by
  unfold tailWord_577528
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532088325861082387430619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14042784434481443183240825 10532088325861082387430619)
  ·
    refine ⟨15798132488791623581145929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10532088325861082387430619 15798132488791623581145929)
    ·
      refine ⟨11848599366593717685859447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15798132488791623581145929 11848599366593717685859447)
      ·
        refine ⟨17772899049890576528789171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11848599366593717685859447 17772899049890576528789171)
        ·
          refine ⟨26659348574835864793183757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17772899049890576528789171 26659348574835864793183757)
          ·
            refine ⟨9997255715563449297443909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26659348574835864793183757 9997255715563449297443909)
            ·
              refine ⟨1874485446668146743270733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9997255715563449297443909 1874485446668146743270733)
              ·
                refine ⟨702932042500555028726525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1874485446668146743270733 702932042500555028726525)
                ·
                  refine ⟨263599515937708135772447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702932042500555028726525 263599515937708135772447)
                  ·
                    rfl

theorem cell20_577528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_577528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577528 prefixEnd_577528 := by exact prefixLift 577528
  have htrace : WordTrace (prefixWord ++ tailWord_577528) baseStart_577528 baseEnd_577528 := by
    simpa [prefixWord, tailWord_577528, baseEnd_577528] using wordTrace_append hprefix tailTrace_577528
  have hstable : (prefixWord ++ tailWord_577528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577528).length < 2 ^ (prefixWord ++ tailWord_577528).sum := by decide
  have hdescent : baseEnd_577528 < baseStart_577528 := by decide
  rcases family_descends (prefixWord ++ tailWord_577528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577559 : List Nat := [1, 1, 3, 5, 2, 1, 7]
def baseStart_577559 : Nat := 118140960795 + 577559 * 2 ^ 59
def prefixEnd_577559 : Nat := 4983230072969 + 3 ^ 40 * 577559 * 2
def baseEnd_577559 : Nat := 29290407242489978415443

theorem tailTrace_577559 : CollatzResearch.WordTrace tailWord_577559 prefixEnd_577559 29290407242489978415443 := by
  unfold tailWord_577559
  simp only [CollatzResearch.WordTrace]
  refine ⟨21065307314609857069239731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14043538209739904712826487 21065307314609857069239731)
  ·
    refine ⟨31597960971914785603859597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21065307314609857069239731 31597960971914785603859597)
    ·
      refine ⟨11849235364468044601447349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31597960971914785603859597 11849235364468044601447349)
      ·
        refine ⟨1110865815418879181385689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11849235364468044601447349 1110865815418879181385689)
        ·
          refine ⟨833149361564159386039267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110865815418879181385689 833149361564159386039267)
          ·
            refine ⟨1249724042346239079058901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833149361564159386039267 1249724042346239079058901)
            ·
              refine ⟨29290407242489978415443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1249724042346239079058901 29290407242489978415443)
              ·
                rfl

theorem cell20_577559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_577559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577559 prefixEnd_577559 := by exact prefixLift 577559
  have htrace : WordTrace (prefixWord ++ tailWord_577559) baseStart_577559 baseEnd_577559 := by
    simpa [prefixWord, tailWord_577559, baseEnd_577559] using wordTrace_append hprefix tailTrace_577559
  have hstable : (prefixWord ++ tailWord_577559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577559).length < 2 ^ (prefixWord ++ tailWord_577559).sum := by decide
  have hdescent : baseEnd_577559 < baseStart_577559 := by decide
  rcases family_descends (prefixWord ++ tailWord_577559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577573 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_577573 : Nat := 118140960795 + 577573 * 2 ^ 59
def prefixEnd_577573 : Nat := 4983230072969 + 3 ^ 40 * 577573 * 2
def baseEnd_577573 : Nat := 263620055163887979272263

theorem tailTrace_577573 : CollatzResearch.WordTrace tailWord_577573 prefixEnd_577573 263620055163887979272263 := by
  unfold tailWord_577573
  simp only [CollatzResearch.WordTrace]
  refine ⟨21065817936559137460249373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14043878624372758306832915 21065817936559137460249373)
  ·
    refine ⟨7899681726209676547593515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21065817936559137460249373 7899681726209676547593515)
    ·
      refine ⟨11849522589314514821390273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7899681726209676547593515 11849522589314514821390273)
      ·
        refine ⟨8887141941985886116042705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11849522589314514821390273 8887141941985886116042705)
        ·
          refine ⟨6665356456489414587032029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8887141941985886116042705 6665356456489414587032029)
          ·
            refine ⟨2499508671183530470137011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6665356456489414587032029 2499508671183530470137011)
            ·
              refine ⟨3749263006775295705205517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499508671183530470137011 3749263006775295705205517)
              ·
                refine ⟨1405973627540735889452069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3749263006775295705205517 1405973627540735889452069)
                ·
                  refine ⟨263620055163887979272263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405973627540735889452069 263620055163887979272263)
                  ·
                    rfl

theorem cell20_577573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_577573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577573 prefixEnd_577573 := by exact prefixLift 577573
  have htrace : WordTrace (prefixWord ++ tailWord_577573) baseStart_577573 baseEnd_577573 := by
    simpa [prefixWord, tailWord_577573, baseEnd_577573] using wordTrace_append hprefix tailTrace_577573
  have hstable : (prefixWord ++ tailWord_577573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577573).length < 2 ^ (prefixWord ++ tailWord_577573).sum := by decide
  have hdescent : baseEnd_577573 < baseStart_577573 := by decide
  rcases family_descends (prefixWord ++ tailWord_577573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577590 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_577590 : Nat := 118140960795 + 577590 * 2 ^ 59
def prefixEnd_577590 : Nat := 4983230072969 + 3 ^ 40 * 577590 * 2
def baseEnd_577590 : Nat := 263627814427111475705527

theorem tailTrace_577590 : CollatzResearch.WordTrace tailWord_577590 prefixEnd_577590 263627814427111475705527 := by
  unfold tailWord_577590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316652373593596835226139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14044291984998366242412149 1316652373593596835226139)
  ·
    refine ⟨1974978560390395252839209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316652373593596835226139 1974978560390395252839209)
    ·
      refine ⟨1481233920292796439629407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1974978560390395252839209 1481233920292796439629407)
      ·
        refine ⟨2221850880439194659444111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481233920292796439629407 2221850880439194659444111)
        ·
          refine ⟨3332776320658791989166167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221850880439194659444111 3332776320658791989166167)
          ·
            refine ⟨4999164480988187983749251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332776320658791989166167 4999164480988187983749251)
            ·
              refine ⟨7498746721482281975623877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999164480988187983749251 7498746721482281975623877)
              ·
                refine ⟨1406015010277927870429477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7498746721482281975623877 1406015010277927870429477)
                ·
                  refine ⟨263627814427111475705527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406015010277927870429477 263627814427111475705527)
                  ·
                    rfl

theorem cell20_577590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_577590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577590 prefixEnd_577590 := by exact prefixLift 577590
  have htrace : WordTrace (prefixWord ++ tailWord_577590) baseStart_577590 baseEnd_577590 := by
    simpa [prefixWord, tailWord_577590, baseEnd_577590] using wordTrace_append hprefix tailTrace_577590
  have hstable : (prefixWord ++ tailWord_577590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577590).length < 2 ^ (prefixWord ++ tailWord_577590).sum := by decide
  have hdescent : baseEnd_577590 < baseStart_577590 := by decide
  rcases family_descends (prefixWord ++ tailWord_577590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577593 : List Nat := [1, 2, 1, 5, 4, 1, 2, 4]
def baseStart_577593 : Nat := 118140960795 + 577593 * 2 ^ 59
def prefixEnd_577593 : Nat := 4983230072969 + 3 ^ 40 * 577593 * 2
def baseEnd_577593 : Nat := 87876394569618932868505

theorem tailTrace_577593 : CollatzResearch.WordTrace tailWord_577593 prefixEnd_577593 87876394569618932868505 := by
  unfold tailWord_577593
  simp only [CollatzResearch.WordTrace]
  refine ⟨21066547396486680875977433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14044364930991120583984955 21066547396486680875977433)
  ·
    refine ⟨15799910547365010656983075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21066547396486680875977433 15799910547365010656983075)
    ·
      refine ⟨23699865821047515985474613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15799910547365010656983075 23699865821047515985474613)
      ·
        refine ⟨2221862420723204623638245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23699865821047515985474613 2221862420723204623638245)
        ·
          refine ⟨416599203885600866932171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2221862420723204623638245 416599203885600866932171)
          ·
            refine ⟨624898805828401300398257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416599203885600866932171 624898805828401300398257)
            ·
              refine ⟨468674104371300975298693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624898805828401300398257 468674104371300975298693)
              ·
                refine ⟨87876394569618932868505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468674104371300975298693 87876394569618932868505)
                ·
                  rfl

theorem cell20_577593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].length) (baseStart_577593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577593 prefixEnd_577593 := by exact prefixLift 577593
  have htrace : WordTrace (prefixWord ++ tailWord_577593) baseStart_577593 baseEnd_577593 := by
    simpa [prefixWord, tailWord_577593, baseEnd_577593] using wordTrace_append hprefix tailTrace_577593
  have hstable : (prefixWord ++ tailWord_577593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577593).length < 2 ^ (prefixWord ++ tailWord_577593).sum := by decide
  have hdescent : baseEnd_577593 < baseStart_577593 := by decide
  rcases family_descends (prefixWord ++ tailWord_577593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577625 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_577625 : Nat := 118140960795 + 577625 * 2 ^ 59
def prefixEnd_577625 : Nat := 4983230072969 + 3 ^ 40 * 577625 * 2
def baseEnd_577625 : Nat := 263643789380806909538717

theorem tailTrace_577625 : CollatzResearch.WordTrace tailWord_577625 prefixEnd_577625 263643789380806909538717 := by
  unfold tailWord_577625
  simp only [CollatzResearch.WordTrace]
  refine ⟨21067714532370750341142329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14045143021580500227428219 21067714532370750341142329)
  ·
    refine ⟨15800785899278062755856747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21067714532370750341142329 15800785899278062755856747)
    ·
      refine ⟨23701178848917094133785121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15800785899278062755856747 23701178848917094133785121)
      ·
        refine ⟨17775884136687820600338841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23701178848917094133785121 17775884136687820600338841)
        ·
          refine ⟨13331913102515865450254131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17775884136687820600338841 13331913102515865450254131)
          ·
            refine ⟨19997869653773798175381197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13331913102515865450254131 19997869653773798175381197)
            ·
              refine ⟨7499201120165174315767949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19997869653773798175381197 7499201120165174315767949)
              ·
                refine ⟨2812200420061940368412981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7499201120165174315767949 2812200420061940368412981)
                ·
                  refine ⟨263643789380806909538717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2812200420061940368412981 263643789380806909538717)
                  ·
                    rfl

theorem cell20_577625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_577625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577625 prefixEnd_577625 := by exact prefixLift 577625
  have htrace : WordTrace (prefixWord ++ tailWord_577625) baseStart_577625 baseEnd_577625 := by
    simpa [prefixWord, tailWord_577625, baseEnd_577625] using wordTrace_append hprefix tailTrace_577625
  have hstable : (prefixWord ++ tailWord_577625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577625).length < 2 ^ (prefixWord ++ tailWord_577625).sum := by decide
  have hdescent : baseEnd_577625 < baseStart_577625 := by decide
  rcases family_descends (prefixWord ++ tailWord_577625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577628 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_577628 : Nat := 118140960795 + 577628 * 2 ^ 59
def prefixEnd_577628 : Nat := 4983230072969 + 3 ^ 40 * 577628 * 2
def baseEnd_577628 : Nat := 263645158662552232438705

theorem tailTrace_577628 : CollatzResearch.WordTrace tailWord_577628 prefixEnd_577628 263645158662552232438705 := by
  unfold tailWord_577628
  simp only [CollatzResearch.WordTrace]
  refine ⟨10533911975679940926750769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14045215967573254569001025 10533911975679940926750769)
  ·
    refine ⟨7900433981759955695063077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10533911975679940926750769 7900433981759955695063077)
    ·
      refine ⟨1481331371579991692824327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7900433981759955695063077 1481331371579991692824327)
      ·
        refine ⟨2221997057369987539236491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481331371579991692824327 2221997057369987539236491)
        ·
          refine ⟨3332995586054981308854737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221997057369987539236491 3332995586054981308854737)
          ·
            refine ⟨2499746689541235981641053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3332995586054981308854737 2499746689541235981641053)
            ·
              refine ⟨937405008577963493115395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2499746689541235981641053 937405008577963493115395)
              ·
                refine ⟨1406107512866945239673093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937405008577963493115395 1406107512866945239673093)
                ·
                  refine ⟨263645158662552232438705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406107512866945239673093 263645158662552232438705)
                  ·
                    rfl

theorem cell20_577628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_577628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577628 prefixEnd_577628 := by exact prefixLift 577628
  have htrace : WordTrace (prefixWord ++ tailWord_577628) baseStart_577628 baseEnd_577628 := by
    simpa [prefixWord, tailWord_577628, baseEnd_577628] using wordTrace_append hprefix tailTrace_577628
  have hstable : (prefixWord ++ tailWord_577628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577628).length < 2 ^ (prefixWord ++ tailWord_577628).sum := by decide
  have hdescent : baseEnd_577628 < baseStart_577628 := by decide
  rcases family_descends (prefixWord ++ tailWord_577628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577634 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_577634 : Nat := 118140960795 + 577634 * 2 ^ 59
def prefixEnd_577634 : Nat := 4983230072969 + 3 ^ 40 * 577634 * 2
def baseEnd_577634 : Nat := 263647897226042878238681

theorem tailTrace_577634 : CollatzResearch.WordTrace tailWord_577634 prefixEnd_577634 263647897226042878238681 := by
  unfold tailWord_577634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267010697334536219554989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14045361859558763252146637 5267010697334536219554989)
  ·
    refine ⟨1975129011500451082333121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5267010697334536219554989 1975129011500451082333121)
    ·
      refine ⟨1481346758625338311749841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1975129011500451082333121 1481346758625338311749841)
      ·
        refine ⟨1111010068969003733812381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1481346758625338311749841 1111010068969003733812381)
        ·
          refine ⟨416628775863376400179643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1111010068969003733812381 416628775863376400179643)
          ·
            refine ⟨624943163795064600269465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416628775863376400179643 624943163795064600269465)
            ·
              refine ⟨468707372846298450202099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624943163795064600269465 468707372846298450202099)
              ·
                refine ⟨703061059269447675303149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468707372846298450202099 703061059269447675303149)
                ·
                  refine ⟨263647897226042878238681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703061059269447675303149 263647897226042878238681)
                  ·
                    rfl

theorem cell20_577634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_577634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577634 prefixEnd_577634 := by exact prefixLift 577634
  have htrace : WordTrace (prefixWord ++ tailWord_577634) baseStart_577634 baseEnd_577634 := by
    simpa [prefixWord, tailWord_577634, baseEnd_577634] using wordTrace_append hprefix tailTrace_577634
  have hstable : (prefixWord ++ tailWord_577634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577634).length < 2 ^ (prefixWord ++ tailWord_577634).sum := by decide
  have hdescent : baseEnd_577634 < baseStart_577634 := by decide
  rcases family_descends (prefixWord ++ tailWord_577634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577680 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_577680 : Nat := 118140960795 + 577680 * 2 ^ 59
def prefixEnd_577680 : Nat := 4983230072969 + 3 ^ 40 * 577680 * 2
def baseEnd_577680 : Nat := 263668892879471162705159

theorem tailTrace_577680 : CollatzResearch.WordTrace tailWord_577680 prefixEnd_577680 263668892879471162705159 := by
  unfold tailWord_577680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10534860273585747367197247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14046480364780996489596329 10534860273585747367197247)
  ·
    refine ⟨15802290410378621050795871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10534860273585747367197247 15802290410378621050795871)
    ·
      refine ⟨23703435615567931576193807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15802290410378621050795871 23703435615567931576193807)
      ·
        refine ⟨35555153423351897364290711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23703435615567931576193807 35555153423351897364290711)
        ·
          refine ⟨53332730135027846046436067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35555153423351897364290711 53332730135027846046436067)
          ·
            refine ⟨79999095202541769069654101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53332730135027846046436067 79999095202541769069654101)
            ·
              refine ⟨937489396904786356285009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 79999095202541769069654101 937489396904786356285009)
              ·
                refine ⟨703117047678589767213757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937489396904786356285009 703117047678589767213757)
                ·
                  refine ⟨263668892879471162705159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703117047678589767213757 263668892879471162705159)
                  ·
                    rfl

theorem cell20_577680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_577680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577680 prefixEnd_577680 := by exact prefixLift 577680
  have htrace : WordTrace (prefixWord ++ tailWord_577680) baseStart_577680 baseEnd_577680 := by
    simpa [prefixWord, tailWord_577680, baseEnd_577680] using wordTrace_append hprefix tailTrace_577680
  have hstable : (prefixWord ++ tailWord_577680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577680).length < 2 ^ (prefixWord ++ tailWord_577680).sum := by decide
  have hdescent : baseEnd_577680 < baseStart_577680 := by decide
  rcases family_descends (prefixWord ++ tailWord_577680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577690 : List Nat := [3, 1, 1, 5, 2, 2, 1, 5]
def baseStart_577690 : Nat := 118140960795 + 577690 * 2 ^ 59
def prefixEnd_577690 : Nat := 4983230072969 + 3 ^ 40 * 577690 * 2
def baseEnd_577690 : Nat := 87891152383985190790595

theorem tailTrace_577690 : CollatzResearch.WordTrace tailWord_577690 prefixEnd_577690 87891152383985190790595 := by
  unfold tailWord_577690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267521319283816610564631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14046723518090177628172349 5267521319283816610564631)
  ·
    refine ⟨7901281978925724915846947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5267521319283816610564631 7901281978925724915846947)
    ·
      refine ⟨11851922968388587373770421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7901281978925724915846947 11851922968388587373770421)
      ·
        refine ⟨1111117778286430066290977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11851922968388587373770421 1111117778286430066290977)
        ·
          refine ⟨833338333714822549718233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111117778286430066290977 833338333714822549718233)
          ·
            refine ⟨625003750286116912288675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833338333714822549718233 625003750286116912288675)
            ·
              refine ⟨937505625429175368433013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625003750286116912288675 937505625429175368433013)
              ·
                refine ⟨87891152383985190790595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 937505625429175368433013 87891152383985190790595)
                ·
                  rfl

theorem cell20_577690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_577690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577690 prefixEnd_577690 := by exact prefixLift 577690
  have htrace : WordTrace (prefixWord ++ tailWord_577690) baseStart_577690 baseEnd_577690 := by
    simpa [prefixWord, tailWord_577690, baseEnd_577690] using wordTrace_append hprefix tailTrace_577690
  have hstable : (prefixWord ++ tailWord_577690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577690).length < 2 ^ (prefixWord ++ tailWord_577690).sum := by decide
  have hdescent : baseEnd_577690 < baseStart_577690 := by decide
  rcases family_descends (prefixWord ++ tailWord_577690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577739 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_577739 : Nat := 118140960795 + 577739 * 2 ^ 59
def prefixEnd_577739 : Nat := 4983230072969 + 3 ^ 40 * 577739 * 2
def baseEnd_577739 : Nat := 263695822087129179738251

theorem tailTrace_577739 : CollatzResearch.WordTrace tailWord_577739 prefixEnd_577739 263695822087129179738251 := by
  unfold tailWord_577739
  simp only [CollatzResearch.WordTrace]
  refine ⟨21071872453957747810792271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14047914969305165207194847 21071872453957747810792271)
  ·
    refine ⟨31607808680936621716188407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21071872453957747810792271 31607808680936621716188407)
    ·
      refine ⟨47411713021404932574282611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31607808680936621716188407 47411713021404932574282611)
      ·
        refine ⟨71117569532107398861423917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47411713021404932574282611 71117569532107398861423917)
        ·
          refine ⟨26669088574540274573033969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71117569532107398861423917 26669088574540274573033969)
          ·
            refine ⟨20001816430905205929775477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26669088574540274573033969 20001816430905205929775477)
            ·
              refine ⟨1875170290397363055916451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20001816430905205929775477 1875170290397363055916451)
              ·
                refine ⟨2812755435596044583874677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875170290397363055916451 2812755435596044583874677)
                ·
                  refine ⟨263695822087129179738251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2812755435596044583874677 263695822087129179738251)
                  ·
                    rfl

theorem cell20_577739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_577739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577739 prefixEnd_577739 := by exact prefixLift 577739
  have htrace : WordTrace (prefixWord ++ tailWord_577739) baseStart_577739 baseEnd_577739 := by
    simpa [prefixWord, tailWord_577739, baseEnd_577739] using wordTrace_append hprefix tailTrace_577739
  have hstable : (prefixWord ++ tailWord_577739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577739).length < 2 ^ (prefixWord ++ tailWord_577739).sum := by decide
  have hdescent : baseEnd_577739 < baseStart_577739 := by decide
  rcases family_descends (prefixWord ++ tailWord_577739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577742 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_577742 : Nat := 118140960795 + 577742 * 2 ^ 59
def prefixEnd_577742 : Nat := 4983230072969 + 3 ^ 40 * 577742 * 2
def baseEnd_577742 : Nat := 263697191368874502638239

theorem tailTrace_577742 : CollatzResearch.WordTrace tailWord_577742 prefixEnd_577742 263697191368874502638239 := by
  unfold tailWord_577742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633997734118359915393935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14047987915297919548767653 2633997734118359915393935)
  ·
    refine ⟨3950996601177539873090903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2633997734118359915393935 3950996601177539873090903)
    ·
      refine ⟨5926494901766309809636355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950996601177539873090903 5926494901766309809636355)
      ·
        refine ⟨8889742352649464714454533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926494901766309809636355 8889742352649464714454533)
        ·
          refine ⟨1666826691121774633960225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8889742352649464714454533 1666826691121774633960225)
          ·
            refine ⟨1250120018341330975470169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666826691121774633960225 1250120018341330975470169)
            ·
              refine ⟨937590013755998231602627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250120018341330975470169 937590013755998231602627)
              ·
                refine ⟨1406385020633997347403941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937590013755998231602627 1406385020633997347403941)
                ·
                  refine ⟨263697191368874502638239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406385020633997347403941 263697191368874502638239)
                  ·
                    rfl

theorem cell20_577742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_577742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577742 prefixEnd_577742 := by exact prefixLift 577742
  have htrace : WordTrace (prefixWord ++ tailWord_577742) baseStart_577742 baseEnd_577742 := by
    simpa [prefixWord, tailWord_577742, baseEnd_577742] using wordTrace_append hprefix tailTrace_577742
  have hstable : (prefixWord ++ tailWord_577742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577742).length < 2 ^ (prefixWord ++ tailWord_577742).sum := by decide
  have hdescent : baseEnd_577742 < baseStart_577742 := by decide
  rcases family_descends (prefixWord ++ tailWord_577742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577770 : List Nat := [3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_577770 : Nat := 118140960795 + 577770 * 2 ^ 59
def prefixEnd_577770 : Nat := 4983230072969 + 3 ^ 40 * 577770 * 2
def baseEnd_577770 : Nat := 87903323777276949901597

theorem tailTrace_577770 : CollatzResearch.WordTrace tailWord_577770 prefixEnd_577770 87903323777276949901597 := by
  unfold tailWord_577770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268250779211360026292691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14048668744563626736780509 5268250779211360026292691)
  ·
    refine ⟨7902376168817040039439037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5268250779211360026292691 7902376168817040039439037)
    ·
      refine ⟨2963391063306390014789639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7902376168817040039439037 2963391063306390014789639)
      ·
        refine ⟨4445086594959585022184459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963391063306390014789639 4445086594959585022184459)
        ·
          refine ⟨6667629892439377533276689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445086594959585022184459 6667629892439377533276689)
          ·
            refine ⟨5000722419329533149957517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6667629892439377533276689 5000722419329533149957517)
            ·
              refine ⟨1875270907248574931234069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5000722419329533149957517 1875270907248574931234069)
              ·
                refine ⟨87903323777276949901597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1875270907248574931234069 87903323777276949901597)
                ·
                  rfl

theorem cell20_577770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_577770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577770 prefixEnd_577770 := by exact prefixLift 577770
  have htrace : WordTrace (prefixWord ++ tailWord_577770) baseStart_577770 baseEnd_577770 := by
    simpa [prefixWord, tailWord_577770, baseEnd_577770] using wordTrace_append hprefix tailTrace_577770
  have hstable : (prefixWord ++ tailWord_577770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577770).length < 2 ^ (prefixWord ++ tailWord_577770).sum := by decide
  have hdescent : baseEnd_577770 < baseStart_577770 := by decide
  rcases family_descends (prefixWord ++ tailWord_577770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577777 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_577777 : Nat := 118140960795 + 577777 * 2 ^ 59
def prefixEnd_577777 : Nat := 4983230072969 + 3 ^ 40 * 577777 * 2
def baseEnd_577777 : Nat := 263713166322569936471429

theorem tailTrace_577777 : CollatzResearch.WordTrace tailWord_577777 prefixEnd_577777 263713166322569936471429 := by
  unfold tailWord_577777
  simp only [CollatzResearch.WordTrace]
  refine ⟨21073258427820080300675585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14048838951880053533783723 21073258427820080300675585)
  ·
    refine ⟨15804943820865060225506689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21073258427820080300675585 15804943820865060225506689)
    ·
      refine ⟨11853707865648795169130017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15804943820865060225506689 11853707865648795169130017)
      ·
        refine ⟨8890280899236596376847513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11853707865648795169130017 8890280899236596376847513)
        ·
          refine ⟨6667710674427447282635635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8890280899236596376847513 6667710674427447282635635)
          ·
            refine ⟨10001566011641170923953453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667710674427447282635635 10001566011641170923953453)
            ·
              refine ⟨3750587254365439096482545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10001566011641170923953453 3750587254365439096482545)
              ·
                refine ⟨2812940440774079322361909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750587254365439096482545 2812940440774079322361909)
                ·
                  refine ⟨263713166322569936471429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2812940440774079322361909 263713166322569936471429)
                  ·
                    rfl

theorem cell20_577777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_577777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577777 prefixEnd_577777 := by exact prefixLift 577777
  have htrace : WordTrace (prefixWord ++ tailWord_577777) baseStart_577777 baseEnd_577777 := by
    simpa [prefixWord, tailWord_577777, baseEnd_577777] using wordTrace_append hprefix tailTrace_577777
  have hstable : (prefixWord ++ tailWord_577777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577777).length < 2 ^ (prefixWord ++ tailWord_577777).sum := by decide
  have hdescent : baseEnd_577777 < baseStart_577777 := by decide
  rcases family_descends (prefixWord ++ tailWord_577777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577784 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_577784 : Nat := 118140960795 + 577784 * 2 ^ 59
def prefixEnd_577784 : Nat := 4983230072969 + 3 ^ 40 * 577784 * 2
def baseEnd_577784 : Nat := 263716361313309023238067

theorem tailTrace_577784 : CollatzResearch.WordTrace tailWord_577784 prefixEnd_577784 263716361313309023238067 := by
  unfold tailWord_577784
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536756869397360248090203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14049009159196480330786937 10536756869397360248090203)
  ·
    refine ⟨15805135304096040372135305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10536756869397360248090203 15805135304096040372135305)
    ·
      refine ⟨11853851478072030279101479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15805135304096040372135305 11853851478072030279101479)
      ·
        refine ⟨17780777217108045418652219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853851478072030279101479 17780777217108045418652219)
        ·
          refine ⟨26671165825662068127978329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17780777217108045418652219 26671165825662068127978329)
          ·
            refine ⟨20003374369246551095983747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26671165825662068127978329 20003374369246551095983747)
            ·
              refine ⟨30005061553869826643975621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20003374369246551095983747 30005061553869826643975621)
              ·
                refine ⟨5625949041350592495745429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30005061553869826643975621 5625949041350592495745429)
                ·
                  refine ⟨263716361313309023238067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5625949041350592495745429 263716361313309023238067)
                  ·
                    rfl

theorem cell20_577784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_577784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577784 prefixEnd_577784 := by exact prefixLift 577784
  have htrace : WordTrace (prefixWord ++ tailWord_577784) baseStart_577784 baseEnd_577784 := by
    simpa [prefixWord, tailWord_577784, baseEnd_577784] using wordTrace_append hprefix tailTrace_577784
  have hstable : (prefixWord ++ tailWord_577784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577784).length < 2 ^ (prefixWord ++ tailWord_577784).sum := by decide
  have hdescent : baseEnd_577784 < baseStart_577784 := by decide
  rcases family_descends (prefixWord ++ tailWord_577784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577801 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_577801 : Nat := 118140960795 + 577801 * 2 ^ 59
def prefixEnd_577801 : Nat := 4983230072969 + 3 ^ 40 * 577801 * 2
def baseEnd_577801 : Nat := 263724120576532519671331

theorem tailTrace_577801 : CollatzResearch.WordTrace tailWord_577801 prefixEnd_577801 263724120576532519671331 := by
  unfold tailWord_577801
  simp only [CollatzResearch.WordTrace]
  refine ⟨21074133779733132399549257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14049422519822088266366171 21074133779733132399549257)
  ·
    refine ⟨15805600334799849299661943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21074133779733132399549257 15805600334799849299661943)
    ·
      refine ⟨23708400502199773949492915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15805600334799849299661943 23708400502199773949492915)
      ·
        refine ⟨35562600753299660924239373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23708400502199773949492915 35562600753299660924239373)
        ·
          refine ⟨13335975282487372846589765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35562600753299660924239373 13335975282487372846589765)
          ·
            refine ⟨2500495365466382408735581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13335975282487372846589765 2500495365466382408735581)
            ·
              refine ⟨937685762049893403275843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500495365466382408735581 937685762049893403275843)
              ·
                refine ⟨1406528643074840104913765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937685762049893403275843 1406528643074840104913765)
                ·
                  refine ⟨263724120576532519671331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406528643074840104913765 263724120576532519671331)
                  ·
                    rfl

theorem cell20_577801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_577801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577801 prefixEnd_577801 := by exact prefixLift 577801
  have htrace : WordTrace (prefixWord ++ tailWord_577801) baseStart_577801 baseEnd_577801 := by
    simpa [prefixWord, tailWord_577801, baseEnd_577801] using wordTrace_append hprefix tailTrace_577801
  have hstable : (prefixWord ++ tailWord_577801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577801).length < 2 ^ (prefixWord ++ tailWord_577801).sum := by decide
  have hdescent : baseEnd_577801 < baseStart_577801 := by decide
  rcases family_descends (prefixWord ++ tailWord_577801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577846 : List Nat := [5, 1, 2, 12]
def baseStart_577846 : Nat := 118140960795 + 577846 * 2 ^ 59
def prefixEnd_577846 : Nat := 4983230072969 + 3 ^ 40 * 577846 * 2
def baseEnd_577846 : Nat := 1085368970381532358729

theorem tailTrace_577846 : CollatzResearch.WordTrace tailWord_577846 prefixEnd_577846 1085368970381532358729 := by
  unfold tailWord_577846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317235941535631567808587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14050516709713403389958261 1317235941535631567808587)
  ·
    refine ⟨1975853912303447351712881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1317235941535631567808587 1975853912303447351712881)
    ·
      refine ⟨1481890434227585513784661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1975853912303447351712881 1481890434227585513784661)
      ·
        refine ⟨1085368970381532358729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1481890434227585513784661 1085368970381532358729)
        ·
          rfl

theorem cell20_577846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 12].length) (baseStart_577846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577846 prefixEnd_577846 := by exact prefixLift 577846
  have htrace : WordTrace (prefixWord ++ tailWord_577846) baseStart_577846 baseEnd_577846 := by
    simpa [prefixWord, tailWord_577846, baseEnd_577846] using wordTrace_append hprefix tailTrace_577846
  have hstable : (prefixWord ++ tailWord_577846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577846).length < 2 ^ (prefixWord ++ tailWord_577846).sum := by decide
  have hdescent : baseEnd_577846 < baseStart_577846 := by decide
  rcases family_descends (prefixWord ++ tailWord_577846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577849 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_577849 : Nat := 118140960795 + 577849 * 2 ^ 59
def prefixEnd_577849 : Nat := 4983230072969 + 3 ^ 40 * 577849 * 2
def baseEnd_577849 : Nat := 263746029084457686071135

theorem tailTrace_577849 : CollatzResearch.WordTrace tailWord_577849 prefixEnd_577849 263746029084457686071135 := by
  unfold tailWord_577849
  simp only [CollatzResearch.WordTrace]
  refine ⟨21075884483559236597296601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14050589655706157731531067 21075884483559236597296601)
  ·
    refine ⟨15806913362669427447972451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21075884483559236597296601 15806913362669427447972451)
    ·
      refine ⟨23710370044004141171958677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15806913362669427447972451 23710370044004141171958677)
      ·
        refine ⟨1111423595812694117435563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23710370044004141171958677 1111423595812694117435563)
        ·
          refine ⟨1667135393719041176153345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111423595812694117435563 1667135393719041176153345)
          ·
            refine ⟨1250351545289280882115009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667135393719041176153345 1250351545289280882115009)
            ·
              refine ⟨937763658966960661586257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250351545289280882115009 937763658966960661586257)
              ·
                refine ⟨703322744225220496189693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937763658966960661586257 703322744225220496189693)
                ·
                  refine ⟨263746029084457686071135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703322744225220496189693 263746029084457686071135)
                  ·
                    rfl

theorem cell20_577849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_577849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577849 prefixEnd_577849 := by exact prefixLift 577849
  have htrace : WordTrace (prefixWord ++ tailWord_577849) baseStart_577849 baseEnd_577849 := by
    simpa [prefixWord, tailWord_577849, baseEnd_577849] using wordTrace_append hprefix tailTrace_577849
  have hstable : (prefixWord ++ tailWord_577849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577849).length < 2 ^ (prefixWord ++ tailWord_577849).sum := by decide
  have hdescent : baseEnd_577849 < baseStart_577849 := by decide
  rcases family_descends (prefixWord ++ tailWord_577849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577867 : List Nat := [1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_577867 : Nat := 118140960795 + 577867 * 2 ^ 59
def prefixEnd_577867 : Nat := 4983230072969 + 3 ^ 40 * 577867 * 2
def baseEnd_577867 : Nat := 87918081591643207823687

theorem tailTrace_577867 : CollatzResearch.WordTrace tailWord_577867 prefixEnd_577867 87918081591643207823687 := by
  unfold tailWord_577867
  simp only [CollatzResearch.WordTrace]
  refine ⟨21076540997494025671451855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14051027331662683780967903 21076540997494025671451855)
  ·
    refine ⟨31614811496241038507177783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21076540997494025671451855 31614811496241038507177783)
    ·
      refine ⟨47422217244361557760766675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31614811496241038507177783 47422217244361557760766675)
      ·
        refine ⟨71133325866542336641150013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47422217244361557760766675 71133325866542336641150013)
        ·
          refine ⟨26674997199953376240431255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71133325866542336641150013 26674997199953376240431255)
          ·
            refine ⟨40012495799930064360646883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26674997199953376240431255 40012495799930064360646883)
            ·
              refine ⟨60018743699895096540970325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40012495799930064360646883 60018743699895096540970325)
              ·
                refine ⟨87918081591643207823687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 60018743699895096540970325 87918081591643207823687)
                ·
                  rfl

theorem cell20_577867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_577867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577867 prefixEnd_577867 := by exact prefixLift 577867
  have htrace : WordTrace (prefixWord ++ tailWord_577867) baseStart_577867 baseEnd_577867 := by
    simpa [prefixWord, tailWord_577867, baseEnd_577867] using wordTrace_append hprefix tailTrace_577867
  have hstable : (prefixWord ++ tailWord_577867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577867).length < 2 ^ (prefixWord ++ tailWord_577867).sum := by decide
  have hdescent : baseEnd_577867 < baseStart_577867 := by decide
  rcases family_descends (prefixWord ++ tailWord_577867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577891 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_577891 : Nat := 118140960795 + 577891 * 2 ^ 59
def prefixEnd_577891 : Nat := 4983230072969 + 3 ^ 40 * 577891 * 2
def baseEnd_577891 : Nat := 263765199028892206670963

theorem tailTrace_577891 : CollatzResearch.WordTrace tailWord_577891 prefixEnd_577891 263765199028892206670963 := by
  unfold tailWord_577891
  simp only [CollatzResearch.WordTrace]
  refine ⟨21077416349407077770325527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14051610899604718513550351 21077416349407077770325527)
  ·
    refine ⟨31616124524110616655488291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21077416349407077770325527 31616124524110616655488291)
    ·
      refine ⟨47424186786165924983232437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31616124524110616655488291 47424186786165924983232437)
      ·
        refine ⟨4446017511203055467178041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47424186786165924983232437 4446017511203055467178041)
        ·
          refine ⟨3334513133402291600383531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4446017511203055467178041 3334513133402291600383531)
          ·
            refine ⟨5001769700103437400575297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334513133402291600383531 5001769700103437400575297)
            ·
              refine ⟨3751327275077578050431473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5001769700103437400575297 3751327275077578050431473)
              ·
                refine ⟨2813495456308183537823605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3751327275077578050431473 2813495456308183537823605)
                ·
                  refine ⟨263765199028892206670963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2813495456308183537823605 263765199028892206670963)
                  ·
                    rfl

theorem cell20_577891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_577891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577891 prefixEnd_577891 := by exact prefixLift 577891
  have htrace : WordTrace (prefixWord ++ tailWord_577891) baseStart_577891 baseEnd_577891 := by
    simpa [prefixWord, tailWord_577891, baseEnd_577891] using wordTrace_append hprefix tailTrace_577891
  have hstable : (prefixWord ++ tailWord_577891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577891).length < 2 ^ (prefixWord ++ tailWord_577891).sum := by decide
  have hdescent : baseEnd_577891 < baseStart_577891 := by decide
  rcases family_descends (prefixWord ++ tailWord_577891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577915 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_577915 : Nat := 118140960795 + 577915 * 2 ^ 59
def prefixEnd_577915 : Nat := 4983230072969 + 3 ^ 40 * 577915 * 2
def baseEnd_577915 : Nat := 263776153282854789870865

theorem tailTrace_577915 : CollatzResearch.WordTrace tailWord_577915 prefixEnd_577915 263776153282854789870865 := by
  unfold tailWord_577915
  simp only [CollatzResearch.WordTrace]
  refine ⟨21078291701320129869199199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14052194467546753246132799 21078291701320129869199199)
  ·
    refine ⟨31617437551980194803798799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21078291701320129869199199 31617437551980194803798799)
    ·
      refine ⟨47426156327970292205698199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31617437551980194803798799 47426156327970292205698199)
      ·
        refine ⟨71139234491955438308547299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47426156327970292205698199 71139234491955438308547299)
        ·
          refine ⟨106708851737933157462820949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71139234491955438308547299 106708851737933157462820949)
          ·
            refine ⟨1250494356303904189017433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 106708851737933157462820949 1250494356303904189017433)
            ·
              refine ⟨937870767227928141763075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250494356303904189017433 937870767227928141763075)
              ·
                refine ⟨1406806150841892212644613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937870767227928141763075 1406806150841892212644613)
                ·
                  refine ⟨263776153282854789870865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406806150841892212644613 263776153282854789870865)
                  ·
                    rfl

theorem cell20_577915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_577915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577915 prefixEnd_577915 := by exact prefixLift 577915
  have htrace : WordTrace (prefixWord ++ tailWord_577915) baseStart_577915 baseEnd_577915 := by
    simpa [prefixWord, tailWord_577915, baseEnd_577915] using wordTrace_append hprefix tailTrace_577915
  have hstable : (prefixWord ++ tailWord_577915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577915).length < 2 ^ (prefixWord ++ tailWord_577915).sum := by decide
  have hdescent : baseEnd_577915 < baseStart_577915 := by decide
  rcases family_descends (prefixWord ++ tailWord_577915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577962 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_577962 : Nat := 118140960795 + 577962 * 2 ^ 59
def prefixEnd_577962 : Nat := 4983230072969 + 3 ^ 40 * 577962 * 2
def baseEnd_577962 : Nat := 263797605363531515304007

theorem tailTrace_577962 : CollatzResearch.WordTrace tailWord_577962 prefixEnd_577962 263797605363531515304007 := by
  unfold tailWord_577962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270001483037464224040035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14053337288099904597440093 5270001483037464224040035)
  ·
    refine ⟨7905002224556196336060053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5270001483037464224040035 7905002224556196336060053)
    ·
      refine ⟨370546979276071703252815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7905002224556196336060053 370546979276071703252815)
      ·
        refine ⟨555820468914107554879223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370546979276071703252815 555820468914107554879223)
        ·
          refine ⟨833730703371161332318835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555820468914107554879223 833730703371161332318835)
          ·
            refine ⟨1250596055056741998478253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833730703371161332318835 1250596055056741998478253)
            ·
              refine ⟨468973520646278249429345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250596055056741998478253 468973520646278249429345)
              ·
                refine ⟨351730140484708687072009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468973520646278249429345 351730140484708687072009)
                ·
                  refine ⟨263797605363531515304007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351730140484708687072009 263797605363531515304007)
                  ·
                    rfl

theorem cell20_577962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_577962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577962 prefixEnd_577962 := by exact prefixLift 577962
  have htrace : WordTrace (prefixWord ++ tailWord_577962) baseStart_577962 baseEnd_577962 := by
    simpa [prefixWord, tailWord_577962, baseEnd_577962] using wordTrace_append hprefix tailTrace_577962
  have hstable : (prefixWord ++ tailWord_577962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577962).length < 2 ^ (prefixWord ++ tailWord_577962).sum := by decide
  have hdescent : baseEnd_577962 < baseStart_577962 := by decide
  rcases family_descends (prefixWord ++ tailWord_577962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577980 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_577980 : Nat := 118140960795 + 577980 * 2 ^ 59
def prefixEnd_577980 : Nat := 4983230072969 + 3 ^ 40 * 577980 * 2
def baseEnd_577980 : Nat := 263805821054003452703933

theorem tailTrace_577980 : CollatzResearch.WordTrace tailWord_577980 prefixEnd_577980 263805821054003452703933 := by
  unfold tailWord_577980
  simp only [CollatzResearch.WordTrace]
  refine ⟨10540331223042322985157697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14053774964056430646876929 10540331223042322985157697)
  ·
    refine ⟨7905248417281742238868273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10540331223042322985157697 7905248417281742238868273)
    ·
      refine ⟨5928936312961306679151205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7905248417281742238868273 5928936312961306679151205)
      ·
        refine ⟨1111675558680245002340851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5928936312961306679151205 1111675558680245002340851)
        ·
          refine ⟨1667513338020367503511277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111675558680245002340851 1667513338020367503511277)
          ·
            refine ⟨625317501757637813816729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1667513338020367503511277 625317501757637813816729)
            ·
              refine ⟨468988126318228360362547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625317501757637813816729 468988126318228360362547)
              ·
                refine ⟨703482189477342540543821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468988126318228360362547 703482189477342540543821)
                ·
                  refine ⟨263805821054003452703933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703482189477342540543821 263805821054003452703933)
                  ·
                    rfl

theorem cell20_577980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_577980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577980 prefixEnd_577980 := by exact prefixLift 577980
  have htrace : WordTrace (prefixWord ++ tailWord_577980) baseStart_577980 baseEnd_577980 := by
    simpa [prefixWord, tailWord_577980, baseEnd_577980] using wordTrace_append hprefix tailTrace_577980
  have hstable : (prefixWord ++ tailWord_577980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577980).length < 2 ^ (prefixWord ++ tailWord_577980).sum := by decide
  have hdescent : baseEnd_577980 < baseStart_577980 := by decide
  rcases family_descends (prefixWord ++ tailWord_577980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578019 : List Nat := [1, 1, 1, 6, 11]
def baseStart_578019 : Nat := 118140960795 + 578019 * 2 ^ 59
def prefixEnd_578019 : Nat := 4983230072969 + 3 ^ 40 * 578019 * 2
def baseEnd_578019 : Nat := 3257081749588798153133

theorem tailTrace_578019 : CollatzResearch.WordTrace tailWord_578019 prefixEnd_578019 3257081749588798153133 := by
  unfold tailWord_578019
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082084892943355630985111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14054723261962237087323407 21082084892943355630985111)
  ·
    refine ⟨31623127339415033446477667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21082084892943355630985111 31623127339415033446477667)
    ·
      refine ⟨47434691009122550169716501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31623127339415033446477667 47434691009122550169716501)
      ·
        refine ⟨2223501141052619539205461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47434691009122550169716501 2223501141052619539205461)
        ·
          refine ⟨3257081749588798153133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2223501141052619539205461 3257081749588798153133)
          ·
            rfl

theorem cell20_578019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 11].length) (baseStart_578019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578019 prefixEnd_578019 := by exact prefixLift 578019
  have htrace : WordTrace (prefixWord ++ tailWord_578019) baseStart_578019 baseEnd_578019 := by
    simpa [prefixWord, tailWord_578019, baseEnd_578019] using wordTrace_append hprefix tailTrace_578019
  have hstable : (prefixWord ++ tailWord_578019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578019).length < 2 ^ (prefixWord ++ tailWord_578019).sum := by decide
  have hdescent : baseEnd_578019 < baseStart_578019 := by decide
  rcases family_descends (prefixWord ++ tailWord_578019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578021 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 2]
def baseStart_578021 : Nat := 118140960795 + 578021 * 2 ^ 59
def prefixEnd_578021 : Nat := 4983230072969 + 3 ^ 40 * 578021 * 2
def baseEnd_578021 : Nat := 263824534571189532337099

theorem tailTrace_578021 : CollatzResearch.WordTrace tailWord_578021 prefixEnd_578021 263824534571189532337099 := by
  unfold tailWord_578021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082157838936109972557917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14054771892624073315038611 21082157838936109972557917)
  ·
    refine ⟨7905809189601041239709219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21082157838936109972557917 7905809189601041239709219)
    ·
      refine ⟨11858713784401561859563829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7905809189601041239709219 11858713784401561859563829)
      ·
        refine ⟨1111754417287646424334109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11858713784401561859563829 1111754417287646424334109)
        ·
          refine ⟨416907906482867409125291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1111754417287646424334109 416907906482867409125291)
          ·
            refine ⟨625361859724301113687937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416907906482867409125291 625361859724301113687937)
            ·
              refine ⟨469021394793225835265953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625361859724301113687937 469021394793225835265953)
              ·
                refine ⟨351766046094919376449465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469021394793225835265953 351766046094919376449465)
                ·
                  refine ⟨263824534571189532337099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351766046094919376449465 263824534571189532337099)
                  ·
                    rfl

theorem cell20_578021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_578021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578021 prefixEnd_578021 := by exact prefixLift 578021
  have htrace : WordTrace (prefixWord ++ tailWord_578021) baseStart_578021 baseEnd_578021 := by
    simpa [prefixWord, tailWord_578021, baseEnd_578021] using wordTrace_append hprefix tailTrace_578021
  have hstable : (prefixWord ++ tailWord_578021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578021).length < 2 ^ (prefixWord ++ tailWord_578021).sum := by decide
  have hdescent : baseEnd_578021 < baseStart_578021 := by decide
  rcases family_descends (prefixWord ++ tailWord_578021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578077 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 3]
def baseStart_578077 : Nat := 118140960795 + 578077 * 2 ^ 59
def prefixEnd_578077 : Nat := 4983230072969 + 3 ^ 40 * 578077 * 2
def baseEnd_578077 : Nat := 263850094497102226470203

theorem tailTrace_578077 : CollatzResearch.WordTrace tailWord_578077 prefixEnd_578077 263850094497102226470203 := by
  unfold tailWord_578077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21084200326733231536596485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14056133551155487691064323 21084200326733231536596485)
  ·
    refine ⟨3953287561262480913111841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21084200326733231536596485 3953287561262480913111841)
    ·
      refine ⟨2964965670946860684833881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3953287561262480913111841 2964965670946860684833881)
      ·
        refine ⟨2223724253210145513625411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2964965670946860684833881 2223724253210145513625411)
        ·
          refine ⟨3335586379815218270438117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2223724253210145513625411 3335586379815218270438117)
          ·
            refine ⟨625422446215353425707147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3335586379815218270438117 625422446215353425707147)
            ·
              refine ⟨938133669323030138560721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625422446215353425707147 938133669323030138560721)
              ·
                refine ⟨703600251992272603920541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938133669323030138560721 703600251992272603920541)
                ·
                  refine ⟨263850094497102226470203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703600251992272603920541 263850094497102226470203)
                  ·
                    rfl

theorem cell20_578077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_578077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578077 prefixEnd_578077 := by exact prefixLift 578077
  have htrace : WordTrace (prefixWord ++ tailWord_578077) baseStart_578077 baseEnd_578077 := by
    simpa [prefixWord, tailWord_578077, baseEnd_578077] using wordTrace_append hprefix tailTrace_578077
  have hstable : (prefixWord ++ tailWord_578077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578077).length < 2 ^ (prefixWord ++ tailWord_578077).sum := by decide
  have hdescent : baseEnd_578077 < baseStart_578077 := by decide
  rcases family_descends (prefixWord ++ tailWord_578077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578081 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_578081 : Nat := 118140960795 + 578081 * 2 ^ 59
def prefixEnd_578081 : Nat := 4983230072969 + 3 ^ 40 * 578081 * 2
def baseEnd_578081 : Nat := 263851920206095990336853

theorem tailTrace_578081 : CollatzResearch.WordTrace tailWord_578081 prefixEnd_578081 263851920206095990336853 := by
  unfold tailWord_578081
  simp only [CollatzResearch.WordTrace]
  refine ⟨21084346218718740219742097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14056230812479160146494731 21084346218718740219742097)
  ·
    refine ⟨15813259664039055164806573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21084346218718740219742097 15813259664039055164806573)
    ·
      refine ⟨5929972374014645686802465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15813259664039055164806573 5929972374014645686802465)
      ·
        refine ⟨4447479280510984265101849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5929972374014645686802465 4447479280510984265101849)
        ·
          refine ⟨3335609460383238198826387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447479280510984265101849 3335609460383238198826387)
          ·
            refine ⟨5003414190574857298239581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335609460383238198826387 5003414190574857298239581)
            ·
              refine ⟨1876280321465571486839843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5003414190574857298239581 1876280321465571486839843)
              ·
                refine ⟨2814420482198357230259765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876280321465571486839843 2814420482198357230259765)
                ·
                  refine ⟨263851920206095990336853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2814420482198357230259765 263851920206095990336853)
                  ·
                    rfl

theorem cell20_578081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_578081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578081 prefixEnd_578081 := by exact prefixLift 578081
  have htrace : WordTrace (prefixWord ++ tailWord_578081) baseStart_578081 baseEnd_578081 := by
    simpa [prefixWord, tailWord_578081, baseEnd_578081] using wordTrace_append hprefix tailTrace_578081
  have hstable : (prefixWord ++ tailWord_578081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578081).length < 2 ^ (prefixWord ++ tailWord_578081).sum := by decide
  have hdescent : baseEnd_578081 < baseStart_578081 := by decide
  rcases family_descends (prefixWord ++ tailWord_578081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578094 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_578094 : Nat := 118140960795 + 578094 * 2 ^ 59
def prefixEnd_578094 : Nat := 4983230072969 + 3 ^ 40 * 578094 * 2
def baseEnd_578094 : Nat := 263857853760325722903467

theorem tailTrace_578094 : CollatzResearch.WordTrace tailWord_578094 prefixEnd_578094 263857853760325722903467 := by
  unfold tailWord_578094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635602545958955429995667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14056546911781095626643557 2635602545958955429995667)
  ·
    refine ⟨3953403818938433144993501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635602545958955429995667 3953403818938433144993501)
    ·
      refine ⟨1482526432101912429372563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3953403818938433144993501 1482526432101912429372563)
      ·
        refine ⟨2223789648152868644058845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482526432101912429372563 2223789648152868644058845)
        ·
          refine ⟨833921118057325741522067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2223789648152868644058845 833921118057325741522067)
          ·
            refine ⟨1250881677085988612283101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833921118057325741522067 1250881677085988612283101)
            ·
              refine ⟨469080628907245729606163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250881677085988612283101 469080628907245729606163)
              ·
                refine ⟨703620943360868594409245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469080628907245729606163 703620943360868594409245)
                ·
                  refine ⟨263857853760325722903467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703620943360868594409245 263857853760325722903467)
                  ·
                    rfl

theorem cell20_578094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_578094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578094 prefixEnd_578094 := by exact prefixLift 578094
  have htrace : WordTrace (prefixWord ++ tailWord_578094) baseStart_578094 baseEnd_578094 := by
    simpa [prefixWord, tailWord_578094, baseEnd_578094] using wordTrace_append hprefix tailTrace_578094
  have hstable : (prefixWord ++ tailWord_578094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578094).length < 2 ^ (prefixWord ++ tailWord_578094).sum := by decide
  have hdescent : baseEnd_578094 < baseStart_578094 := by decide
  rcases family_descends (prefixWord ++ tailWord_578094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578112 : List Nat := [2, 1, 1, 2, 2, 2, 6, 4]
def baseStart_578112 : Nat := 118140960795 + 578112 * 2 ^ 59
def prefixEnd_578112 : Nat := 4983230072969 + 3 ^ 40 * 578112 * 2
def baseEnd_578112 : Nat := 87955356483599220101131

theorem tailTrace_578112 : CollatzResearch.WordTrace tailWord_578112 prefixEnd_578112 87955356483599220101131 := by
  unfold tailWord_578112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10542738440803216257060295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14056984587737621676080393 10542738440803216257060295)
  ·
    refine ⟨15814107661204824385590443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10542738440803216257060295 15814107661204824385590443)
    ·
      refine ⟨23721161491807236578385665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15814107661204824385590443 23721161491807236578385665)
      ·
        refine ⟨17790871118855427433789249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23721161491807236578385665 17790871118855427433789249)
        ·
          refine ⟨13343153339141570575341937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17790871118855427433789249 13343153339141570575341937)
          ·
            refine ⟨10007365004356177931506453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13343153339141570575341937 10007365004356177931506453)
            ·
              refine ⟨469095234579195840539365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10007365004356177931506453 469095234579195840539365)
              ·
                refine ⟨87955356483599220101131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469095234579195840539365 87955356483599220101131)
                ·
                  rfl

theorem cell20_578112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_578112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578112 prefixEnd_578112 := by exact prefixLift 578112
  have htrace : WordTrace (prefixWord ++ tailWord_578112) baseStart_578112 baseEnd_578112 := by
    simpa [prefixWord, tailWord_578112, baseEnd_578112] using wordTrace_append hprefix tailTrace_578112
  have hstable : (prefixWord ++ tailWord_578112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578112).length < 2 ^ (prefixWord ++ tailWord_578112).sum := by decide
  have hdescent : baseEnd_578112 < baseStart_578112 := by decide
  rcases family_descends (prefixWord ++ tailWord_578112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578118 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_578118 : Nat := 118140960795 + 578118 * 2 ^ 59
def prefixEnd_578118 : Nat := 4983230072969 + 3 ^ 40 * 578118 * 2
def baseEnd_578118 : Nat := 263868808014288306103369

theorem tailTrace_578118 : CollatzResearch.WordTrace tailWord_578118 prefixEnd_578118 263868808014288306103369 := by
  unfold tailWord_578118
  simp only [CollatzResearch.WordTrace]
  refine ⟨658927991237021735588719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14057130479723130359226005 658927991237021735588719)
  ·
    refine ⟨988391986855532603383079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 658927991237021735588719 988391986855532603383079)
    ·
      refine ⟨1482587980283298905074619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988391986855532603383079 1482587980283298905074619)
      ·
        refine ⟨2223881970424948357611929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482587980283298905074619 2223881970424948357611929)
        ·
          refine ⟨1667911477818711268208947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2223881970424948357611929 1667911477818711268208947)
          ·
            refine ⟨2501867216728066902313421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667911477818711268208947 2501867216728066902313421)
            ·
              refine ⟨938200206273025088367533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2501867216728066902313421 938200206273025088367533)
              ·
                refine ⟨351825077352384408137825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938200206273025088367533 351825077352384408137825)
                ·
                  refine ⟨263868808014288306103369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351825077352384408137825 263868808014288306103369)
                  ·
                    rfl

theorem cell20_578118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_578118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578118 prefixEnd_578118 := by exact prefixLift 578118
  have htrace : WordTrace (prefixWord ++ tailWord_578118) baseStart_578118 baseEnd_578118 := by
    simpa [prefixWord, tailWord_578118, baseEnd_578118] using wordTrace_append hprefix tailTrace_578118
  have hstable : (prefixWord ++ tailWord_578118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578118).length < 2 ^ (prefixWord ++ tailWord_578118).sum := by decide
  have hdescent : baseEnd_578118 < baseStart_578118 := by decide
  rcases family_descends (prefixWord ++ tailWord_578118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578119 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_578119 : Nat := 118140960795 + 578119 * 2 ^ 59
def prefixEnd_578119 : Nat := 4983230072969 + 3 ^ 40 * 578119 * 2
def baseEnd_578119 : Nat := 263869264441536747070031

theorem tailTrace_578119 : CollatzResearch.WordTrace tailWord_578119 prefixEnd_578119 263869264441536747070031 := by
  unfold tailWord_578119
  simp only [CollatzResearch.WordTrace]
  refine ⟨21085732192581072709625411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14057154795054048473083607 21085732192581072709625411)
  ·
    refine ⟨31628598288871609064438117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21085732192581072709625411 31628598288871609064438117)
    ·
      refine ⟨5930362179163426699582147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31628598288871609064438117 5930362179163426699582147)
      ·
        refine ⟨8895543268745140049373221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930362179163426699582147 8895543268745140049373221)
        ·
          refine ⟨1667914362889713759257479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8895543268745140049373221 1667914362889713759257479)
          ·
            refine ⟨2501871544334570638886219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667914362889713759257479 2501871544334570638886219)
            ·
              refine ⟨3752807316501855958329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501871544334570638886219 3752807316501855958329329)
              ·
                refine ⟨2814605487376391968746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3752807316501855958329329 2814605487376391968746997)
                ·
                  refine ⟨263869264441536747070031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2814605487376391968746997 263869264441536747070031)
                  ·
                    rfl

theorem cell20_578119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_578119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578119 prefixEnd_578119 := by exact prefixLift 578119
  have htrace : WordTrace (prefixWord ++ tailWord_578119) baseStart_578119 baseEnd_578119 := by
    simpa [prefixWord, tailWord_578119, baseEnd_578119] using wordTrace_append hprefix tailTrace_578119
  have hstable : (prefixWord ++ tailWord_578119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578119).length < 2 ^ (prefixWord ++ tailWord_578119).sum := by decide
  have hdescent : baseEnd_578119 < baseStart_578119 := by decide
  rcases family_descends (prefixWord ++ tailWord_578119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578122 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_578122 : Nat := 118140960795 + 578122 * 2 ^ 59
def prefixEnd_578122 : Nat := 4983230072969 + 3 ^ 40 * 578122 * 2
def baseEnd_578122 : Nat := 263870633723282069970019

theorem tailTrace_578122 : CollatzResearch.WordTrace tailWord_578122 prefixEnd_578122 263870633723282069970019 := by
  unfold tailWord_578122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271460402892551055496155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14057227741046802814656413 5271460402892551055496155)
  ·
    refine ⟨7907190604338826583244233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5271460402892551055496155 7907190604338826583244233)
    ·
      refine ⟨5930392953254119937433175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7907190604338826583244233 5930392953254119937433175)
      ·
        refine ⟨8895589429881179906149763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930392953254119937433175 8895589429881179906149763)
        ·
          refine ⟨13343384144821769859224645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8895589429881179906149763 13343384144821769859224645)
          ·
            refine ⟨2501884527154081848604621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13343384144821769859224645 2501884527154081848604621)
            ·
              refine ⟨938206697682780693226733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2501884527154081848604621 938206697682780693226733)
              ·
                refine ⟨351827511631042759960025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938206697682780693226733 351827511631042759960025)
                ·
                  refine ⟨263870633723282069970019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351827511631042759960025 263870633723282069970019)
                  ·
                    rfl

theorem cell20_578122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_578122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578122 prefixEnd_578122 := by exact prefixLift 578122
  have htrace : WordTrace (prefixWord ++ tailWord_578122) baseStart_578122 baseEnd_578122 := by
    simpa [prefixWord, tailWord_578122, baseEnd_578122] using wordTrace_append hprefix tailTrace_578122
  have hstable : (prefixWord ++ tailWord_578122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578122).length < 2 ^ (prefixWord ++ tailWord_578122).sum := by decide
  have hdescent : baseEnd_578122 < baseStart_578122 := by decide
  rcases family_descends (prefixWord ++ tailWord_578122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578126 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_578126 : Nat := 118140960795 + 578126 * 2 ^ 59
def prefixEnd_578126 : Nat := 4983230072969 + 3 ^ 40 * 578126 * 2
def baseEnd_578126 : Nat := 263872459432275833836669

theorem tailTrace_578126 : CollatzResearch.WordTrace tailWord_578126 prefixEnd_578126 263872459432275833836669 := by
  unfold tailWord_578126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635748437944464113141279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14057325002370475270086821 2635748437944464113141279)
  ·
    refine ⟨3953622656916696169711919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635748437944464113141279 3953622656916696169711919)
    ·
      refine ⟨5930433985375044254567879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953622656916696169711919 5930433985375044254567879)
      ·
        refine ⟨8895650978062566381851819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930433985375044254567879 8895650978062566381851819)
        ·
          refine ⟨13343476467093849572777729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8895650978062566381851819 13343476467093849572777729)
          ·
            refine ⟨10007607350320387179583297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13343476467093849572777729 10007607350320387179583297)
            ·
              refine ⟨7505705512740290384687473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10007607350320387179583297 7505705512740290384687473)
              ·
                refine ⟨5629279134555217788515605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7505705512740290384687473 5629279134555217788515605)
                ·
                  refine ⟨263872459432275833836669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5629279134555217788515605 263872459432275833836669)
                  ·
                    rfl

theorem cell20_578126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_578126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578126 prefixEnd_578126 := by exact prefixLift 578126
  have htrace : WordTrace (prefixWord ++ tailWord_578126) baseStart_578126 baseEnd_578126 := by
    simpa [prefixWord, tailWord_578126, baseEnd_578126] using wordTrace_append hprefix tailTrace_578126
  have hstable : (prefixWord ++ tailWord_578126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578126).length < 2 ^ (prefixWord ++ tailWord_578126).sum := by decide
  have hdescent : baseEnd_578126 < baseStart_578126 := by decide
  rcases family_descends (prefixWord ++ tailWord_578126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578133 : List Nat := [1, 3, 2, 2, 1, 1, 10]
def baseStart_578133 : Nat := 118140960795 + 578133 * 2 ^ 59
def prefixEnd_578133 : Nat := 4983230072969 + 3 ^ 40 * 578133 * 2
def baseEnd_578133 : Nat := 29319517158112768955923

theorem tailTrace_578133 : CollatzResearch.WordTrace tailWord_578133 prefixEnd_578133 29319517158112768955923 := by
  unfold tailWord_578133
  simp only [CollatzResearch.WordTrace]
  refine ⟨21086242814530353100635053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14057495209686902067090035 21086242814530353100635053)
  ·
    refine ⟨7907341055448882412738145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21086242814530353100635053 7907341055448882412738145)
    ·
      refine ⟨5930505791586661809553609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7907341055448882412738145 5930505791586661809553609)
      ·
        refine ⟨4447879343689996357165207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5930505791586661809553609 4447879343689996357165207)
        ·
          refine ⟨6671819015534994535747811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447879343689996357165207 6671819015534994535747811)
          ·
            refine ⟨10007728523302491803621717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6671819015534994535747811 10007728523302491803621717)
            ·
              refine ⟨29319517158112768955923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10007728523302491803621717 29319517158112768955923)
              ·
                rfl

theorem cell20_578133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_578133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578133 prefixEnd_578133 := by exact prefixLift 578133
  have htrace : WordTrace (prefixWord ++ tailWord_578133) baseStart_578133 baseEnd_578133 := by
    simpa [prefixWord, tailWord_578133, baseEnd_578133] using wordTrace_append hprefix tailTrace_578133
  have hstable : (prefixWord ++ tailWord_578133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578133).length < 2 ^ (prefixWord ++ tailWord_578133).sum := by decide
  have hdescent : baseEnd_578133 < baseStart_578133 := by decide
  rcases family_descends (prefixWord ++ tailWord_578133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578143 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 2]
def baseStart_578143 : Nat := 118140960795 + 578143 * 2 ^ 59
def prefixEnd_578143 : Nat := 4983230072969 + 3 ^ 40 * 578143 * 2
def baseEnd_578143 : Nat := 263880218695499330269933

theorem tailTrace_578143 : CollatzResearch.WordTrace tailWord_578143 prefixEnd_578143 263880218695499330269933 := by
  unfold tailWord_578143
  simp only [CollatzResearch.WordTrace]
  refine ⟨21086607544494124808499083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14057738362996083205666055 21086607544494124808499083)
  ·
    refine ⟨31629911316741187212748625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21086607544494124808499083 31629911316741187212748625)
    ·
      refine ⟨23722433487555890409561469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31629911316741187212748625 23722433487555890409561469)
      ·
        refine ⟨8895912557833458903585551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23722433487555890409561469 8895912557833458903585551)
        ·
          refine ⟨13343868836750188355378327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8895912557833458903585551 13343868836750188355378327)
          ·
            refine ⟨20015803255125282533067491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13343868836750188355378327 20015803255125282533067491)
            ·
              refine ⟨30023704882687923799601237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20015803255125282533067491 30023704882687923799601237)
              ·
                refine ⟨351840291593999107026577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30023704882687923799601237 351840291593999107026577)
                ·
                  refine ⟨263880218695499330269933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351840291593999107026577 263880218695499330269933)
                  ·
                    rfl

theorem cell20_578143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 2].length) (baseStart_578143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578143 prefixEnd_578143 := by exact prefixLift 578143
  have htrace : WordTrace (prefixWord ++ tailWord_578143) baseStart_578143 baseEnd_578143 := by
    simpa [prefixWord, tailWord_578143, baseEnd_578143] using wordTrace_append hprefix tailTrace_578143
  have hstable : (prefixWord ++ tailWord_578143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578143).length < 2 ^ (prefixWord ++ tailWord_578143).sum := by decide
  have hdescent : baseEnd_578143 < baseStart_578143 := by decide
  rcases family_descends (prefixWord ++ tailWord_578143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578146 : List Nat := [3, 3, 2, 3, 1, 1, 2, 5]
def baseStart_578146 : Nat := 118140960795 + 578146 * 2 ^ 59
def prefixEnd_578146 : Nat := 4983230072969 + 3 ^ 40 * 578146 * 2
def baseEnd_578146 : Nat := 87960529325748217723307

theorem tailTrace_578146 : CollatzResearch.WordTrace tailWord_578146 prefixEnd_578146 87960529325748217723307 := by
  unfold tailWord_578146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271679240870814080214573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14057811308988837547238861 5271679240870814080214573)
  ·
    refine ⟨1976879715326555280080465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5271679240870814080214573 1976879715326555280080465)
    ·
      refine ⟨1482659786494916460060349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1976879715326555280080465 1482659786494916460060349)
      ·
        refine ⟨555997419935593672522631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1482659786494916460060349 555997419935593672522631)
        ·
          refine ⟨833996129903390508783947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555997419935593672522631 833996129903390508783947)
          ·
            refine ⟨1250994194855085763175921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833996129903390508783947 1250994194855085763175921)
            ·
              refine ⟨938245646141314322381941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250994194855085763175921 938245646141314322381941)
              ·
                refine ⟨87960529325748217723307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 938245646141314322381941 87960529325748217723307)
                ·
                  rfl

theorem cell20_578146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_578146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578146 prefixEnd_578146 := by exact prefixLift 578146
  have htrace : WordTrace (prefixWord ++ tailWord_578146) baseStart_578146 baseEnd_578146 := by
    simpa [prefixWord, tailWord_578146, baseEnd_578146] using wordTrace_append hprefix tailTrace_578146
  have hstable : (prefixWord ++ tailWord_578146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578146).length < 2 ^ (prefixWord ++ tailWord_578146).sum := by decide
  have hdescent : baseEnd_578146 < baseStart_578146 := by decide
  rcases family_descends (prefixWord ++ tailWord_578146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578194 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_578194 : Nat := 118140960795 + 578194 * 2 ^ 59
def prefixEnd_578194 : Nat := 4983230072969 + 3 ^ 40 * 578194 * 2
def baseEnd_578194 : Nat := 263903496485169819569725

theorem tailTrace_578194 : CollatzResearch.WordTrace tailWord_578194 prefixEnd_578194 263903496485169819569725 := by
  unfold tailWord_578194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272116916827340129651409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14058978444872907012403757 5272116916827340129651409)
  ·
    refine ⟨3954087687620505097238557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5272116916827340129651409 3954087687620505097238557)
    ·
      refine ⟨1482782882857689411464459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3954087687620505097238557 1482782882857689411464459)
      ·
        refine ⟨2224174324286534117196689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482782882857689411464459 2224174324286534117196689)
        ·
          refine ⟨1668130743214900587897517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224174324286534117196689 1668130743214900587897517)
          ·
            refine ⟨625549028705587720461569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1668130743214900587897517 625549028705587720461569)
            ·
              refine ⟨469161771529190790346177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625549028705587720461569 469161771529190790346177)
              ·
                refine ⟨351871328646893092759633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469161771529190790346177 351871328646893092759633)
                ·
                  refine ⟨263903496485169819569725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351871328646893092759633 263903496485169819569725)
                  ·
                    rfl

theorem cell20_578194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_578194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578194 prefixEnd_578194 := by exact prefixLift 578194
  have htrace : WordTrace (prefixWord ++ tailWord_578194) baseStart_578194 baseEnd_578194 := by
    simpa [prefixWord, tailWord_578194, baseEnd_578194] using wordTrace_append hprefix tailTrace_578194
  have hstable : (prefixWord ++ tailWord_578194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578194).length < 2 ^ (prefixWord ++ tailWord_578194).sum := by decide
  have hdescent : baseEnd_578194 < baseStart_578194 := by decide
  rcases family_descends (prefixWord ++ tailWord_578194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578222 : List Nat := [4, 1, 4, 1, 1, 2, 3, 4]
def baseStart_578222 : Nat := 118140960795 + 578222 * 2 ^ 59
def prefixEnd_578222 : Nat := 4983230072969 + 3 ^ 40 * 578222 * 2
def baseEnd_578222 : Nat := 87972092149375388878759

theorem tailTrace_578222 : CollatzResearch.WordTrace tailWord_578222 prefixEnd_578222 87972092149375388878759 := by
  unfold tailWord_578222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636186113900990162578115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14059659274138614200416613 2636186113900990162578115)
  ·
    refine ⟨3954279170851485243867173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2636186113900990162578115 3954279170851485243867173)
    ·
      refine ⟨741427344534653483225095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3954279170851485243867173 741427344534653483225095)
      ·
        refine ⟨1112141016801980224837643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741427344534653483225095 1112141016801980224837643)
        ·
          refine ⟨1668211525202970337256465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112141016801980224837643 1668211525202970337256465)
          ·
            refine ⟨1251158643902227752942349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1668211525202970337256465 1251158643902227752942349)
            ·
              refine ⟨469184491463335407353381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251158643902227752942349 469184491463335407353381)
              ·
                refine ⟨87972092149375388878759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469184491463335407353381 87972092149375388878759)
                ·
                  rfl

theorem cell20_578222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_578222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578222 prefixEnd_578222 := by exact prefixLift 578222
  have htrace : WordTrace (prefixWord ++ tailWord_578222) baseStart_578222 baseEnd_578222 := by
    simpa [prefixWord, tailWord_578222, baseEnd_578222] using wordTrace_append hprefix tailTrace_578222
  have hstable : (prefixWord ++ tailWord_578222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578222).length < 2 ^ (prefixWord ++ tailWord_578222).sum := by decide
  have hdescent : baseEnd_578222 < baseStart_578222 := by decide
  rcases family_descends (prefixWord ++ tailWord_578222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578236 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 2]
def baseStart_578236 : Nat := 118140960795 + 578236 * 2 ^ 59
def prefixEnd_578236 : Nat := 4983230072969 + 3 ^ 40 * 578236 * 2
def baseEnd_578236 : Nat := 263922666429604340169553

theorem tailTrace_578236 : CollatzResearch.WordTrace tailWord_578236 prefixEnd_578236 263922666429604340169553 := by
  unfold tailWord_578236
  simp only [CollatzResearch.WordTrace]
  refine ⟨10544999766578600845817281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14059999688771467794423041 10544999766578600845817281)
  ·
    refine ⟨7908749824933950634362961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10544999766578600845817281 7908749824933950634362961)
    ·
      refine ⟨5931562368700462975772221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7908749824933950634362961 5931562368700462975772221)
      ·
        refine ⟨2224335888262673615914583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5931562368700462975772221 2224335888262673615914583)
        ·
          refine ⟨3336503832394010423871875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224335888262673615914583 3336503832394010423871875)
          ·
            refine ⟨5004755748591015635807813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336503832394010423871875 5004755748591015635807813)
            ·
              refine ⟨938391702860815431713965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5004755748591015635807813 938391702860815431713965)
              ·
                refine ⟨351896888572805786892737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938391702860815431713965 351896888572805786892737)
                ·
                  refine ⟨263922666429604340169553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351896888572805786892737 263922666429604340169553)
                  ·
                    rfl

theorem cell20_578236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_578236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578236 prefixEnd_578236 := by exact prefixLift 578236
  have htrace : WordTrace (prefixWord ++ tailWord_578236) baseStart_578236 baseEnd_578236 := by
    simpa [prefixWord, tailWord_578236, baseEnd_578236] using wordTrace_append hprefix tailTrace_578236
  have hstable : (prefixWord ++ tailWord_578236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578236).length < 2 ^ (prefixWord ++ tailWord_578236).sum := by decide
  have hdescent : baseEnd_578236 < baseStart_578236 := by decide
  rcases family_descends (prefixWord ++ tailWord_578236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578246 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_578246 : Nat := 118140960795 + 578246 * 2 ^ 59
def prefixEnd_578246 : Nat := 4983230072969 + 3 ^ 40 * 578246 * 2
def baseEnd_578246 : Nat := 263927230702088749836179

theorem tailTrace_578246 : CollatzResearch.WordTrace tailWord_578246 prefixEnd_578246 263927230702088749836179 := by
  unfold tailWord_578246
  simp only [CollatzResearch.WordTrace]
  refine ⟨659073883222530418734331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14060242842080648932999061 659073883222530418734331)
  ·
    refine ⟨988610824833795628101497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659073883222530418734331 988610824833795628101497)
    ·
      refine ⟨741458118625346721076123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 988610824833795628101497 741458118625346721076123)
      ·
        refine ⟨1112187177938020081614185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741458118625346721076123 1112187177938020081614185)
        ·
          refine ⟨834140383453515061210639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1112187177938020081614185 834140383453515061210639)
          ·
            refine ⟨1251210575180272591815959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834140383453515061210639 1251210575180272591815959)
            ·
              refine ⟨1876815862770408887723939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251210575180272591815959 1876815862770408887723939)
              ·
                refine ⟨2815223794155613331585909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876815862770408887723939 2815223794155613331585909)
                ·
                  refine ⟨263927230702088749836179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2815223794155613331585909 263927230702088749836179)
                  ·
                    rfl

theorem cell20_578246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_578246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578246 prefixEnd_578246 := by exact prefixLift 578246
  have htrace : WordTrace (prefixWord ++ tailWord_578246) baseStart_578246 baseEnd_578246 := by
    simpa [prefixWord, tailWord_578246, baseEnd_578246] using wordTrace_append hprefix tailTrace_578246
  have hstable : (prefixWord ++ tailWord_578246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578246).length < 2 ^ (prefixWord ++ tailWord_578246).sum := by decide
  have hdescent : baseEnd_578246 < baseStart_578246 := by decide
  rcases family_descends (prefixWord ++ tailWord_578246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578250 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_578250 : Nat := 118140960795 + 578250 * 2 ^ 59
def prefixEnd_578250 : Nat := 4983230072969 + 3 ^ 40 * 578250 * 2
def baseEnd_578250 : Nat := 263929056411082513702829

theorem tailTrace_578250 : CollatzResearch.WordTrace tailWord_578250 prefixEnd_578250 263929056411082513702829 := by
  unfold tailWord_578250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272627538776620520661051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14060340103404321388429469 5272627538776620520661051)
  ·
    refine ⟨7908941308164930780991577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5272627538776620520661051 7908941308164930780991577)
    ·
      refine ⟨5931705981123698085743683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7908941308164930780991577 5931705981123698085743683)
      ·
        refine ⟨8897558971685547128615525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5931705981123698085743683 8897558971685547128615525)
        ·
          refine ⟨1668292307191040086615411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8897558971685547128615525 1668292307191040086615411)
          ·
            refine ⟨2502438460786560129923117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668292307191040086615411 2502438460786560129923117)
            ·
              refine ⟨938414422794960048721169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2502438460786560129923117 938414422794960048721169)
              ·
                refine ⟨703810817096220036540877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938414422794960048721169 703810817096220036540877)
                ·
                  refine ⟨263929056411082513702829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703810817096220036540877 263929056411082513702829)
                  ·
                    rfl

theorem cell20_578250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_578250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578250 prefixEnd_578250 := by exact prefixLift 578250
  have htrace : WordTrace (prefixWord ++ tailWord_578250) baseStart_578250 baseEnd_578250 := by
    simpa [prefixWord, tailWord_578250, baseEnd_578250] using wordTrace_append hprefix tailTrace_578250
  have hstable : (prefixWord ++ tailWord_578250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578250).length < 2 ^ (prefixWord ++ tailWord_578250).sum := by decide
  have hdescent : baseEnd_578250 < baseStart_578250 := by decide
  rcases family_descends (prefixWord ++ tailWord_578250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578253 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_578253 : Nat := 118140960795 + 578253 * 2 ^ 59
def prefixEnd_578253 : Nat := 4983230072969 + 3 ^ 40 * 578253 * 2
def baseEnd_578253 : Nat := 263930425692827836602817

theorem tailTrace_578253 : CollatzResearch.WordTrace tailWord_578253 prefixEnd_578253 263930425692827836602817 := by
  unfold tailWord_578253
  simp only [CollatzResearch.WordTrace]
  refine ⟨21090619574095613595003413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14060413049397075730002275 21090619574095613595003413)
  ·
    refine ⟨988622792535731887265785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21090619574095613595003413 988622792535731887265785)
    ·
      refine ⟨741467094401798915449339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 988622792535731887265785 741467094401798915449339)
      ·
        refine ⟨1112200641602698373174009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741467094401798915449339 1112200641602698373174009)
        ·
          refine ⟨834150481202023779880507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1112200641602698373174009 834150481202023779880507)
          ·
            refine ⟨1251225721803035669820761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834150481202023779880507 1251225721803035669820761)
            ·
              refine ⟨938419291352276752365571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251225721803035669820761 938419291352276752365571)
              ·
                refine ⟨1407628937028415128548357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938419291352276752365571 1407628937028415128548357)
                ·
                  refine ⟨263930425692827836602817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407628937028415128548357 263930425692827836602817)
                  ·
                    rfl

theorem cell20_578253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_578253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578253 prefixEnd_578253 := by exact prefixLift 578253
  have htrace : WordTrace (prefixWord ++ tailWord_578253) baseStart_578253 baseEnd_578253 := by
    simpa [prefixWord, tailWord_578253, baseEnd_578253] using wordTrace_append hprefix tailTrace_578253
  have hstable : (prefixWord ++ tailWord_578253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578253).length < 2 ^ (prefixWord ++ tailWord_578253).sum := by decide
  have hdescent : baseEnd_578253 < baseStart_578253 := by decide
  rcases family_descends (prefixWord ++ tailWord_578253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578257 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 2]
def baseStart_578257 : Nat := 118140960795 + 578257 * 2 ^ 59
def prefixEnd_578257 : Nat := 4983230072969 + 3 ^ 40 * 578257 * 2
def baseEnd_578257 : Nat := 263932251401821600469467

theorem tailTrace_578257 : CollatzResearch.WordTrace tailWord_578257 prefixEnd_578257 263932251401821600469467 := by
  unfold tailWord_578257
  simp only [CollatzResearch.WordTrace]
  refine ⟨21090765466081122278149025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14060510310720748185432683 21090765466081122278149025)
  ·
    refine ⟨15818074099560841708611769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21090765466081122278149025 15818074099560841708611769)
    ·
      refine ⟨11863555574670631281458827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15818074099560841708611769 11863555574670631281458827)
      ·
        refine ⟨17795333362005946922188241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11863555574670631281458827 17795333362005946922188241)
        ·
          refine ⟨13346500021504460191641181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17795333362005946922188241 13346500021504460191641181)
          ·
            refine ⟨5004937508064172571865443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13346500021504460191641181 5004937508064172571865443)
            ·
              refine ⟨7507406262096258857798165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004937508064172571865443 7507406262096258857798165)
              ·
                refine ⟨351909668535762133959289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7507406262096258857798165 351909668535762133959289)
                ·
                  refine ⟨263932251401821600469467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351909668535762133959289 263932251401821600469467)
                  ·
                    rfl

theorem cell20_578257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_578257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578257 prefixEnd_578257 := by exact prefixLift 578257
  have htrace : WordTrace (prefixWord ++ tailWord_578257) baseStart_578257 baseEnd_578257 := by
    simpa [prefixWord, tailWord_578257, baseEnd_578257] using wordTrace_append hprefix tailTrace_578257
  have hstable : (prefixWord ++ tailWord_578257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578257).length < 2 ^ (prefixWord ++ tailWord_578257).sum := by decide
  have hdescent : baseEnd_578257 < baseStart_578257 := by decide
  rcases family_descends (prefixWord ++ tailWord_578257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578302 : List Nat := [4, 2, 2, 1, 2, 1, 8]
def baseStart_578302 : Nat := 118140960795 + 578302 * 2 ^ 59
def prefixEnd_578302 : Nat := 4983230072969 + 3 ^ 40 * 578302 * 2
def baseEnd_578302 : Nat := 29328087847555715996587

theorem tailTrace_578302 : CollatzResearch.WordTrace tailWord_578302 prefixEnd_578302 29328087847555715996587 := by
  unfold tailWord_578302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636550843864761870442145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14061604500612063309024773 2636550843864761870442145)
  ·
    refine ⟨1977413132898571402831609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2636550843864761870442145 1977413132898571402831609)
    ·
      refine ⟨1483059849673928552123707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1977413132898571402831609 1483059849673928552123707)
      ·
        refine ⟨2224589774510892828185561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483059849673928552123707 2224589774510892828185561)
        ·
          refine ⟨1668442330883169621139171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224589774510892828185561 1668442330883169621139171)
          ·
            refine ⟨2502663496324754431708757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668442330883169621139171 2502663496324754431708757)
            ·
              refine ⟨29328087847555715996587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2502663496324754431708757 29328087847555715996587)
              ·
                rfl

theorem cell20_578302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_578302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578302 prefixEnd_578302 := by exact prefixLift 578302
  have htrace : WordTrace (prefixWord ++ tailWord_578302) baseStart_578302 baseEnd_578302 := by
    simpa [prefixWord, tailWord_578302, baseEnd_578302] using wordTrace_append hprefix tailTrace_578302
  have hstable : (prefixWord ++ tailWord_578302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578302).length < 2 ^ (prefixWord ++ tailWord_578302).sum := by decide
  have hdescent : baseEnd_578302 < baseStart_578302 := by decide
  rcases family_descends (prefixWord ++ tailWord_578302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578323 : List Nat := [1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_578323 : Nat := 118140960795 + 578323 * 2 ^ 59
def prefixEnd_578323 : Nat := 4983230072969 + 3 ^ 40 * 578323 * 2
def baseEnd_578323 : Nat := 87987458533406234756399

theorem tailTrace_578323 : CollatzResearch.WordTrace tailWord_578323 prefixEnd_578323 87987458533406234756399 := by
  unfold tailWord_578323
  simp only [CollatzResearch.WordTrace]
  refine ⟨21093172683842015550051623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14062115122561343700034415 21093172683842015550051623)
  ·
    refine ⟨31639759025763023325077435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21093172683842015550051623 31639759025763023325077435)
    ·
      refine ⟨47459638538644534987616153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31639759025763023325077435 47459638538644534987616153)
      ·
        refine ⟨35594728903983401240712115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47459638538644534987616153 35594728903983401240712115)
        ·
          refine ⟨53392093355975101861068173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35594728903983401240712115 53392093355975101861068173)
          ·
            refine ⟨20022035008490663197900565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53392093355975101861068173 20022035008490663197900565)
            ·
              refine ⟨938532891022999837401589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20022035008490663197900565 938532891022999837401589)
              ·
                refine ⟨87987458533406234756399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 938532891022999837401589 87987458533406234756399)
                ·
                  rfl

theorem cell20_578323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_578323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578323 prefixEnd_578323 := by exact prefixLift 578323
  have htrace : WordTrace (prefixWord ++ tailWord_578323) baseStart_578323 baseEnd_578323 := by
    simpa [prefixWord, tailWord_578323, baseEnd_578323] using wordTrace_append hprefix tailTrace_578323
  have hstable : (prefixWord ++ tailWord_578323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578323).length < 2 ^ (prefixWord ++ tailWord_578323).sum := by decide
  have hdescent : baseEnd_578323 < baseStart_578323 := by decide
  rcases family_descends (prefixWord ++ tailWord_578323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578367 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 2]
def baseStart_578367 : Nat := 118140960795 + 578367 * 2 ^ 59
def prefixEnd_578367 : Nat := 4983230072969 + 3 ^ 40 * 578367 * 2
def baseEnd_578367 : Nat := 263982458399150106802351

theorem tailTrace_578367 : CollatzResearch.WordTrace tailWord_578367 prefixEnd_578367 263982458399150106802351 := by
  unfold tailWord_578367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21094777495682611064653355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14063184997121740709768903 21094777495682611064653355)
  ·
    refine ⟨31642166243523916596980033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21094777495682611064653355 31642166243523916596980033)
    ·
      refine ⟨23731624682642937447735025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31642166243523916596980033 23731624682642937447735025)
      ·
        refine ⟨17798718511982203085801269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23731624682642937447735025 17798718511982203085801269)
        ·
          refine ⟨1668629860498331539293869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17798718511982203085801269 1668629860498331539293869)
          ·
            refine ⟨625736197686874327235201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1668629860498331539293869 625736197686874327235201)
            ·
              refine ⟨469302148265155745426401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625736197686874327235201 469302148265155745426401)
              ·
                refine ⟨351976611198866809069801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469302148265155745426401 351976611198866809069801)
                ·
                  refine ⟨263982458399150106802351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351976611198866809069801 263982458399150106802351)
                  ·
                    rfl

theorem cell20_578367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 2].length) (baseStart_578367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578367 prefixEnd_578367 := by exact prefixLift 578367
  have htrace : WordTrace (prefixWord ++ tailWord_578367) baseStart_578367 baseEnd_578367 := by
    simpa [prefixWord, tailWord_578367, baseEnd_578367] using wordTrace_append hprefix tailTrace_578367
  have hstable : (prefixWord ++ tailWord_578367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578367).length < 2 ^ (prefixWord ++ tailWord_578367).sum := by decide
  have hdescent : baseEnd_578367 < baseStart_578367 := by decide
  rcases family_descends (prefixWord ++ tailWord_578367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578368 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_578368 : Nat := 118140960795 + 578368 * 2 ^ 59
def prefixEnd_578368 : Nat := 4983230072969 + 3 ^ 40 * 578368 * 2
def baseEnd_578368 : Nat := 263982914826398547769013

theorem tailTrace_578368 : CollatzResearch.WordTrace tailWord_578368 prefixEnd_578368 263982914826398547769013 := by
  unfold tailWord_578368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547406984339494117719879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14063209312452658823626505 10547406984339494117719879)
  ·
    refine ⟨15821110476509241176579819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10547406984339494117719879 15821110476509241176579819)
    ·
      refine ⟨23731665714763861764869729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15821110476509241176579819 23731665714763861764869729)
      ·
        refine ⟨17798749286072896323652297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23731665714763861764869729 17798749286072896323652297)
        ·
          refine ⟨13349061964554672242739223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17798749286072896323652297 13349061964554672242739223)
          ·
            refine ⟨20023592946832008364108835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13349061964554672242739223 20023592946832008364108835)
            ·
              refine ⟨30035389420248012546163253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20023592946832008364108835 30035389420248012546163253)
              ·
                refine ⟨2815817758148251176202805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30035389420248012546163253 2815817758148251176202805)
                ·
                  refine ⟨263982914826398547769013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2815817758148251176202805 263982914826398547769013)
                  ·
                    rfl

theorem cell20_578368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_578368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578368 prefixEnd_578368 := by exact prefixLift 578368
  have htrace : WordTrace (prefixWord ++ tailWord_578368) baseStart_578368 baseEnd_578368 := by
    simpa [prefixWord, tailWord_578368, baseEnd_578368] using wordTrace_append hprefix tailTrace_578368
  have hstable : (prefixWord ++ tailWord_578368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578368).length < 2 ^ (prefixWord ++ tailWord_578368).sum := by decide
  have hdescent : baseEnd_578368 < baseStart_578368 := by decide
  rcases family_descends (prefixWord ++ tailWord_578368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578371 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 2]
def baseStart_578371 : Nat := 118140960795 + 578371 * 2 ^ 59
def prefixEnd_578371 : Nat := 4983230072969 + 3 ^ 40 * 578371 * 2
def baseEnd_578371 : Nat := 263984284108143870669001

theorem tailTrace_578371 : CollatzResearch.WordTrace tailWord_578371 prefixEnd_578371 263984284108143870669001 := by
  unfold tailWord_578371
  simp only [CollatzResearch.WordTrace]
  refine ⟨21094923387668119747798967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14063282258445413165199311 21094923387668119747798967)
  ·
    refine ⟨31642385081502179621698451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21094923387668119747798967 31642385081502179621698451)
    ·
      refine ⟨47463577622253269432547677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31642385081502179621698451 47463577622253269432547677)
      ·
        refine ⟨17798841608344976037205379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47463577622253269432547677 17798841608344976037205379)
        ·
          refine ⟨26698262412517464055808069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17798841608344976037205379 26698262412517464055808069)
          ·
            refine ⟨5005924202347024510464013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26698262412517464055808069 5005924202347024510464013)
            ·
              refine ⟨1877221575880134191424005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5005924202347024510464013 1877221575880134191424005)
              ·
                refine ⟨351979045477525160892001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1877221575880134191424005 351979045477525160892001)
                ·
                  refine ⟨263984284108143870669001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351979045477525160892001 263984284108143870669001)
                  ·
                    rfl

theorem cell20_578371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 2].length) (baseStart_578371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578371 prefixEnd_578371 := by exact prefixLift 578371
  have htrace : WordTrace (prefixWord ++ tailWord_578371) baseStart_578371 baseEnd_578371 := by
    simpa [prefixWord, tailWord_578371, baseEnd_578371] using wordTrace_append hprefix tailTrace_578371
  have hstable : (prefixWord ++ tailWord_578371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578371).length < 2 ^ (prefixWord ++ tailWord_578371).sum := by decide
  have hdescent : baseEnd_578371 < baseStart_578371 := by decide
  rcases family_descends (prefixWord ++ tailWord_578371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578450 : List Nat := [3, 2, 3, 2, 2, 2, 2, 4]
def baseStart_578450 : Nat := 118140960795 + 578450 * 2 ^ 59
def prefixEnd_578450 : Nat := 4983230072969 + 3 ^ 40 * 578450 * 2
def baseEnd_578450 : Nat := 88006780620256902345115

theorem tailTrace_578450 : CollatzResearch.WordTrace tailWord_578450 prefixEnd_578450 88006780620256902345115 := by
  unfold tailWord_578450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274451188595479059981201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14065203169587944159949869 5274451188595479059981201)
  ·
    refine ⟨3955838391446609294985901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5274451188595479059981201 3955838391446609294985901)
    ·
      refine ⟨1483439396792478485619713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3955838391446609294985901 1483439396792478485619713)
      ·
        refine ⟨1112579547594358864214785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1483439396792478485619713 1112579547594358864214785)
        ·
          refine ⟨834434660695769148161089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1112579547594358864214785 834434660695769148161089)
          ·
            refine ⟨625825995521826861120817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834434660695769148161089 625825995521826861120817)
            ·
              refine ⟨469369496641370145840613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625825995521826861120817 469369496641370145840613)
              ·
                refine ⟨88006780620256902345115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469369496641370145840613 88006780620256902345115)
                ·
                  rfl

theorem cell20_578450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_578450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578450 prefixEnd_578450 := by exact prefixLift 578450
  have htrace : WordTrace (prefixWord ++ tailWord_578450) baseStart_578450 baseEnd_578450 := by
    simpa [prefixWord, tailWord_578450, baseEnd_578450] using wordTrace_append hprefix tailTrace_578450
  have hstable : (prefixWord ++ tailWord_578450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578450).length < 2 ^ (prefixWord ++ tailWord_578450).sum := by decide
  have hdescent : baseEnd_578450 < baseStart_578450 := by decide
  rcases family_descends (prefixWord ++ tailWord_578450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578451 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_578451 : Nat := 118140960795 + 578451 * 2 ^ 59
def prefixEnd_578451 : Nat := 4983230072969 + 3 ^ 40 * 578451 * 2
def baseEnd_578451 : Nat := 264020798288019148002007

theorem tailTrace_578451 : CollatzResearch.WordTrace tailWord_578451 prefixEnd_578451 264020798288019148002007 := by
  unfold tailWord_578451
  simp only [CollatzResearch.WordTrace]
  refine ⟨21097841227378293410711207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14065227484918862273807471 21097841227378293410711207)
  ·
    refine ⟨31646761841067440116066811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21097841227378293410711207 31646761841067440116066811)
    ·
      refine ⟨47470142761601160174100217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31646761841067440116066811 47470142761601160174100217)
      ·
        refine ⟨35602607071200870130575163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47470142761601160174100217 35602607071200870130575163)
        ·
          refine ⟨53403910606801305195862745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35602607071200870130575163 53403910606801305195862745)
          ·
            refine ⟨40052932955100978896897059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53403910606801305195862745 40052932955100978896897059)
            ·
              refine ⟨60079399432651468345345589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40052932955100978896897059 60079399432651468345345589)
              ·
                refine ⟨5632443696811075157376149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60079399432651468345345589 5632443696811075157376149)
                ·
                  refine ⟨264020798288019148002007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5632443696811075157376149 264020798288019148002007)
                  ·
                    rfl

theorem cell20_578451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_578451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578451 prefixEnd_578451 := by exact prefixLift 578451
  have htrace : WordTrace (prefixWord ++ tailWord_578451) baseStart_578451 baseEnd_578451 := by
    simpa [prefixWord, tailWord_578451, baseEnd_578451] using wordTrace_append hprefix tailTrace_578451
  have hstable : (prefixWord ++ tailWord_578451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578451).length < 2 ^ (prefixWord ++ tailWord_578451).sum := by decide
  have hdescent : baseEnd_578451 < baseStart_578451 := by decide
  rcases family_descends (prefixWord ++ tailWord_578451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578460 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 2]
def baseStart_578460 : Nat := 118140960795 + 578460 * 2 ^ 59
def prefixEnd_578460 : Nat := 4983230072969 + 3 ^ 40 * 578460 * 2
def baseEnd_578460 : Nat := 264024906133255116701971

theorem tailTrace_578460 : CollatzResearch.WordTrace tailWord_578460 prefixEnd_578460 264024906133255116701971 := by
  unfold tailWord_578460
  simp only [CollatzResearch.WordTrace]
  refine ⟨10549084742172843973894417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14065446322897125298525889 10549084742172843973894417)
  ·
    refine ⟨7911813556629632980420813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10549084742172843973894417 7911813556629632980420813)
    ·
      refine ⟨2966930083736112367657805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7911813556629632980420813 2966930083736112367657805)
      ·
        refine ⟨1112598781401042137871677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2966930083736112367657805 1112598781401042137871677)
        ·
          refine ⟨417224543025390801701879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1112598781401042137871677 417224543025390801701879)
          ·
            refine ⟨625836814538086202552819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417224543025390801701879 625836814538086202552819)
            ·
              refine ⟨938755221807129303829229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625836814538086202552819 938755221807129303829229)
              ·
                refine ⟨352033208177673488935961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938755221807129303829229 352033208177673488935961)
                ·
                  refine ⟨264024906133255116701971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352033208177673488935961 264024906133255116701971)
                  ·
                    rfl

theorem cell20_578460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_578460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578460 prefixEnd_578460 := by exact prefixLift 578460
  have htrace : WordTrace (prefixWord ++ tailWord_578460) baseStart_578460 baseEnd_578460 := by
    simpa [prefixWord, tailWord_578460, baseEnd_578460] using wordTrace_append hprefix tailTrace_578460
  have hstable : (prefixWord ++ tailWord_578460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578460).length < 2 ^ (prefixWord ++ tailWord_578460).sum := by decide
  have hdescent : baseEnd_578460 < baseStart_578460 := by decide
  rcases family_descends (prefixWord ++ tailWord_578460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578471 : List Nat := [1, 1, 6, 1, 4, 1, 6]
def baseStart_578471 : Nat := 118140960795 + 578471 * 2 ^ 59
def prefixEnd_578471 : Nat := 4983230072969 + 3 ^ 40 * 578471 * 2
def baseEnd_578471 : Nat := 29336658536998663037251

theorem tailTrace_578471 : CollatzResearch.WordTrace tailWord_578471 prefixEnd_578471 29336658536998663037251 := by
  unfold tailWord_578471
  simp only [CollatzResearch.WordTrace]
  refine ⟨21098570687305836826439267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14065713791537224550959511 21098570687305836826439267)
  ·
    refine ⟨31647856030958755239658901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21098570687305836826439267 31647856030958755239658901)
    ·
      refine ⟨1483493251451191651859011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31647856030958755239658901 1483493251451191651859011)
      ·
        refine ⟨2225239877176787477788517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483493251451191651859011 2225239877176787477788517)
        ·
          refine ⟨417232476970647652085347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2225239877176787477788517 417232476970647652085347)
          ·
            refine ⟨625848715455971478128021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417232476970647652085347 625848715455971478128021)
            ·
              refine ⟨29336658536998663037251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 625848715455971478128021 29336658536998663037251)
              ·
                rfl

theorem cell20_578471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 6].length) (baseStart_578471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578471 prefixEnd_578471 := by exact prefixLift 578471
  have htrace : WordTrace (prefixWord ++ tailWord_578471) baseStart_578471 baseEnd_578471 := by
    simpa [prefixWord, tailWord_578471, baseEnd_578471] using wordTrace_append hprefix tailTrace_578471
  have hstable : (prefixWord ++ tailWord_578471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578471).length < 2 ^ (prefixWord ++ tailWord_578471).sum := by decide
  have hdescent : baseEnd_578471 < baseStart_578471 := by decide
  rcases family_descends (prefixWord ++ tailWord_578471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578481 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 2]
def baseStart_578481 : Nat := 118140960795 + 578481 * 2 ^ 59
def prefixEnd_578481 : Nat := 4983230072969 + 3 ^ 40 * 578481 * 2
def baseEnd_578481 : Nat := 264034491105472377001885

theorem tailTrace_578481 : CollatzResearch.WordTrace tailWord_578481 prefixEnd_578481 264034491105472377001885 := by
  unfold tailWord_578481
  simp only [CollatzResearch.WordTrace]
  refine ⟨21098935417269608534303297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14065956944846405689535531 21098935417269608534303297)
  ·
    refine ⟨15824201562952206400727473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21098935417269608534303297 15824201562952206400727473)
    ·
      refine ⟨11868151172214154800545605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15824201562952206400727473 11868151172214154800545605)
      ·
        refine ⟨2225278344790154025102301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11868151172214154800545605 2225278344790154025102301)
        ·
          refine ⟨834479379296307759413363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2225278344790154025102301 834479379296307759413363)
          ·
            refine ⟨1251719068944461639120045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834479379296307759413363 1251719068944461639120045)
            ·
              refine ⟨469394650854173114670017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251719068944461639120045 469394650854173114670017)
              ·
                refine ⟨352045988140629836002513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469394650854173114670017 352045988140629836002513)
                ·
                  refine ⟨264034491105472377001885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352045988140629836002513 264034491105472377001885)
                  ·
                    rfl

theorem cell20_578481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_578481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578481 prefixEnd_578481 := by exact prefixLift 578481
  have htrace : WordTrace (prefixWord ++ tailWord_578481) baseStart_578481 baseEnd_578481 := by
    simpa [prefixWord, tailWord_578481, baseEnd_578481] using wordTrace_append hprefix tailTrace_578481
  have hstable : (prefixWord ++ tailWord_578481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578481).length < 2 ^ (prefixWord ++ tailWord_578481).sum := by decide
  have hdescent : baseEnd_578481 < baseStart_578481 := by decide
  rcases family_descends (prefixWord ++ tailWord_578481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578530 : List Nat := [3, 3, 3, 1, 1, 9]
def baseStart_578530 : Nat := 118140960795 + 578530 * 2 ^ 59
def prefixEnd_578530 : Nat := 4983230072969 + 3 ^ 40 * 578530 * 2
def baseEnd_578530 : Nat := 9779883557060962384013

theorem tailTrace_578530 : CollatzResearch.WordTrace tailWord_578530 prefixEnd_578530 9779883557060962384013 := by
  unfold tailWord_578530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275180648523022475709261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14067148396061393268558029 5275180648523022475709261)
  ·
    refine ⟨1978192743196133428390973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5275180648523022475709261 1978192743196133428390973)
    ·
      refine ⟨741822278698550035646615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1978192743196133428390973 741822278698550035646615)
      ·
        refine ⟨1112733418047825053469923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741822278698550035646615 1112733418047825053469923)
        ·
          refine ⟨1669100127071737580204885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112733418047825053469923 1669100127071737580204885)
          ·
            refine ⟨9779883557060962384013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1669100127071737580204885 9779883557060962384013)
            ·
              rfl

theorem cell20_578530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 9].length) (baseStart_578530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578530 prefixEnd_578530 := by exact prefixLift 578530
  have htrace : WordTrace (prefixWord ++ tailWord_578530) baseStart_578530 baseEnd_578530 := by
    simpa [prefixWord, tailWord_578530, baseEnd_578530] using wordTrace_append hprefix tailTrace_578530
  have hstable : (prefixWord ++ tailWord_578530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578530).length < 2 ^ (prefixWord ++ tailWord_578530).sum := by decide
  have hdescent : baseEnd_578530 < baseStart_578530 := by decide
  rcases family_descends (prefixWord ++ tailWord_578530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578533 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 3]
def baseStart_578533 : Nat := 118140960795 + 578533 * 2 ^ 59
def prefixEnd_578533 : Nat := 4983230072969 + 3 ^ 40 * 578533 * 2
def baseEnd_578533 : Nat := 264058225322391307268339

theorem tailTrace_578533 : CollatzResearch.WordTrace tailWord_578533 prefixEnd_578533 264058225322391307268339 := by
  unfold tailWord_578533
  simp only [CollatzResearch.WordTrace]
  refine ⟨21100832013081221415196253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14067221342054147610130835 21100832013081221415196253)
  ·
    refine ⟨7912812004905458030698595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21100832013081221415196253 7912812004905458030698595)
    ·
      refine ⟨11869218007358187046047893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7912812004905458030698595 11869218007358187046047893)
      ·
        refine ⟨556369594094915017783495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11869218007358187046047893 556369594094915017783495)
        ·
          refine ⟨834554391142372526675243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556369594094915017783495 834554391142372526675243)
          ·
            refine ⟨1251831586713558790012865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834554391142372526675243 1251831586713558790012865)
            ·
              refine ⟨938873690035169092509649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251831586713558790012865 938873690035169092509649)
              ·
                refine ⟨704155267526376819382237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938873690035169092509649 704155267526376819382237)
                ·
                  refine ⟨264058225322391307268339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704155267526376819382237 264058225322391307268339)
                  ·
                    rfl

theorem cell20_578533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_578533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578533 prefixEnd_578533 := by exact prefixLift 578533
  have htrace : WordTrace (prefixWord ++ tailWord_578533) baseStart_578533 baseEnd_578533 := by
    simpa [prefixWord, tailWord_578533, baseEnd_578533] using wordTrace_append hprefix tailTrace_578533
  have hstable : (prefixWord ++ tailWord_578533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578533).length < 2 ^ (prefixWord ++ tailWord_578533).sum := by decide
  have hdescent : baseEnd_578533 < baseStart_578533 := by decide
  rcases family_descends (prefixWord ++ tailWord_578533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578568 : List Nat := [2, 1, 3, 2, 1, 4, 3, 4]
def baseStart_578568 : Nat := 118140960795 + 578568 * 2 ^ 59
def prefixEnd_578568 : Nat := 4983230072969 + 3 ^ 40 * 578568 * 2
def baseEnd_578568 : Nat := 88024733425362247033843

theorem tailTrace_578568 : CollatzResearch.WordTrace tailWord_578568 prefixEnd_578568 88024733425362247033843 := by
  unfold tailWord_578568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10551054283977211196360179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14068072378636281595146905 10551054283977211196360179)
  ·
    refine ⟨15826581425965816794540269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10551054283977211196360179 15826581425965816794540269)
    ·
      refine ⟨5934968034737181297952601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15826581425965816794540269 5934968034737181297952601)
      ·
        refine ⟨4451226026052885973464451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5934968034737181297952601 4451226026052885973464451)
        ·
          refine ⟨6676839039079328960196677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4451226026052885973464451 6676839039079328960196677)
          ·
            refine ⟨1251907319827374180036877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6676839039079328960196677 1251907319827374180036877)
            ·
              refine ⟨469465244935265317513829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251907319827374180036877 469465244935265317513829)
              ·
                refine ⟨88024733425362247033843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469465244935265317513829 88024733425362247033843)
                ·
                  rfl

theorem cell20_578568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_578568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578568 prefixEnd_578568 := by exact prefixLift 578568
  have htrace : WordTrace (prefixWord ++ tailWord_578568) baseStart_578568 baseEnd_578568 := by
    simpa [prefixWord, tailWord_578568, baseEnd_578568] using wordTrace_append hprefix tailTrace_578568
  have hstable : (prefixWord ++ tailWord_578568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578568).length < 2 ^ (prefixWord ++ tailWord_578568).sum := by decide
  have hdescent : baseEnd_578568 < baseStart_578568 := by decide
  rcases family_descends (prefixWord ++ tailWord_578568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578592 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_578592 : Nat := 118140960795 + 578592 * 2 ^ 59
def prefixEnd_578592 : Nat := 4983230072969 + 3 ^ 40 * 578592 * 2
def baseEnd_578592 : Nat := 264085154530049324301431

theorem tailTrace_578592 : CollatzResearch.WordTrace tailWord_578592 prefixEnd_578592 264085154530049324301431 := by
  unfold tailWord_578592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10551491959933737245797015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14068655946578316327729353 10551491959933737245797015)
  ·
    refine ⟨15827237939900605868695523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10551491959933737245797015 15827237939900605868695523)
    ·
      refine ⟨23740856909850908803043285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15827237939900605868695523 23740856909850908803043285)
      ·
        refine ⟨556426333824630675071327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 23740856909850908803043285 556426333824630675071327)
        ·
          refine ⟨834639500736946012606991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556426333824630675071327 834639500736946012606991)
          ·
            refine ⟨1251959251105419018910487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834639500736946012606991 1251959251105419018910487)
            ·
              refine ⟨1877938876658128528365731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251959251105419018910487 1877938876658128528365731)
              ·
                refine ⟨2816908314987192792548597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877938876658128528365731 2816908314987192792548597)
                ·
                  refine ⟨264085154530049324301431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2816908314987192792548597 264085154530049324301431)
                  ·
                    rfl

theorem cell20_578592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_578592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578592 prefixEnd_578592 := by exact prefixLift 578592
  have htrace : WordTrace (prefixWord ++ tailWord_578592) baseStart_578592 baseEnd_578592 := by
    simpa [prefixWord, tailWord_578592, baseEnd_578592] using wordTrace_append hprefix tailTrace_578592
  have hstable : (prefixWord ++ tailWord_578592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578592).length < 2 ^ (prefixWord ++ tailWord_578592).sum := by decide
  have hdescent : baseEnd_578592 < baseStart_578592 := by decide
  rcases family_descends (prefixWord ++ tailWord_578592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578599 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_578599 : Nat := 118140960795 + 578599 * 2 ^ 59
def prefixEnd_578599 : Nat := 4983230072969 + 3 ^ 40 * 578599 * 2
def baseEnd_578599 : Nat := 264088349520788411068069

theorem tailTrace_578599 : CollatzResearch.WordTrace tailWord_578599 prefixEnd_578599 264088349520788411068069 := by
  unfold tailWord_578599
  simp only [CollatzResearch.WordTrace]
  refine ⟨21103239230842114687098851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14068826153894743124732567 21103239230842114687098851)
  ·
    refine ⟨31654858846263172030648277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21103239230842114687098851 31654858846263172030648277)
    ·
      refine ⟨741910754209293094468319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31654858846263172030648277 741910754209293094468319)
      ·
        refine ⟨1112866131313939641702479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741910754209293094468319 1112866131313939641702479)
        ·
          refine ⟨1669299196970909462553719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112866131313939641702479 1669299196970909462553719)
          ·
            refine ⟨2503948795456364193830579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669299196970909462553719 2503948795456364193830579)
            ·
              refine ⟨3755923193184546290745869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503948795456364193830579 3755923193184546290745869)
              ·
                refine ⟨1408471197444204859029701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3755923193184546290745869 1408471197444204859029701)
                ·
                  refine ⟨264088349520788411068069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408471197444204859029701 264088349520788411068069)
                  ·
                    rfl

theorem cell20_578599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_578599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578599 prefixEnd_578599 := by exact prefixLift 578599
  have htrace : WordTrace (prefixWord ++ tailWord_578599) baseStart_578599 baseEnd_578599 := by
    simpa [prefixWord, tailWord_578599, baseEnd_578599] using wordTrace_append hprefix tailTrace_578599
  have hstable : (prefixWord ++ tailWord_578599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578599).length < 2 ^ (prefixWord ++ tailWord_578599).sum := by decide
  have hdescent : baseEnd_578599 < baseStart_578599 := by decide
  rcases family_descends (prefixWord ++ tailWord_578599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578620 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_578620 : Nat := 118140960795 + 578620 * 2 ^ 59
def prefixEnd_578620 : Nat := 4983230072969 + 3 ^ 40 * 578620 * 2
def baseEnd_578620 : Nat := 264097934493005671367983

theorem tailTrace_578620 : CollatzResearch.WordTrace tailWord_578620 prefixEnd_578620 264097934493005671367983 := by
  unfold tailWord_578620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10552002581883017636806657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14069336775844023515742209 10552002581883017636806657)
  ·
    refine ⟨7914001936412263227604993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10552002581883017636806657 7914001936412263227604993)
    ·
      refine ⟨5935501452309197420703745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7914001936412263227604993 5935501452309197420703745)
      ·
        refine ⟨4451626089231898065527809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5935501452309197420703745 4451626089231898065527809)
        ·
          refine ⟨3338719566923923549145857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4451626089231898065527809 3338719566923923549145857)
          ·
            refine ⟨2504039675192942661859393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3338719566923923549145857 2504039675192942661859393)
            ·
              refine ⟨1878029756394706996394545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504039675192942661859393 1878029756394706996394545)
              ·
                refine ⟨1408522317296030247295909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878029756394706996394545 1408522317296030247295909)
                ·
                  refine ⟨264097934493005671367983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408522317296030247295909 264097934493005671367983)
                  ·
                    rfl

theorem cell20_578620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_578620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578620 prefixEnd_578620 := by exact prefixLift 578620
  have htrace : WordTrace (prefixWord ++ tailWord_578620) baseStart_578620 baseEnd_578620 := by
    simpa [prefixWord, tailWord_578620, baseEnd_578620] using wordTrace_append hprefix tailTrace_578620
  have hstable : (prefixWord ++ tailWord_578620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578620).length < 2 ^ (prefixWord ++ tailWord_578620).sum := by decide
  have hdescent : baseEnd_578620 < baseStart_578620 := by decide
  rcases family_descends (prefixWord ++ tailWord_578620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578630 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_578630 : Nat := 118140960795 + 578630 * 2 ^ 59
def prefixEnd_578630 : Nat := 4983230072969 + 3 ^ 40 * 578630 * 2
def baseEnd_578630 : Nat := 264102498765490081034609

theorem tailTrace_578630 : CollatzResearch.WordTrace tailWord_578630 prefixEnd_578630 264102498765490081034609 := by
  unfold tailWord_578630
  simp only [CollatzResearch.WordTrace]
  refine ⟨659511559179056468171167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14069579929153204654318229 659511559179056468171167)
  ·
    refine ⟨989267338768584702256751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659511559179056468171167 989267338768584702256751)
    ·
      refine ⟨1483901008152877053385127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989267338768584702256751 1483901008152877053385127)
      ·
        refine ⟨2225851512229315580077691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483901008152877053385127 2225851512229315580077691)
        ·
          refine ⟨3338777268343973370116537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225851512229315580077691 3338777268343973370116537)
          ·
            refine ⟨2504082951257980027587403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3338777268343973370116537 2504082951257980027587403)
            ·
              refine ⟨3756124426886970041381105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504082951257980027587403 3756124426886970041381105)
              ·
                refine ⟨2817093320165227531035829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3756124426886970041381105 2817093320165227531035829)
                ·
                  refine ⟨264102498765490081034609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2817093320165227531035829 264102498765490081034609)
                  ·
                    rfl

theorem cell20_578630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_578630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578630 prefixEnd_578630 := by exact prefixLift 578630
  have htrace : WordTrace (prefixWord ++ tailWord_578630) baseStart_578630 baseEnd_578630 := by
    simpa [prefixWord, tailWord_578630, baseEnd_578630] using wordTrace_append hprefix tailTrace_578630
  have hstable : (prefixWord ++ tailWord_578630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578630).length < 2 ^ (prefixWord ++ tailWord_578630).sum := by decide
  have hdescent : baseEnd_578630 < baseStart_578630 := by decide
  rcases family_descends (prefixWord ++ tailWord_578630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578634 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_578634 : Nat := 118140960795 + 578634 * 2 ^ 59
def prefixEnd_578634 : Nat := 4983230072969 + 3 ^ 40 * 578634 * 2
def baseEnd_578634 : Nat := 264104324474483844901259

theorem tailTrace_578634 : CollatzResearch.WordTrace tailWord_578634 prefixEnd_578634 264104324474483844901259 := by
  unfold tailWord_578634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276128946428828916155739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14069677190476877109748637 5276128946428828916155739)
  ·
    refine ⟨7914193419643243374233609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5276128946428828916155739 7914193419643243374233609)
    ·
      refine ⟨5935645064732432530675207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7914193419643243374233609 5935645064732432530675207)
      ·
        refine ⟨8903467597098648796012811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935645064732432530675207 8903467597098648796012811)
        ·
          refine ⟨13355201395647973194019217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8903467597098648796012811 13355201395647973194019217)
          ·
            refine ⟨10016401046735979895514413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13355201395647973194019217 10016401046735979895514413)
            ·
              refine ⟨3756150392525992460817905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10016401046735979895514413 3756150392525992460817905)
              ·
                refine ⟨2817112794394494345613429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3756150392525992460817905 2817112794394494345613429)
                ·
                  refine ⟨264104324474483844901259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2817112794394494345613429 264104324474483844901259)
                  ·
                    rfl

theorem cell20_578634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_578634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578634 prefixEnd_578634 := by exact prefixLift 578634
  have htrace : WordTrace (prefixWord ++ tailWord_578634) baseStart_578634 baseEnd_578634 := by
    simpa [prefixWord, tailWord_578634, baseEnd_578634] using wordTrace_append hprefix tailTrace_578634
  have hstable : (prefixWord ++ tailWord_578634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578634).length < 2 ^ (prefixWord ++ tailWord_578634).sum := by decide
  have hdescent : baseEnd_578634 < baseStart_578634 := by decide
  rcases family_descends (prefixWord ++ tailWord_578634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578641 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_578641 : Nat := 118140960795 + 578641 * 2 ^ 59
def prefixEnd_578641 : Nat := 4983230072969 + 3 ^ 40 * 578641 * 2
def baseEnd_578641 : Nat := 264107519465222931667897

theorem tailTrace_578641 : CollatzResearch.WordTrace tailWord_578641 prefixEnd_578641 264107519465222931667897 := by
  unfold tailWord_578641
  simp only [CollatzResearch.WordTrace]
  refine ⟨21104771096689955860127777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14069847397793303906751851 21104771096689955860127777)
  ·
    refine ⟨15828578322517466895095833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21104771096689955860127777 15828578322517466895095833)
    ·
      refine ⟨11871433741888100171321875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15828578322517466895095833 11871433741888100171321875)
      ·
        refine ⟨17807150612832150256982813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11871433741888100171321875 17807150612832150256982813)
        ·
          refine ⟨6677681479812056346368555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17807150612832150256982813 6677681479812056346368555)
          ·
            refine ⟨10016522219718084519552833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6677681479812056346368555 10016522219718084519552833)
            ·
              refine ⟨7512391664788563389664625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10016522219718084519552833 7512391664788563389664625)
              ·
                refine ⟨5634293748591422542248469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7512391664788563389664625 5634293748591422542248469)
                ·
                  refine ⟨264107519465222931667897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5634293748591422542248469 264107519465222931667897)
                  ·
                    rfl

theorem cell20_578641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_578641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578641 prefixEnd_578641 := by exact prefixLift 578641
  have htrace : WordTrace (prefixWord ++ tailWord_578641) baseStart_578641 baseEnd_578641 := by
    simpa [prefixWord, tailWord_578641, baseEnd_578641] using wordTrace_append hprefix tailTrace_578641
  have hstable : (prefixWord ++ tailWord_578641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578641).length < 2 ^ (prefixWord ++ tailWord_578641).sum := by decide
  have hdescent : baseEnd_578641 < baseStart_578641 := by decide
  rcases family_descends (prefixWord ++ tailWord_578641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578664 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_578664 : Nat := 118140960795 + 578664 * 2 ^ 59
def prefixEnd_578664 : Nat := 4983230072969 + 3 ^ 40 * 578664 * 2
def baseEnd_578664 : Nat := 264118017291937073901137

theorem tailTrace_578664 : CollatzResearch.WordTrace tailWord_578664 prefixEnd_578664 264118017291937073901137 := by
  unfold tailWord_578664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10552804987803315394107523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14070406650404420525476697 10552804987803315394107523)
  ·
    refine ⟨15829207481704973091161285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10552804987803315394107523 15829207481704973091161285)
    ·
      refine ⟨2967976402819682454592741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15829207481704973091161285 2967976402819682454592741)
      ·
        refine ⟨556495575528690460236139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2967976402819682454592741 556495575528690460236139)
        ·
          refine ⟨834743363293035690354209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556495575528690460236139 834743363293035690354209)
          ·
            refine ⟨626057522469776767765657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834743363293035690354209 626057522469776767765657)
            ·
              refine ⟨469543141852332575824243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626057522469776767765657 469543141852332575824243)
              ·
                refine ⟨704314712778498863736365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469543141852332575824243 704314712778498863736365)
                ·
                  refine ⟨264118017291937073901137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704314712778498863736365 264118017291937073901137)
                  ·
                    rfl

theorem cell20_578664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_578664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578664 prefixEnd_578664 := by exact prefixLift 578664
  have htrace : WordTrace (prefixWord ++ tailWord_578664) baseStart_578664 baseEnd_578664 := by
    simpa [prefixWord, tailWord_578664, baseEnd_578664] using wordTrace_append hprefix tailTrace_578664
  have hstable : (prefixWord ++ tailWord_578664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578664).length < 2 ^ (prefixWord ++ tailWord_578664).sum := by decide
  have hdescent : baseEnd_578664 < baseStart_578664 := by decide
  rcases family_descends (prefixWord ++ tailWord_578664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578665 : List Nat := [1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_578665 : Nat := 118140960795 + 578665 * 2 ^ 59
def prefixEnd_578665 : Nat := 4983230072969 + 3 ^ 40 * 578665 * 2
def baseEnd_578665 : Nat := 88039491239728504955933

theorem tailTrace_578665 : CollatzResearch.WordTrace tailWord_578665 prefixEnd_578665 88039491239728504955933 := by
  unfold tailWord_578665
  simp only [CollatzResearch.WordTrace]
  refine ⟨21105646448603007959001449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14070430965735338639334299 21105646448603007959001449)
  ·
    refine ⟨15829234836452255969251087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21105646448603007959001449 15829234836452255969251087)
    ·
      refine ⟨23743852254678383953876631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15829234836452255969251087 23743852254678383953876631)
      ·
        refine ⟨35615778382017575930814947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23743852254678383953876631 35615778382017575930814947)
        ·
          refine ⟨53423667573026363896222421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35615778382017575930814947 53423667573026363896222421)
          ·
            refine ⟨1252117208742805403817713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53423667573026363896222421 1252117208742805403817713)
            ·
              refine ⟨939087906557104052863285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252117208742805403817713 939087906557104052863285)
              ·
                refine ⟨88039491239728504955933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 939087906557104052863285 88039491239728504955933)
                ·
                  rfl

theorem cell20_578665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_578665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578665 prefixEnd_578665 := by exact prefixLift 578665
  have htrace : WordTrace (prefixWord ++ tailWord_578665) baseStart_578665 baseEnd_578665 := by
    simpa [prefixWord, tailWord_578665, baseEnd_578665] using wordTrace_append hprefix tailTrace_578665
  have hstable : (prefixWord ++ tailWord_578665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578665).length < 2 ^ (prefixWord ++ tailWord_578665).sum := by decide
  have hdescent : baseEnd_578665 < baseStart_578665 := by decide
  rcases family_descends (prefixWord ++ tailWord_578665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578679 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_578679 : Nat := 118140960795 + 578679 * 2 ^ 59
def prefixEnd_578679 : Nat := 4983230072969 + 3 ^ 40 * 578679 * 2
def baseEnd_578679 : Nat := 264124863700663688401075

theorem tailTrace_578679 : CollatzResearch.WordTrace tailWord_578679 prefixEnd_578679 264124863700663688401075 := by
  unfold tailWord_578679
  simp only [CollatzResearch.WordTrace]
  refine ⟨21106157070552288350011091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14070771380368192233340727 21106157070552288350011091)
  ·
    refine ⟨31659235605828432525016637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21106157070552288350011091 31659235605828432525016637)
    ·
      refine ⟨11872213352185662196881239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31659235605828432525016637 11872213352185662196881239)
      ·
        refine ⟨17808320028278493295321859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11872213352185662196881239 17808320028278493295321859)
        ·
          refine ⟨26712480042417739942982789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17808320028278493295321859 26712480042417739942982789)
          ·
            refine ⟨5008590007953326239309273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26712480042417739942982789 5008590007953326239309273)
            ·
              refine ⟨3756442505964994679481955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008590007953326239309273 3756442505964994679481955)
              ·
                refine ⟨5634663758947492019222933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756442505964994679481955 5634663758947492019222933)
                ·
                  refine ⟨264124863700663688401075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5634663758947492019222933 264124863700663688401075)
                  ·
                    rfl

theorem cell20_578679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_578679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578679 prefixEnd_578679 := by exact prefixLift 578679
  have htrace : WordTrace (prefixWord ++ tailWord_578679) baseStart_578679 baseEnd_578679 := by
    simpa [prefixWord, tailWord_578679, baseEnd_578679] using wordTrace_append hprefix tailTrace_578679
  have hstable : (prefixWord ++ tailWord_578679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578679).length < 2 ^ (prefixWord ++ tailWord_578679).sum := by decide
  have hdescent : baseEnd_578679 < baseStart_578679 := by decide
  rcases family_descends (prefixWord ++ tailWord_578679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578706 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_578706 : Nat := 118140960795 + 578706 * 2 ^ 59
def prefixEnd_578706 : Nat := 4983230072969 + 3 ^ 40 * 578706 * 2
def baseEnd_578706 : Nat := 264137187236371594500965

theorem tailTrace_578706 : CollatzResearch.WordTrace tailWord_578706 prefixEnd_578706 264137187236371594500965 := by
  unfold tailWord_578706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276785460363617990310993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14071427894302981307495981 5276785460363617990310993)
  ·
    refine ⟨3957589095272713492733245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5276785460363617990310993 3957589095272713492733245)
    ·
      refine ⟨1484095910727267559774967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3957589095272713492733245 1484095910727267559774967)
      ·
        refine ⟨2226143866090901339662451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484095910727267559774967 2226143866090901339662451)
        ·
          refine ⟨3339215799136352009493677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226143866090901339662451 3339215799136352009493677)
          ·
            refine ⟨1252205924676132003560129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3339215799136352009493677 1252205924676132003560129)
            ·
              refine ⟨939154443507099002670097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252205924676132003560129 939154443507099002670097)
              ·
                refine ⟨704365832630324252002573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939154443507099002670097 704365832630324252002573)
                ·
                  refine ⟨264137187236371594500965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704365832630324252002573 264137187236371594500965)
                  ·
                    rfl

theorem cell20_578706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_578706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578706 prefixEnd_578706 := by exact prefixLift 578706
  have htrace : WordTrace (prefixWord ++ tailWord_578706) baseStart_578706 baseEnd_578706 := by
    simpa [prefixWord, tailWord_578706, baseEnd_578706] using wordTrace_append hprefix tailTrace_578706
  have hstable : (prefixWord ++ tailWord_578706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578706).length < 2 ^ (prefixWord ++ tailWord_578706).sum := by decide
  have hdescent : baseEnd_578706 < baseStart_578706 := by decide
  rcases family_descends (prefixWord ++ tailWord_578706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578796 : List Nat := [2, 2, 1, 1, 2, 6, 2, 4]
def baseStart_578796 : Nat := 118140960795 + 578796 * 2 ^ 59
def prefixEnd_578796 : Nat := 4983230072969 + 3 ^ 40 * 578796 * 2
def baseEnd_578796 : Nat := 88059421896243760500199

theorem tailTrace_578796 : CollatzResearch.WordTrace tailWord_578796 prefixEnd_578796 88059421896243760500199 := by
  unfold tailWord_578796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10555212205564208666010121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14073616274085611554680161 10555212205564208666010121)
  ·
    refine ⟨7916409154173156499507591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10555212205564208666010121 7916409154173156499507591)
    ·
      refine ⟨11874613731259734749261387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7916409154173156499507591 11874613731259734749261387)
      ·
        refine ⟨17811920596889602123892081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11874613731259734749261387 17811920596889602123892081)
        ·
          refine ⟨13358940447667201592919061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17811920596889602123892081 13358940447667201592919061)
          ·
            refine ⟨626200333484400074668081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13358940447667201592919061 626200333484400074668081)
            ·
              refine ⟨469650250113300056001061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626200333484400074668081 469650250113300056001061)
              ·
                refine ⟨88059421896243760500199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469650250113300056001061 88059421896243760500199)
                ·
                  rfl

theorem cell20_578796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_578796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578796 prefixEnd_578796 := by exact prefixLift 578796
  have htrace : WordTrace (prefixWord ++ tailWord_578796) baseStart_578796 baseEnd_578796 := by
    simpa [prefixWord, tailWord_578796, baseEnd_578796] using wordTrace_append hprefix tailTrace_578796
  have hstable : (prefixWord ++ tailWord_578796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578796).length < 2 ^ (prefixWord ++ tailWord_578796).sum := by decide
  have hdescent : baseEnd_578796 < baseStart_578796 := by decide
  rcases family_descends (prefixWord ++ tailWord_578796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578817 : List Nat := [1, 2, 4, 1, 1, 5, 6]
def baseStart_578817 : Nat := 118140960795 + 578817 * 2 ^ 59
def prefixEnd_578817 : Nat := 4983230072969 + 3 ^ 40 * 578817 * 2
def baseEnd_578817 : Nat := 29354205628994282422279

theorem tailTrace_578817 : CollatzResearch.WordTrace tailWord_578817 prefixEnd_578817 29354205628994282422279 := by
  unfold tailWord_578817
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111190344052337918534705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14074126896034891945689803 21111190344052337918534705)
  ·
    refine ⟨15833392758039253438901029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21111190344052337918534705 15833392758039253438901029)
    ·
      refine ⟨2968761142132360019793943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15833392758039253438901029 2968761142132360019793943)
      ·
        refine ⟨4453141713198540029690915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968761142132360019793943 4453141713198540029690915)
        ·
          refine ⟨6679712569797810044536373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453141713198540029690915 6679712569797810044536373)
          ·
            refine ⟨626223053418544691675285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6679712569797810044536373 626223053418544691675285)
            ·
              refine ⟨29354205628994282422279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 626223053418544691675285 29354205628994282422279)
              ·
                rfl

theorem cell20_578817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_578817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578817 prefixEnd_578817 := by exact prefixLift 578817
  have htrace : WordTrace (prefixWord ++ tailWord_578817) baseStart_578817 baseEnd_578817 := by
    simpa [prefixWord, tailWord_578817, baseEnd_578817] using wordTrace_append hprefix tailTrace_578817
  have hstable : (prefixWord ++ tailWord_578817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578817).length < 2 ^ (prefixWord ++ tailWord_578817).sum := by decide
  have hdescent : baseEnd_578817 < baseStart_578817 := by decide
  rcases family_descends (prefixWord ++ tailWord_578817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578876 : List Nat := [2, 2, 2, 2, 1, 11]
def baseStart_578876 : Nat := 118140960795 + 578876 * 2 ^ 59
def prefixEnd_578876 : Nat := 4983230072969 + 3 ^ 40 * 578876 * 2
def baseEnd_578876 : Nat := 9785732587726168845689

theorem tailTrace_578876 : CollatzResearch.WordTrace tailWord_578876 prefixEnd_578876 9785732587726168845689 := by
  unfold tailWord_578876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556671125419295497466241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14075561500559060663288321 10556671125419295497466241)
  ·
    refine ⟨7917503344064471623099681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10556671125419295497466241 7917503344064471623099681)
    ·
      refine ⟨5938127508048353717324761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7917503344064471623099681 5938127508048353717324761)
      ·
        refine ⟨4453595631036265287993571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5938127508048353717324761 4453595631036265287993571)
        ·
          refine ⟨6680393446554397931990357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453595631036265287993571 6680393446554397931990357)
          ·
            refine ⟨9785732587726168845689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6680393446554397931990357 9785732587726168845689)
            ·
              rfl

theorem cell20_578876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 11].length) (baseStart_578876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578876 prefixEnd_578876 := by exact prefixLift 578876
  have htrace : WordTrace (prefixWord ++ tailWord_578876) baseStart_578876 baseEnd_578876 := by
    simpa [prefixWord, tailWord_578876, baseEnd_578876] using wordTrace_append hprefix tailTrace_578876
  have hstable : (prefixWord ++ tailWord_578876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578876).length < 2 ^ (prefixWord ++ tailWord_578876).sum := by decide
  have hdescent : baseEnd_578876 < baseStart_578876 := by decide
  rcases family_descends (prefixWord ++ tailWord_578876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578879 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_578879 : Nat := 118140960795 + 578879 * 2 ^ 59
def prefixEnd_578879 : Nat := 4983230072969 + 3 ^ 40 * 578879 * 2
def baseEnd_578879 : Nat := 264216149150351881733591

theorem tailTrace_578879 : CollatzResearch.WordTrace tailWord_578879 prefixEnd_578879 264216149150351881733591 := by
  unfold tailWord_578879
  simp only [CollatzResearch.WordTrace]
  refine ⟨21113451669827722507291691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14075634446551815004861127 21113451669827722507291691)
  ·
    refine ⟨31670177504741583760937537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21113451669827722507291691 31670177504741583760937537)
    ·
      refine ⟨23752633128556187820703153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31670177504741583760937537 23752633128556187820703153)
      ·
        refine ⟨17814474846417140865527365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23752633128556187820703153 17814474846417140865527365)
        ·
          refine ⟨3340214033703213912286381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17814474846417140865527365 3340214033703213912286381)
          ·
            refine ⟨1252580262638705217107393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3340214033703213912286381 1252580262638705217107393)
            ·
              refine ⟨939435196979028912830545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252580262638705217107393 939435196979028912830545)
              ·
                refine ⟨704576397734271684622909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939435196979028912830545 704576397734271684622909)
                ·
                  refine ⟨264216149150351881733591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704576397734271684622909 264216149150351881733591)
                  ·
                    rfl

theorem cell20_578879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_578879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578879 prefixEnd_578879 := by exact prefixLift 578879
  have htrace : WordTrace (prefixWord ++ tailWord_578879) baseStart_578879 baseEnd_578879 := by
    simpa [prefixWord, tailWord_578879, baseEnd_578879] using wordTrace_append hprefix tailTrace_578879
  have hstable : (prefixWord ++ tailWord_578879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578879).length < 2 ^ (prefixWord ++ tailWord_578879).sum := by decide
  have hdescent : baseEnd_578879 < baseStart_578879 := by decide
  rcases family_descends (prefixWord ++ tailWord_578879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578920 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 2]
def baseStart_578920 : Nat := 118140960795 + 578920 * 2 ^ 59
def prefixEnd_578920 : Nat := 4983230072969 + 3 ^ 40 * 578920 * 2
def baseEnd_578920 : Nat := 264234862667537961366757

theorem tailTrace_578920 : CollatzResearch.WordTrace tailWord_578920 prefixEnd_578920 264234862667537961366757 := by
  unfold tailWord_578920
  simp only [CollatzResearch.WordTrace]
  refine ⟨10557473531339593254767107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14076631375119457673022809 10557473531339593254767107)
  ·
    refine ⟨15836210297009389882150661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10557473531339593254767107 15836210297009389882150661)
    ·
      refine ⟨2969289430689260602903249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15836210297009389882150661 2969289430689260602903249)
      ·
        refine ⟨2226967073016945452177437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2969289430689260602903249 2226967073016945452177437)
        ·
          refine ⟨835112652381354544566539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2226967073016945452177437 835112652381354544566539)
          ·
            refine ⟨1252668978572031816849809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835112652381354544566539 1252668978572031816849809)
            ·
              refine ⟨939501733929023862637357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252668978572031816849809 939501733929023862637357)
              ·
                refine ⟨352313150223383948489009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939501733929023862637357 352313150223383948489009)
                ·
                  refine ⟨264234862667537961366757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352313150223383948489009 264234862667537961366757)
                  ·
                    rfl

theorem cell20_578920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_578920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578920 prefixEnd_578920 := by exact prefixLift 578920
  have htrace : WordTrace (prefixWord ++ tailWord_578920) baseStart_578920 baseEnd_578920 := by
    simpa [prefixWord, tailWord_578920, baseEnd_578920] using wordTrace_append hprefix tailTrace_578920
  have hstable : (prefixWord ++ tailWord_578920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578920).length < 2 ^ (prefixWord ++ tailWord_578920).sum := by decide
  have hdescent : baseEnd_578920 < baseStart_578920 := by decide
  rcases family_descends (prefixWord ++ tailWord_578920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578955 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 3]
def baseStart_578955 : Nat := 118140960795 + 578955 * 2 ^ 59
def prefixEnd_578955 : Nat := 4983230072969 + 3 ^ 40 * 578955 * 2
def baseEnd_578955 : Nat := 264250837621233395199947

theorem tailTrace_578955 : CollatzResearch.WordTrace tailWord_578955 prefixEnd_578955 264250837621233395199947 := by
  unfold tailWord_578955
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116223617552387487058319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14077482411701591658038879 21116223617552387487058319)
  ·
    refine ⟨31674335426328581230587479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21116223617552387487058319 31674335426328581230587479)
    ·
      refine ⟨47511503139492871845881219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31674335426328581230587479 47511503139492871845881219)
      ·
        refine ⟨71267254709239307768821829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47511503139492871845881219 71267254709239307768821829)
        ·
          refine ⟨13362610257982370206654093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71267254709239307768821829 13362610257982370206654093)
          ·
            refine ⟨5010978846743388827495285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13362610257982370206654093 5010978846743388827495285)
            ·
              refine ⟨469779266882192702577683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5010978846743388827495285 469779266882192702577683)
              ·
                refine ⟨704668900323289053866525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469779266882192702577683 704668900323289053866525)
                ·
                  refine ⟨264250837621233395199947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704668900323289053866525 264250837621233395199947)
                  ·
                    rfl

theorem cell20_578955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_578955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578955 prefixEnd_578955 := by exact prefixLift 578955
  have htrace : WordTrace (prefixWord ++ tailWord_578955) baseStart_578955 baseEnd_578955 := by
    simpa [prefixWord, tailWord_578955, baseEnd_578955] using wordTrace_append hprefix tailTrace_578955
  have hstable : (prefixWord ++ tailWord_578955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578955).length < 2 ^ (prefixWord ++ tailWord_578955).sum := by decide
  have hdescent : baseEnd_578955 < baseStart_578955 := by decide
  rcases family_descends (prefixWord ++ tailWord_578955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578969 : List Nat := [1, 2, 1, 2, 1, 5, 4, 4]
def baseStart_578969 : Nat := 118140960795 + 578969 * 2 ^ 59
def prefixEnd_578969 : Nat := 4983230072969 + 3 ^ 40 * 578969 * 2
def baseEnd_578969 : Nat := 88085742534237189577741

theorem tailTrace_578969 : CollatzResearch.WordTrace tailWord_578969 prefixEnd_578969 88085742534237189577741 := by
  unfold tailWord_578969
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116734239501667878067961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14077822826334445252045307 21116734239501667878067961)
  ·
    refine ⟨15837550679626250908550971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21116734239501667878067961 15837550679626250908550971)
    ·
      refine ⟨23756326019439376362826457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15837550679626250908550971 23756326019439376362826457)
      ·
        refine ⟨17817244514579532272119843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23756326019439376362826457 17817244514579532272119843)
        ·
          refine ⟨26725866771869298408179765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17817244514579532272119843 26725866771869298408179765)
          ·
            refine ⟨2505550009862746725766853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26725866771869298408179765 2505550009862746725766853)
            ·
              refine ⟨469790626849265011081285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2505550009862746725766853 469790626849265011081285)
              ·
                refine ⟨88085742534237189577741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469790626849265011081285 88085742534237189577741)
                ·
                  rfl

theorem cell20_578969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_578969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_578969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_578969 prefixEnd_578969 := by exact prefixLift 578969
  have htrace : WordTrace (prefixWord ++ tailWord_578969) baseStart_578969 baseEnd_578969 := by
    simpa [prefixWord, tailWord_578969, baseEnd_578969] using wordTrace_append hprefix tailTrace_578969
  have hstable : (prefixWord ++ tailWord_578969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578969).length < 2 ^ (prefixWord ++ tailWord_578969).sum := by decide
  have hdescent : baseEnd_578969 < baseStart_578969 := by decide
  rcases family_descends (prefixWord ++ tailWord_578969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579000 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 2]
def baseStart_579000 : Nat := 118140960795 + 579000 * 2 ^ 59
def prefixEnd_579000 : Nat := 4983230072969 + 3 ^ 40 * 579000 * 2
def baseEnd_579000 : Nat := 264271376847413238699763

theorem tailTrace_579000 : CollatzResearch.WordTrace tailWord_579000 prefixEnd_579000 264271376847413238699763 := by
  unfold tailWord_579000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10558932451194680086223227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14078576601592906781630969 10558932451194680086223227)
  ·
    refine ⟨15838398676792020129334841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10558932451194680086223227 15838398676792020129334841)
    ·
      refine ⟨11878799007594015097001131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15838398676792020129334841 11878799007594015097001131)
      ·
        refine ⟨17818198511391022645501697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11878799007594015097001131 17818198511391022645501697)
        ·
          refine ⟨13363648883543266984126273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17818198511391022645501697 13363648883543266984126273)
          ·
            refine ⟨10022736662657450238094705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13363648883543266984126273 10022736662657450238094705)
            ·
              refine ⟨7517052496993087678571029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10022736662657450238094705 7517052496993087678571029)
              ·
                refine ⟨352361835796550984933017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7517052496993087678571029 352361835796550984933017)
                ·
                  refine ⟨264271376847413238699763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352361835796550984933017 264271376847413238699763)
                  ·
                    rfl

theorem cell20_579000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_579000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579000 prefixEnd_579000 := by exact prefixLift 579000
  have htrace : WordTrace (prefixWord ++ tailWord_579000) baseStart_579000 baseEnd_579000 := by
    simpa [prefixWord, tailWord_579000, baseEnd_579000] using wordTrace_append hprefix tailTrace_579000
  have hstable : (prefixWord ++ tailWord_579000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579000).length < 2 ^ (prefixWord ++ tailWord_579000).sum := by decide
  have hdescent : baseEnd_579000 < baseStart_579000 := by decide
  rcases family_descends (prefixWord ++ tailWord_579000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579055 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 2]
def baseStart_579055 : Nat := 118140960795 + 579055 * 2 ^ 59
def prefixEnd_579055 : Nat := 4983230072969 + 3 ^ 40 * 579055 * 2
def baseEnd_579055 : Nat := 264296480346077491866205

theorem tailTrace_579055 : CollatzResearch.WordTrace tailWord_579055 prefixEnd_579055 264296480346077491866205 := by
  unfold tailWord_579055
  simp only [CollatzResearch.WordTrace]
  refine ⟨21119870917190104565698619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14079913944793403043799079 21119870917190104565698619)
  ·
    refine ⟨31679806375785156848547929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21119870917190104565698619 31679806375785156848547929)
    ·
      refine ⟨23759854781838867636410947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31679806375785156848547929 23759854781838867636410947)
      ·
        refine ⟨35639782172758301454616421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23759854781838867636410947 35639782172758301454616421)
        ·
          refine ⟨6682459157392181522740579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35639782172758301454616421 6682459157392181522740579)
          ·
            refine ⟨10023688736088272284110869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6682459157392181522740579 10023688736088272284110869)
            ·
              refine ⟨469860409504137763317697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10023688736088272284110869 469860409504137763317697)
              ·
                refine ⟨352395307128103322488273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469860409504137763317697 352395307128103322488273)
                ·
                  refine ⟨264296480346077491866205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352395307128103322488273 264296480346077491866205)
                  ·
                    rfl

theorem cell20_579055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 2].length) (baseStart_579055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579055 prefixEnd_579055 := by exact prefixLift 579055
  have htrace : WordTrace (prefixWord ++ tailWord_579055) baseStart_579055 baseEnd_579055 := by
    simpa [prefixWord, tailWord_579055, baseEnd_579055] using wordTrace_append hprefix tailTrace_579055
  have hstable : (prefixWord ++ tailWord_579055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579055).length < 2 ^ (prefixWord ++ tailWord_579055).sum := by decide
  have hdescent : baseEnd_579055 < baseStart_579055 := by decide
  rcases family_descends (prefixWord ++ tailWord_579055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579062 : List Nat := [5, 1, 1, 1, 2, 4, 1, 5]
def baseStart_579062 : Nat := 118140960795 + 579062 * 2 ^ 59
def prefixEnd_579062 : Nat := 4983230072969 + 3 ^ 40 * 579062 * 2
def baseEnd_579062 : Nat := 88099891778938859544281

theorem tailTrace_579062 : CollatzResearch.WordTrace tailWord_579062 prefixEnd_579062 88099891778938859544281 := by
  unfold tailWord_579062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320007889260296547575215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14080084152109829840802293 1320007889260296547575215)
  ·
    refine ⟨1980011833890444821362823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320007889260296547575215 1980011833890444821362823)
    ·
      refine ⟨2970017750835667232044235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980011833890444821362823 2970017750835667232044235)
      ·
        refine ⟨4455026626253500848066353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970017750835667232044235 4455026626253500848066353)
        ·
          refine ⟨3341269969690125636049765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4455026626253500848066353 3341269969690125636049765)
          ·
            refine ⟨626488119316898556759331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3341269969690125636049765 626488119316898556759331)
            ·
              refine ⟨939732178975347835138997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626488119316898556759331 939732178975347835138997)
              ·
                refine ⟨88099891778938859544281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 939732178975347835138997 88099891778938859544281)
                ·
                  rfl

theorem cell20_579062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_579062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579062 prefixEnd_579062 := by exact prefixLift 579062
  have htrace : WordTrace (prefixWord ++ tailWord_579062) baseStart_579062 baseEnd_579062 := by
    simpa [prefixWord, tailWord_579062, baseEnd_579062] using wordTrace_append hprefix tailTrace_579062
  have hstable : (prefixWord ++ tailWord_579062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579062).length < 2 ^ (prefixWord ++ tailWord_579062).sum := by decide
  have hdescent : baseEnd_579062 < baseStart_579062 := by decide
  rcases family_descends (prefixWord ++ tailWord_579062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579093 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 2]
def baseStart_579093 : Nat := 118140960795 + 579093 * 2 ^ 59
def prefixEnd_579093 : Nat := 4983230072969 + 3 ^ 40 * 579093 * 2
def baseEnd_579093 : Nat := 264313824581518248599383

theorem tailTrace_579093 : CollatzResearch.WordTrace tailWord_579093 prefixEnd_579093 264313824581518248599383 := by
  unfold tailWord_579093
  simp only [CollatzResearch.WordTrace]
  refine ⟨21121256891052437055581933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14080837927368291370387955 21121256891052437055581933)
  ·
    refine ⟨7920471334144663895843225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21121256891052437055581933 7920471334144663895843225)
    ·
      refine ⟨5940353500608497921882419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7920471334144663895843225 5940353500608497921882419)
      ·
        refine ⟨8910530250912746882823629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5940353500608497921882419 8910530250912746882823629)
        ·
          refine ⟨3341448844092280081058861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8910530250912746882823629 3341448844092280081058861)
          ·
            refine ⟨1253043316534605030397073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3341448844092280081058861 1253043316534605030397073)
            ·
              refine ⟨939782487400953772797805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253043316534605030397073 939782487400953772797805)
              ·
                refine ⟨352418432775357664799177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939782487400953772797805 352418432775357664799177)
                ·
                  refine ⟨264313824581518248599383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352418432775357664799177 264313824581518248599383)
                  ·
                    rfl

theorem cell20_579093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_579093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579093 prefixEnd_579093 := by exact prefixLift 579093
  have htrace : WordTrace (prefixWord ++ tailWord_579093) baseStart_579093 baseEnd_579093 := by
    simpa [prefixWord, tailWord_579093, baseEnd_579093] using wordTrace_append hprefix tailTrace_579093
  have hstable : (prefixWord ++ tailWord_579093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579093).length < 2 ^ (prefixWord ++ tailWord_579093).sum := by decide
  have hdescent : baseEnd_579093 < baseStart_579093 := by decide
  rcases family_descends (prefixWord ++ tailWord_579093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579114 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_579114 : Nat := 118140960795 + 579114 * 2 ^ 59
def prefixEnd_579114 : Nat := 4983230072969 + 3 ^ 40 * 579114 * 2
def baseEnd_579114 : Nat := 264323409553735508899297

theorem tailTrace_579114 : CollatzResearch.WordTrace tailWord_579114 prefixEnd_579114 264323409553735508899297 := by
  unfold tailWord_579114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280505705994089410524099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14081348549317571761397597 5280505705994089410524099)
  ·
    refine ⟨7920758558991134115786149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5280505705994089410524099 7920758558991134115786149)
    ·
      refine ⟨1485142229810837646709903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7920758558991134115786149 1485142229810837646709903)
      ·
        refine ⟨2227713344716256470064855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485142229810837646709903 2227713344716256470064855)
        ·
          refine ⟨3341570017074384705097283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227713344716256470064855 3341570017074384705097283)
          ·
            refine ⟨5012355025611577057645925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341570017074384705097283 5012355025611577057645925)
            ·
              refine ⟨939816567302170698308611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5012355025611577057645925 939816567302170698308611)
              ·
                refine ⟨1409724850953256047462917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939816567302170698308611 1409724850953256047462917)
                ·
                  refine ⟨264323409553735508899297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409724850953256047462917 264323409553735508899297)
                  ·
                    rfl

theorem cell20_579114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_579114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579114 prefixEnd_579114 := by exact prefixLift 579114
  have htrace : WordTrace (prefixWord ++ tailWord_579114) baseStart_579114 baseEnd_579114 := by
    simpa [prefixWord, tailWord_579114, baseEnd_579114] using wordTrace_append hprefix tailTrace_579114
  have hstable : (prefixWord ++ tailWord_579114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579114).length < 2 ^ (prefixWord ++ tailWord_579114).sum := by decide
  have hdescent : baseEnd_579114 < baseStart_579114 := by decide
  rcases family_descends (prefixWord ++ tailWord_579114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579135 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_579135 : Nat := 118140960795 + 579135 * 2 ^ 59
def prefixEnd_579135 : Nat := 4983230072969 + 3 ^ 40 * 579135 * 2
def baseEnd_579135 : Nat := 264332994525952769199211

theorem tailTrace_579135 : CollatzResearch.WordTrace tailWord_579135 prefixEnd_579135 264332994525952769199211 := by
  unfold tailWord_579135
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122788756900278228610859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14081859171266852152407239 21122788756900278228610859)
  ·
    refine ⟨31684183135350417342916289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21122788756900278228610859 31684183135350417342916289)
    ·
      refine ⟨23763137351512813007187217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31684183135350417342916289 23763137351512813007187217)
      ·
        refine ⟨17822353013634609755390413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23763137351512813007187217 17822353013634609755390413)
        ·
          refine ⟨6683382380112978658271405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17822353013634609755390413 6683382380112978658271405)
          ·
            refine ⟨2506268392542366996851777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6683382380112978658271405 2506268392542366996851777)
            ·
              refine ⟨1879701294406775247638833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506268392542366996851777 1879701294406775247638833)
              ·
                refine ⟨1409775970805081435729125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879701294406775247638833 1409775970805081435729125)
                ·
                  refine ⟨264332994525952769199211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409775970805081435729125 264332994525952769199211)
                  ·
                    rfl

theorem cell20_579135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_579135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579135 prefixEnd_579135 := by exact prefixLift 579135
  have htrace : WordTrace (prefixWord ++ tailWord_579135) baseStart_579135 baseEnd_579135 := by
    simpa [prefixWord, tailWord_579135, baseEnd_579135] using wordTrace_append hprefix tailTrace_579135
  have hstable : (prefixWord ++ tailWord_579135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579135).length < 2 ^ (prefixWord ++ tailWord_579135).sum := by decide
  have hdescent : baseEnd_579135 < baseStart_579135 := by decide
  rcases family_descends (prefixWord ++ tailWord_579135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579165 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 4]
def baseStart_579165 : Nat := 118140960795 + 579165 * 2 ^ 59
def prefixEnd_579165 : Nat := 4983230072969 + 3 ^ 40 * 579165 * 2
def baseEnd_579165 : Nat := 264346687343405998199089

theorem tailTrace_579165 : CollatzResearch.WordTrace tailWord_579165 prefixEnd_579165 264346687343405998199089 := by
  unfold tailWord_579165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21123882946791593352202949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14082588631194395568135299 21123882946791593352202949)
  ·
    refine ⟨3960728052523423753538053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21123882946791593352202949 3960728052523423753538053)
    ·
      refine ⟨742636509848141953788385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3960728052523423753538053 742636509848141953788385)
      ·
        refine ⟨556977382386106465341289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742636509848141953788385 556977382386106465341289)
        ·
          refine ⟨417733036789579849005967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 556977382386106465341289 417733036789579849005967)
          ·
            refine ⟨626599555184369773508951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417733036789579849005967 626599555184369773508951)
            ·
              refine ⟨939899332776554660263427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626599555184369773508951 939899332776554660263427)
              ·
                refine ⟨1409848999164831990395141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939899332776554660263427 1409848999164831990395141)
                ·
                  refine ⟨264346687343405998199089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409848999164831990395141 264346687343405998199089)
                  ·
                    rfl

theorem cell20_579165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_579165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579165 prefixEnd_579165 := by exact prefixLift 579165
  have htrace : WordTrace (prefixWord ++ tailWord_579165) baseStart_579165 baseEnd_579165 := by
    simpa [prefixWord, tailWord_579165, baseEnd_579165] using wordTrace_append hprefix tailTrace_579165
  have hstable : (prefixWord ++ tailWord_579165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579165).length < 2 ^ (prefixWord ++ tailWord_579165).sum := by decide
  have hdescent : baseEnd_579165 < baseStart_579165 := by decide
  rcases family_descends (prefixWord ++ tailWord_579165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579169 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 2]
def baseStart_579169 : Nat := 118140960795 + 579169 * 2 ^ 59
def prefixEnd_579169 : Nat := 4983230072969 + 3 ^ 40 * 579169 * 2
def baseEnd_579169 : Nat := 264348513052399762065739

theorem tailTrace_579169 : CollatzResearch.WordTrace tailWord_579169 prefixEnd_579169 264348513052399762065739 := by
  unfold tailWord_579169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21124028838777102035348561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14082685892518068023565707 21124028838777102035348561)
  ·
    refine ⟨15843021629082826526511421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21124028838777102035348561 15843021629082826526511421)
    ·
      refine ⟨5941133110906059947441783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15843021629082826526511421 5941133110906059947441783)
      ·
        refine ⟨8911699666359089921162675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941133110906059947441783 8911699666359089921162675)
        ·
          refine ⟨13367549499538634881744013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8911699666359089921162675 13367549499538634881744013)
          ·
            refine ⟨5012831062326988080654005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13367549499538634881744013 5012831062326988080654005)
            ·
              refine ⟨469952912093155132561313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5012831062326988080654005 469952912093155132561313)
              ·
                refine ⟨352464684069866349420985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469952912093155132561313 352464684069866349420985)
                ·
                  refine ⟨264348513052399762065739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352464684069866349420985 264348513052399762065739)
                  ·
                    rfl

theorem cell20_579169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_579169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579169 prefixEnd_579169 := by exact prefixLift 579169
  have htrace : WordTrace (prefixWord ++ tailWord_579169) baseStart_579169 baseEnd_579169 := by
    simpa [prefixWord, tailWord_579169, baseEnd_579169] using wordTrace_append hprefix tailTrace_579169
  have hstable : (prefixWord ++ tailWord_579169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579169).length < 2 ^ (prefixWord ++ tailWord_579169).sum := by decide
  have hdescent : baseEnd_579169 < baseStart_579169 := by decide
  rcases family_descends (prefixWord ++ tailWord_579169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579218 : List Nat := [3, 2, 3, 1, 11]
def baseStart_579218 : Nat := 118140960795 + 579218 * 2 ^ 59
def prefixEnd_579218 : Nat := 4983230072969 + 3 ^ 40 * 579218 * 2
def baseEnd_579218 : Nat := 3263837999846584807805

theorem tailTrace_579218 : CollatzResearch.WordTrace tailWord_579218 prefixEnd_579218 3263837999846584807805 := by
  unfold tailWord_579218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281454003899895850970577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14083877343733055602588205 5281454003899895850970577)
  ·
    refine ⟨3961090502924921888227933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5281454003899895850970577 3961090502924921888227933)
    ·
      refine ⟨1485408938596845708085475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3961090502924921888227933 1485408938596845708085475)
      ·
        refine ⟨2228113407895268562128213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485408938596845708085475 2228113407895268562128213)
        ·
          refine ⟨3263837999846584807805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2228113407895268562128213 3263837999846584807805)
          ·
            rfl

theorem cell20_579218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 11].length) (baseStart_579218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579218 prefixEnd_579218 := by exact prefixLift 579218
  have htrace : WordTrace (prefixWord ++ tailWord_579218) baseStart_579218 baseEnd_579218 := by
    simpa [prefixWord, tailWord_579218, baseEnd_579218] using wordTrace_append hprefix tailTrace_579218
  have hstable : (prefixWord ++ tailWord_579218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579218).length < 2 ^ (prefixWord ++ tailWord_579218).sum := by decide
  have hdescent : baseEnd_579218 < baseStart_579218 := by decide
  rcases family_descends (prefixWord ++ tailWord_579218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579220 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 2]
def baseStart_579220 : Nat := 118140960795 + 579220 * 2 ^ 59
def prefixEnd_579220 : Nat := 4983230072969 + 3 ^ 40 * 579220 * 2
def baseEnd_579220 : Nat := 264371790842070251365531

theorem tailTrace_579220 : CollatzResearch.WordTrace tailWord_579220 prefixEnd_579220 264371790842070251365531 := by
  unfold tailWord_579220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10562944480796168872727557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14083925974394891830303409 10562944480796168872727557)
  ·
    refine ⟨1980552090149281663636417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10562944480796168872727557 1980552090149281663636417)
    ·
      refine ⟨1485414067611961247727313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1980552090149281663636417 1485414067611961247727313)
      ·
        refine ⟨1114060550708970935795485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1485414067611961247727313 1114060550708970935795485)
        ·
          refine ⟨417772706515864100923307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1114060550708970935795485 417772706515864100923307)
          ·
            refine ⟨626659059773796151384961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417772706515864100923307 626659059773796151384961)
            ·
              refine ⟨469994294830347113538721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626659059773796151384961 469994294830347113538721)
              ·
                refine ⟨352495721122760335154041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469994294830347113538721 352495721122760335154041)
                ·
                  refine ⟨264371790842070251365531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352495721122760335154041 264371790842070251365531)
                  ·
                    rfl

theorem cell20_579220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_579220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579220 prefixEnd_579220 := by exact prefixLift 579220
  have htrace : WordTrace (prefixWord ++ tailWord_579220) baseStart_579220 baseEnd_579220 := by
    simpa [prefixWord, tailWord_579220, baseEnd_579220] using wordTrace_append hprefix tailTrace_579220
  have hstable : (prefixWord ++ tailWord_579220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579220).length < 2 ^ (prefixWord ++ tailWord_579220).sum := by decide
  have hdescent : baseEnd_579220 < baseStart_579220 := by decide
  rcases family_descends (prefixWord ++ tailWord_579220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579224 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 2]
def baseStart_579224 : Nat := 118140960795 + 579224 * 2 ^ 59
def prefixEnd_579224 : Nat := 4983230072969 + 3 ^ 40 * 579224 * 2
def baseEnd_579224 : Nat := 264373616551064015232181

theorem tailTrace_579224 : CollatzResearch.WordTrace tailWord_579224 prefixEnd_579224 264373616551064015232181 := by
  unfold tailWord_579224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563017426788923214300363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14084023235718564285733817 10563017426788923214300363)
  ·
    refine ⟨15844526140183384821450545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10563017426788923214300363 15844526140183384821450545)
    ·
      refine ⟨11883394605137538616087909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15844526140183384821450545 11883394605137538616087909)
      ·
        refine ⟨2228136488463288490516483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11883394605137538616087909 2228136488463288490516483)
        ·
          refine ⟨3342204732694932735774725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228136488463288490516483 3342204732694932735774725)
          ·
            refine ⟨626663387380299887957761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3342204732694932735774725 626663387380299887957761)
            ·
              refine ⟨469997540535224915968321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626663387380299887957761 469997540535224915968321)
              ·
                refine ⟨352498155401418686976241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469997540535224915968321 352498155401418686976241)
                ·
                  refine ⟨264373616551064015232181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352498155401418686976241 264373616551064015232181)
                  ·
                    rfl

theorem cell20_579224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_579224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579224 prefixEnd_579224 := by exact prefixLift 579224
  have htrace : WordTrace (prefixWord ++ tailWord_579224) baseStart_579224 baseEnd_579224 := by
    simpa [prefixWord, tailWord_579224, baseEnd_579224] using wordTrace_append hprefix tailTrace_579224
  have hstable : (prefixWord ++ tailWord_579224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579224).length < 2 ^ (prefixWord ++ tailWord_579224).sum := by decide
  have hdescent : baseEnd_579224 < baseStart_579224 := by decide
  rcases family_descends (prefixWord ++ tailWord_579224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579231 : List Nat := [1, 1, 2, 7, 2, 1, 1, 5]
def baseStart_579231 : Nat := 118140960795 + 579231 * 2 ^ 59
def prefixEnd_579231 : Nat := 4983230072969 + 3 ^ 40 * 579231 * 2
def baseEnd_579231 : Nat := 88125603847267700666273

theorem tailTrace_579231 : CollatzResearch.WordTrace tailWord_579231 prefixEnd_579231 88125603847267700666273 := by
  unfold tailWord_579231
  simp only [CollatzResearch.WordTrace]
  refine ⟨21126290164552486624105547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14084193443034991082737031 21126290164552486624105547)
  ·
    refine ⟨31689435246828729936158321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21126290164552486624105547 31689435246828729936158321)
    ·
      refine ⟨23767076435121547452118741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31689435246828729936158321 23767076435121547452118741)
      ·
        refine ⟨557040853948161268409033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 23767076435121547452118741 557040853948161268409033)
        ·
          refine ⟨417780640461120951306775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557040853948161268409033 417780640461120951306775)
          ·
            refine ⟨626670960691681426960163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417780640461120951306775 626670960691681426960163)
            ·
              refine ⟨940006441037522140440245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626670960691681426960163 940006441037522140440245)
              ·
                refine ⟨88125603847267700666273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 940006441037522140440245 88125603847267700666273)
                ·
                  rfl

theorem cell20_579231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].length) (baseStart_579231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579231 prefixEnd_579231 := by exact prefixLift 579231
  have htrace : WordTrace (prefixWord ++ tailWord_579231) baseStart_579231 baseEnd_579231 := by
    simpa [prefixWord, tailWord_579231, baseEnd_579231] using wordTrace_append hprefix tailTrace_579231
  have hstable : (prefixWord ++ tailWord_579231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579231).length < 2 ^ (prefixWord ++ tailWord_579231).sum := by decide
  have hdescent : baseEnd_579231 < baseStart_579231 := by decide
  rcases family_descends (prefixWord ++ tailWord_579231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579263 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_579263 : Nat := 118140960795 + 579263 * 2 ^ 59
def prefixEnd_579263 : Nat := 4983230072969 + 3 ^ 40 * 579263 * 2
def baseEnd_579263 : Nat := 264391417213753212932021

theorem tailTrace_579263 : CollatzResearch.WordTrace tailWord_579263 prefixEnd_579263 264391417213753212932021 := by
  unfold tailWord_579263
  simp only [CollatzResearch.WordTrace]
  refine ⟨21127457300436556089270443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14084971533624370726180295 21127457300436556089270443)
  ·
    refine ⟨31691185950654834133905665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21127457300436556089270443 31691185950654834133905665)
    ·
      refine ⟨23768389462991125600429249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31691185950654834133905665 23768389462991125600429249)
      ·
        refine ⟨17826292097243344200321937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23768389462991125600429249 17826292097243344200321937)
        ·
          refine ⟨13369719072932508150241453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17826292097243344200321937 13369719072932508150241453)
          ·
            refine ⟨5013644652349690556340545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13369719072932508150241453 5013644652349690556340545)
            ·
              refine ⟨3760233489262267917255409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5013644652349690556340545 3760233489262267917255409)
              ·
                refine ⟨2820175116946700937941557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3760233489262267917255409 2820175116946700937941557)
                ·
                  refine ⟨264391417213753212932021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820175116946700937941557 264391417213753212932021)
                  ·
                    rfl

theorem cell20_579263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_579263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579263 prefixEnd_579263 := by exact prefixLift 579263
  have htrace : WordTrace (prefixWord ++ tailWord_579263) baseStart_579263 baseEnd_579263 := by
    simpa [prefixWord, tailWord_579263, baseEnd_579263] using wordTrace_append hprefix tailTrace_579263
  have hstable : (prefixWord ++ tailWord_579263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579263).length < 2 ^ (prefixWord ++ tailWord_579263).sum := by decide
  have hdescent : baseEnd_579263 < baseStart_579263 := by decide
  rcases family_descends (prefixWord ++ tailWord_579263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579276 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_579276 : Nat := 118140960795 + 579276 * 2 ^ 59
def prefixEnd_579276 : Nat := 4983230072969 + 3 ^ 40 * 579276 * 2
def baseEnd_579276 : Nat := 264397350767982945498635

theorem tailTrace_579276 : CollatzResearch.WordTrace tailWord_579276 prefixEnd_579276 264397350767982945498635 := by
  unfold tailWord_579276
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563965724694729654746841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14085287632926306206329121 10563965724694729654746841)
  ·
    refine ⟨7922974293521047241060131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10563965724694729654746841 7922974293521047241060131)
    ·
      refine ⟨11884461440281570861590197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922974293521047241060131 11884461440281570861590197)
      ·
        refine ⟨1114168260026397268274081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11884461440281570861590197 1114168260026397268274081)
        ·
          refine ⟨835626195019797951205561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114168260026397268274081 835626195019797951205561)
          ·
            refine ⟨626719646264848463404171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835626195019797951205561 626719646264848463404171)
            ·
              refine ⟨940079469397272695106257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626719646264848463404171 940079469397272695106257)
              ·
                refine ⟨705059602047954521329693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940079469397272695106257 705059602047954521329693)
                ·
                  refine ⟨264397350767982945498635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705059602047954521329693 264397350767982945498635)
                  ·
                    rfl

theorem cell20_579276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_579276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579276 prefixEnd_579276 := by exact prefixLift 579276
  have htrace : WordTrace (prefixWord ++ tailWord_579276) baseStart_579276 baseEnd_579276 := by
    simpa [prefixWord, tailWord_579276, baseEnd_579276] using wordTrace_append hprefix tailTrace_579276
  have hstable : (prefixWord ++ tailWord_579276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579276).length < 2 ^ (prefixWord ++ tailWord_579276).sum := by decide
  have hdescent : baseEnd_579276 < baseStart_579276 := by decide
  rcases family_descends (prefixWord ++ tailWord_579276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579287 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_579287 : Nat := 118140960795 + 579287 * 2 ^ 59
def prefixEnd_579287 : Nat := 4983230072969 + 3 ^ 40 * 579287 * 2
def baseEnd_579287 : Nat := 264402371467715796131923

theorem tailTrace_579287 : CollatzResearch.WordTrace tailWord_579287 prefixEnd_579287 264402371467715796131923 := by
  unfold tailWord_579287
  simp only [CollatzResearch.WordTrace]
  refine ⟨21128332652349608188144115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14085555101566405458762743 21128332652349608188144115)
  ·
    refine ⟨31692498978524412282216173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21128332652349608188144115 31692498978524412282216173)
    ·
      refine ⟨11884687116946654605831065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31692498978524412282216173 11884687116946654605831065)
      ·
        refine ⟨8913515337709990954373299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11884687116946654605831065 8913515337709990954373299)
        ·
          refine ⟨13370273006564986431559949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8913515337709990954373299 13370273006564986431559949)
          ·
            refine ⟨5013852377461869911834981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13370273006564986431559949 5013852377461869911834981)
            ·
              refine ⟨940097320774100608469059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5013852377461869911834981 940097320774100608469059)
              ·
                refine ⟨1410145981161150912703589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940097320774100608469059 1410145981161150912703589)
                ·
                  refine ⟨264402371467715796131923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410145981161150912703589 264402371467715796131923)
                  ·
                    rfl

theorem cell20_579287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_579287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579287 prefixEnd_579287 := by exact prefixLift 579287
  have htrace : WordTrace (prefixWord ++ tailWord_579287) baseStart_579287 baseEnd_579287 := by
    simpa [prefixWord, tailWord_579287, baseEnd_579287] using wordTrace_append hprefix tailTrace_579287
  have hstable : (prefixWord ++ tailWord_579287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579287).length < 2 ^ (prefixWord ++ tailWord_579287).sum := by decide
  have hdescent : baseEnd_579287 < baseStart_579287 := by decide
  rcases family_descends (prefixWord ++ tailWord_579287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579293 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 3]
def baseStart_579293 : Nat := 118140960795 + 579293 * 2 ^ 59
def prefixEnd_579293 : Nat := 4983230072969 + 3 ^ 40 * 579293 * 2
def baseEnd_579293 : Nat := 264405110031206441931899

theorem tailTrace_579293 : CollatzResearch.WordTrace tailWord_579293 prefixEnd_579293 264405110031206441931899 := by
  unfold tailWord_579293
  simp only [CollatzResearch.WordTrace]
  refine ⟨21128551490327871212862533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14085700993551914141908355 21128551490327871212862533)
  ·
    refine ⟨3961603404436475852411725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21128551490327871212862533 3961603404436475852411725)
    ·
      refine ⟨1485601276663678444654397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3961603404436475852411725 1485601276663678444654397)
      ·
        refine ⟨557100478748879416745399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1485601276663678444654397 557100478748879416745399)
        ·
          refine ⟨835650718123319125118099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557100478748879416745399 835650718123319125118099)
          ·
            refine ⟨1253476077184978687677149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835650718123319125118099 1253476077184978687677149)
            ·
              refine ⟨470053528944367007878931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1253476077184978687677149 470053528944367007878931)
              ·
                refine ⟨705080293416550511818397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470053528944367007878931 705080293416550511818397)
                ·
                  refine ⟨264405110031206441931899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705080293416550511818397 264405110031206441931899)
                  ·
                    rfl

theorem cell20_579293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_579293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579293 prefixEnd_579293 := by exact prefixLift 579293
  have htrace : WordTrace (prefixWord ++ tailWord_579293) baseStart_579293 baseEnd_579293 := by
    simpa [prefixWord, tailWord_579293, baseEnd_579293] using wordTrace_append hprefix tailTrace_579293
  have hstable : (prefixWord ++ tailWord_579293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579293).length < 2 ^ (prefixWord ++ tailWord_579293).sum := by decide
  have hdescent : baseEnd_579293 < baseStart_579293 := by decide
  rcases family_descends (prefixWord ++ tailWord_579293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579318 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_579318 : Nat := 118140960795 + 579318 * 2 ^ 59
def prefixEnd_579318 : Nat := 4983230072969 + 3 ^ 40 * 579318 * 2
def baseEnd_579318 : Nat := 264416520712417466098463

theorem tailTrace_579318 : CollatzResearch.WordTrace tailWord_579318 prefixEnd_579318 264416520712417466098463 := by
  unfold tailWord_579318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320591457202331280157663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14086308876824866988348405 1320591457202331280157663)
  ·
    refine ⟨1980887185803496920236495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320591457202331280157663 1980887185803496920236495)
    ·
      refine ⟨2971330778705245380354743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980887185803496920236495 2971330778705245380354743)
      ·
        refine ⟨4456996168057868070532115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971330778705245380354743 4456996168057868070532115)
        ·
          refine ⟨6685494252086802105798173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456996168057868070532115 6685494252086802105798173)
          ·
            refine ⟨2507060344532550789674315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6685494252086802105798173 2507060344532550789674315)
            ·
              refine ⟨3760590516798826184511473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507060344532550789674315 3760590516798826184511473)
              ·
                refine ⟨2820442887599119638383605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3760590516798826184511473 2820442887599119638383605)
                ·
                  refine ⟨264416520712417466098463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820442887599119638383605 264416520712417466098463)
                  ·
                    rfl

theorem cell20_579318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_579318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579318 prefixEnd_579318 := by exact prefixLift 579318
  have htrace : WordTrace (prefixWord ++ tailWord_579318) baseStart_579318 baseEnd_579318 := by
    simpa [prefixWord, tailWord_579318, baseEnd_579318] using wordTrace_append hprefix tailTrace_579318
  have hstable : (prefixWord ++ tailWord_579318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579318).length < 2 ^ (prefixWord ++ tailWord_579318).sum := by decide
  have hdescent : baseEnd_579318 < baseStart_579318 := by decide
  rcases family_descends (prefixWord ++ tailWord_579318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579332 : List Nat := [2, 3, 2, 2, 1, 2, 8]
def baseStart_579332 : Nat := 118140960795 + 579332 * 2 ^ 59
def prefixEnd_579332 : Nat := 4983230072969 + 3 ^ 40 * 579332 * 2
def baseEnd_579332 : Nat := 29380323410432848847971

theorem tailTrace_579332 : CollatzResearch.WordTrace tailWord_579332 prefixEnd_579332 29380323410432848847971 := by
  unfold tailWord_579332
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564986968593290436766125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14086649291457720582354833 10564986968593290436766125)
  ·
    refine ⟨3961870113222483913787297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10564986968593290436766125 3961870113222483913787297)
    ·
      refine ⟨2971402584916862935340473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3961870113222483913787297 2971402584916862935340473)
      ·
        refine ⟨2228551938687647201505355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2971402584916862935340473 2228551938687647201505355)
        ·
          refine ⟨3342827908031470802258033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228551938687647201505355 3342827908031470802258033)
          ·
            refine ⟨2507120931023603101693525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342827908031470802258033 2507120931023603101693525)
            ·
              refine ⟨29380323410432848847971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2507120931023603101693525 29380323410432848847971)
              ·
                rfl

theorem cell20_579332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_579332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579332 prefixEnd_579332 := by exact prefixLift 579332
  have htrace : WordTrace (prefixWord ++ tailWord_579332) baseStart_579332 baseEnd_579332 := by
    simpa [prefixWord, tailWord_579332, baseEnd_579332] using wordTrace_append hprefix tailTrace_579332
  have hstable : (prefixWord ++ tailWord_579332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579332).length < 2 ^ (prefixWord ++ tailWord_579332).sum := by decide
  have hdescent : baseEnd_579332 < baseStart_579332 := by decide
  rcases family_descends (prefixWord ++ tailWord_579332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579339 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_579339 : Nat := 118140960795 + 579339 * 2 ^ 59
def prefixEnd_579339 : Nat := 4983230072969 + 3 ^ 40 * 579339 * 2
def baseEnd_579339 : Nat := 264426105684634726398377

theorem tailTrace_579339 : CollatzResearch.WordTrace tailWord_579339 prefixEnd_579339 264426105684634726398377 := by
  unfold tailWord_579339
  simp only [CollatzResearch.WordTrace]
  refine ⟨21130229248161221069037071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14086819498774147379358047 21130229248161221069037071)
  ·
    refine ⟨31695343872241831603555607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21130229248161221069037071 31695343872241831603555607)
    ·
      refine ⟨47543015808362747405333411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31695343872241831603555607 47543015808362747405333411)
      ·
        refine ⟨71314523712544121108000117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47543015808362747405333411 71314523712544121108000117)
        ·
          refine ⟨6685736598051011353875011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71314523712544121108000117 6685736598051011353875011)
          ·
            refine ⟨10028604897076517030812517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6685736598051011353875011 10028604897076517030812517)
            ·
              refine ⟨1880363418201846943277347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10028604897076517030812517 1880363418201846943277347)
              ·
                refine ⟨2820545127302770414916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880363418201846943277347 2820545127302770414916021)
                ·
                  refine ⟨264426105684634726398377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820545127302770414916021 264426105684634726398377)
                  ·
                    rfl

theorem cell20_579339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_579339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579339 prefixEnd_579339 := by exact prefixLift 579339
  have htrace : WordTrace (prefixWord ++ tailWord_579339) baseStart_579339 baseEnd_579339 := by
    simpa [prefixWord, tailWord_579339, baseEnd_579339] using wordTrace_append hprefix tailTrace_579339
  have hstable : (prefixWord ++ tailWord_579339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579339).length < 2 ^ (prefixWord ++ tailWord_579339).sum := by decide
  have hdescent : baseEnd_579339 < baseStart_579339 := by decide
  rcases family_descends (prefixWord ++ tailWord_579339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579342 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_579342 : Nat := 118140960795 + 579342 * 2 ^ 59
def prefixEnd_579342 : Nat := 4983230072969 + 3 ^ 40 * 579342 * 2
def baseEnd_579342 : Nat := 264427474966380049298365

theorem tailTrace_579342 : CollatzResearch.WordTrace tailWord_579342 prefixEnd_579342 264427474966380049298365 := by
  unfold tailWord_579342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641292333393794072674535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14086892444766901720930853 2641292333393794072674535)
  ·
    refine ⟨3961938500090691109011803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2641292333393794072674535 3961938500090691109011803)
    ·
      refine ⟨5942907750136036663517705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3961938500090691109011803 5942907750136036663517705)
      ·
        refine ⟨4457180812602027497638279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5942907750136036663517705 4457180812602027497638279)
        ·
          refine ⟨6685771218903041246457419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457180812602027497638279 6685771218903041246457419)
          ·
            refine ⟨10028656828354561869686129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6685771218903041246457419 10028656828354561869686129)
            ·
              refine ⟨7521492621265921402264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10028656828354561869686129 7521492621265921402264597)
              ·
                refine ⟨352569966621840065731153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7521492621265921402264597 352569966621840065731153)
                ·
                  refine ⟨264427474966380049298365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352569966621840065731153 264427474966380049298365)
                  ·
                    rfl

theorem cell20_579342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_579342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579342 prefixEnd_579342 := by exact prefixLift 579342
  have htrace : WordTrace (prefixWord ++ tailWord_579342) baseStart_579342 baseEnd_579342 := by
    simpa [prefixWord, tailWord_579342, baseEnd_579342] using wordTrace_append hprefix tailTrace_579342
  have hstable : (prefixWord ++ tailWord_579342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579342).length < 2 ^ (prefixWord ++ tailWord_579342).sum := by decide
  have hdescent : baseEnd_579342 < baseStart_579342 := by decide
  rcases family_descends (prefixWord ++ tailWord_579342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579356 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_579356 : Nat := 118140960795 + 579356 * 2 ^ 59
def prefixEnd_579356 : Nat := 4983230072969 + 3 ^ 40 * 579356 * 2
def baseEnd_579356 : Nat := 264433864947858222831641

theorem tailTrace_579356 : CollatzResearch.WordTrace tailWord_579356 prefixEnd_579356 264433864947858222831641 := by
  unfold tailWord_579356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10565424644549816486202961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14087232859399755314937281 10565424644549816486202961)
  ·
    refine ⟨7924068483412362364652221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10565424644549816486202961 7924068483412362364652221)
    ·
      refine ⟨2971525681279635886744583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7924068483412362364652221 2971525681279635886744583)
      ·
        refine ⟨4457288521919453830116875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971525681279635886744583 4457288521919453830116875)
        ·
          refine ⟨6685932782879180745175313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457288521919453830116875 6685932782879180745175313)
          ·
            refine ⟨5014449587159385558881485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6685932782879180745175313 5014449587159385558881485)
            ·
              refine ⟨1880418595184769584580557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5014449587159385558881485 1880418595184769584580557)
              ·
                refine ⟨705156973194288594217709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1880418595184769584580557 705156973194288594217709)
                ·
                  refine ⟨264433864947858222831641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705156973194288594217709 264433864947858222831641)
                  ·
                    rfl

theorem cell20_579356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_579356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579356 prefixEnd_579356 := by exact prefixLift 579356
  have htrace : WordTrace (prefixWord ++ tailWord_579356) baseStart_579356 baseEnd_579356 := by
    simpa [prefixWord, tailWord_579356, baseEnd_579356] using wordTrace_append hprefix tailTrace_579356
  have hstable : (prefixWord ++ tailWord_579356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579356).length < 2 ^ (prefixWord ++ tailWord_579356).sum := by decide
  have hdescent : baseEnd_579356 < baseStart_579356 := by decide
  rcases family_descends (prefixWord ++ tailWord_579356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579391 : List Nat := [1, 1, 2, 2, 14]
def baseStart_579391 : Nat := 118140960795 + 579391 * 2 ^ 59
def prefixEnd_579391 : Nat := 4983230072969 + 3 ^ 40 * 579391 * 2
def baseEnd_579391 : Nat := 3264812838290785884751

theorem tailTrace_579391 : CollatzResearch.WordTrace tailWord_579391 prefixEnd_579391 3264812838290785884751 := by
  unfold tailWord_579391
  simp only [CollatzResearch.WordTrace]
  refine ⟨21132125843972833949930027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14088083895981889299953351 21132125843972833949930027)
  ·
    refine ⟨31698188765959250924895041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21132125843972833949930027 31698188765959250924895041)
    ·
      refine ⟨23773641574469438193671281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31698188765959250924895041 23773641574469438193671281)
      ·
        refine ⟨17830231180852078645253461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23773641574469438193671281 17830231180852078645253461)
        ·
          refine ⟨3264812838290785884751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 17830231180852078645253461 3264812838290785884751)
          ·
            rfl

theorem cell20_579391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 14].length) (baseStart_579391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579391 prefixEnd_579391 := by exact prefixLift 579391
  have htrace : WordTrace (prefixWord ++ tailWord_579391) baseStart_579391 baseEnd_579391 := by
    simpa [prefixWord, tailWord_579391, baseEnd_579391] using wordTrace_append hprefix tailTrace_579391
  have hstable : (prefixWord ++ tailWord_579391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579391).length < 2 ^ (prefixWord ++ tailWord_579391).sum := by decide
  have hdescent : baseEnd_579391 < baseStart_579391 := by decide
  rcases family_descends (prefixWord ++ tailWord_579391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579404 : List Nat := [2, 2, 1, 3, 5, 1, 1, 5]
def baseStart_579404 : Nat := 118140960795 + 579404 * 2 ^ 59
def prefixEnd_579404 : Nat := 4983230072969 + 3 ^ 40 * 579404 * 2
def baseEnd_579404 : Nat := 88151924485261129743815

theorem tailTrace_579404 : CollatzResearch.WordTrace tailWord_579404 prefixEnd_579404 88151924485261129743815 := by
  unfold tailWord_579404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10566299996462868585076633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14088399995283824780102177 10566299996462868585076633)
  ·
    refine ⟨7924724997347151438807475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10566299996462868585076633 7924724997347151438807475)
    ·
      refine ⟨11887087496020727158211213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7924724997347151438807475 11887087496020727158211213)
      ·
        refine ⟨4457657811007772684329205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11887087496020727158211213 4457657811007772684329205)
        ·
          refine ⟨417905419781978689155863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4457657811007772684329205 417905419781978689155863)
          ·
            refine ⟨626858129672968033733795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417905419781978689155863 626858129672968033733795)
            ·
              refine ⟨940287194509452050600693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626858129672968033733795 940287194509452050600693)
              ·
                refine ⟨88151924485261129743815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 940287194509452050600693 88151924485261129743815)
                ·
                  rfl

theorem cell20_579404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_579404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579404 prefixEnd_579404 := by exact prefixLift 579404
  have htrace : WordTrace (prefixWord ++ tailWord_579404) baseStart_579404 baseEnd_579404 := by
    simpa [prefixWord, tailWord_579404, baseEnd_579404] using wordTrace_append hprefix tailTrace_579404
  have hstable : (prefixWord ++ tailWord_579404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579404).length < 2 ^ (prefixWord ++ tailWord_579404).sum := by decide
  have hdescent : baseEnd_579404 < baseStart_579404 := by decide
  rcases family_descends (prefixWord ++ tailWord_579404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579466 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_579466 : Nat := 118140960795 + 579466 * 2 ^ 59
def prefixEnd_579466 : Nat := 4983230072969 + 3 ^ 40 * 579466 * 2
def baseEnd_579466 : Nat := 264484071945186729164525

theorem tailTrace_579466 : CollatzResearch.WordTrace tailWord_579466 prefixEnd_579466 264484071945186729164525 := by
  unfold tailWord_579466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283715329675280439727563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14089907545800747839273501 5283715329675280439727563)
  ·
    refine ⟨7925572994512920659591345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5283715329675280439727563 7925572994512920659591345)
    ·
      refine ⟨5944179745884690494693509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7925572994512920659591345 5944179745884690494693509)
      ·
        refine ⟨1114533702353379467755033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5944179745884690494693509 1114533702353379467755033)
        ·
          refine ⟨835900276765034600816275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114533702353379467755033 835900276765034600816275)
          ·
            refine ⟨1253850415147551901224413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835900276765034600816275 1253850415147551901224413)
            ·
              refine ⟨470193905680331962959155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1253850415147551901224413 470193905680331962959155)
              ·
                refine ⟨705290858520497944438733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470193905680331962959155 705290858520497944438733)
                ·
                  refine ⟨264484071945186729164525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705290858520497944438733 264484071945186729164525)
                  ·
                    rfl

theorem cell20_579466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_579466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579466 prefixEnd_579466 := by exact prefixLift 579466
  have htrace : WordTrace (prefixWord ++ tailWord_579466) baseStart_579466 baseEnd_579466 := by
    simpa [prefixWord, tailWord_579466, baseEnd_579466] using wordTrace_append hprefix tailTrace_579466
  have hstable : (prefixWord ++ tailWord_579466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579466).length < 2 ^ (prefixWord ++ tailWord_579466).sum := by decide
  have hdescent : baseEnd_579466 < baseStart_579466 := by decide
  rcases family_descends (prefixWord ++ tailWord_579466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579467 : List Nat := [1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_579467 : Nat := 118140960795 + 579467 * 2 ^ 59
def prefixEnd_579467 : Nat := 4983230072969 + 3 ^ 40 * 579467 * 2
def baseEnd_579467 : Nat := 88161509457478390043729

theorem tailTrace_579467 : CollatzResearch.WordTrace tailWord_579467 prefixEnd_579467 88161509457478390043729 := by
  unfold tailWord_579467
  simp only [CollatzResearch.WordTrace]
  refine ⟨21134897791697498929696655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14089931861131665953131103 21134897791697498929696655)
  ·
    refine ⟨31702346687546248394544983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21134897791697498929696655 31702346687546248394544983)
    ·
      refine ⟨47553520031319372591817475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31702346687546248394544983 47553520031319372591817475)
      ·
        refine ⟨71330280046979058887726213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47553520031319372591817475 71330280046979058887726213)
        ·
          refine ⟨13374427508808573541448665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71330280046979058887726213 13374427508808573541448665)
          ·
            refine ⟨10030820631606430156086499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13374427508808573541448665 10030820631606430156086499)
            ·
              refine ⟨15046230947409645234129749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10030820631606430156086499 15046230947409645234129749)
              ·
                refine ⟨88161509457478390043729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15046230947409645234129749 88161509457478390043729)
                ·
                  rfl

theorem cell20_579467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_579467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579467 prefixEnd_579467 := by exact prefixLift 579467
  have htrace : WordTrace (prefixWord ++ tailWord_579467) baseStart_579467 baseEnd_579467 := by
    simpa [prefixWord, tailWord_579467, baseEnd_579467] using wordTrace_append hprefix tailTrace_579467
  have hstable : (prefixWord ++ tailWord_579467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579467).length < 2 ^ (prefixWord ++ tailWord_579467).sum := by decide
  have hdescent : baseEnd_579467 < baseStart_579467 := by decide
  rcases family_descends (prefixWord ++ tailWord_579467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579486 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_579486 : Nat := 118140960795 + 579486 * 2 ^ 59
def prefixEnd_579486 : Nat := 4983230072969 + 3 ^ 40 * 579486 * 2
def baseEnd_579486 : Nat := 264493200490155548497777

theorem tailTrace_579486 : CollatzResearch.WordTrace tailWord_579486 prefixEnd_579486 264493200490155548497777 := by
  unfold tailWord_579486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641948847328583146829789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14090393852419110116425541 2641948847328583146829789)
  ·
    refine ⟨990730817748218680061171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2641948847328583146829789 990730817748218680061171)
    ·
      refine ⟨1486096226622328020091757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990730817748218680061171 1486096226622328020091757)
      ·
        refine ⟨557286084983373007534409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1486096226622328020091757 557286084983373007534409)
        ·
          refine ⟨417964563737529755650807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557286084983373007534409 417964563737529755650807)
          ·
            refine ⟨626946845606294633476211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417964563737529755650807 626946845606294633476211)
            ·
              refine ⟨940420268409441950214317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626946845606294633476211 940420268409441950214317)
              ·
                refine ⟨352657600653540731330369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940420268409441950214317 352657600653540731330369)
                ·
                  refine ⟨264493200490155548497777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352657600653540731330369 264493200490155548497777)
                  ·
                    rfl

theorem cell20_579486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_579486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579486 prefixEnd_579486 := by exact prefixLift 579486
  have htrace : WordTrace (prefixWord ++ tailWord_579486) baseStart_579486 baseEnd_579486 := by
    simpa [prefixWord, tailWord_579486, baseEnd_579486] using wordTrace_append hprefix tailTrace_579486
  have hstable : (prefixWord ++ tailWord_579486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579486).length < 2 ^ (prefixWord ++ tailWord_579486).sum := by decide
  have hdescent : baseEnd_579486 < baseStart_579486 := by decide
  rcases family_descends (prefixWord ++ tailWord_579486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579490 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_579490 : Nat := 118140960795 + 579490 * 2 ^ 59
def prefixEnd_579490 : Nat := 4983230072969 + 3 ^ 40 * 579490 * 2
def baseEnd_579490 : Nat := 264495026199149312364427

theorem tailTrace_579490 : CollatzResearch.WordTrace tailWord_579490 prefixEnd_579490 264495026199149312364427 := by
  unfold tailWord_579490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283934167653543464445981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14090491113742782571855949 5283934167653543464445981)
  ·
    refine ⟨1981475312870078799167243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5283934167653543464445981 1981475312870078799167243)
    ·
      refine ⟨2972212969305118198750865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981475312870078799167243 2972212969305118198750865)
      ·
        refine ⟨2229159726978838649063149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2972212969305118198750865 2229159726978838649063149)
        ·
          refine ⟨835934897617064493398681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2229159726978838649063149 835934897617064493398681)
          ·
            refine ⟨626951173212798370049011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835934897617064493398681 626951173212798370049011)
            ·
              refine ⟨940426759819197555073517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626951173212798370049011 940426759819197555073517)
              ·
                refine ⟨352660034932199083152569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940426759819197555073517 352660034932199083152569)
                ·
                  refine ⟨264495026199149312364427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352660034932199083152569 264495026199149312364427)
                  ·
                    rfl

theorem cell20_579490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_579490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579490 prefixEnd_579490 := by exact prefixLift 579490
  have htrace : WordTrace (prefixWord ++ tailWord_579490) baseStart_579490 baseEnd_579490 := by
    simpa [prefixWord, tailWord_579490, baseEnd_579490] using wordTrace_append hprefix tailTrace_579490
  have hstable : (prefixWord ++ tailWord_579490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579490).length < 2 ^ (prefixWord ++ tailWord_579490).sum := by decide
  have hdescent : baseEnd_579490 < baseStart_579490 := by decide
  rcases family_descends (prefixWord ++ tailWord_579490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579529 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_579529 : Nat := 118140960795 + 579529 * 2 ^ 59
def prefixEnd_579529 : Nat := 4983230072969 + 3 ^ 40 * 579529 * 2
def baseEnd_579529 : Nat := 264512826861838510064267

theorem tailTrace_579529 : CollatzResearch.WordTrace tailWord_579529 prefixEnd_579529 264512826861838510064267 := by
  unfold tailWord_579529
  simp only [CollatzResearch.WordTrace]
  refine ⟨21137159117472883518453641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14091439411648589012302427 21137159117472883518453641)
  ·
    refine ⟨15852869338104662638840231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21137159117472883518453641 15852869338104662638840231)
    ·
      refine ⟨23779304007156993958260347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15852869338104662638840231 23779304007156993958260347)
      ·
        refine ⟨35668956010735490937390521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23779304007156993958260347 35668956010735490937390521)
        ·
          refine ⟨26751717008051618203042891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35668956010735490937390521 26751717008051618203042891)
          ·
            refine ⟨40127575512077427304564337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26751717008051618203042891 40127575512077427304564337)
            ·
              refine ⟨30095681634058070478423253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40127575512077427304564337 30095681634058070478423253)
              ·
                refine ⟨705367538298236026838045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30095681634058070478423253 705367538298236026838045)
                ·
                  refine ⟨264512826861838510064267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705367538298236026838045 264512826861838510064267)
                  ·
                    rfl

theorem cell20_579529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_579529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579529 prefixEnd_579529 := by exact prefixLift 579529
  have htrace : WordTrace (prefixWord ++ tailWord_579529) baseStart_579529 baseEnd_579529 := by
    simpa [prefixWord, tailWord_579529, baseEnd_579529] using wordTrace_append hprefix tailTrace_579529
  have hstable : (prefixWord ++ tailWord_579529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579529).length < 2 ^ (prefixWord ++ tailWord_579529).sum := by decide
  have hdescent : baseEnd_579529 < baseStart_579529 := by decide
  rcases family_descends (prefixWord ++ tailWord_579529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579536 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_579536 : Nat := 118140960795 + 579536 * 2 ^ 59
def prefixEnd_579536 : Nat := 4983230072969 + 3 ^ 40 * 579536 * 2
def baseEnd_579536 : Nat := 264516021852577596830905

theorem tailTrace_579536 : CollatzResearch.WordTrace tailWord_579536 prefixEnd_579536 264516021852577596830905 := by
  unfold tailWord_579536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10568707214223761856979231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14091609618965015809305641 10568707214223761856979231)
  ·
    refine ⟨15853060821335642785468847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10568707214223761856979231 15853060821335642785468847)
    ·
      refine ⟨23779591232003464178203271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15853060821335642785468847 23779591232003464178203271)
      ·
        refine ⟨35669386848005196267304907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23779591232003464178203271 35669386848005196267304907)
        ·
          refine ⟨53504080272007794400957361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35669386848005196267304907 53504080272007794400957361)
          ·
            refine ⟨40128060204005845800718021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53504080272007794400957361 40128060204005845800718021)
            ·
              refine ⟨7524011288251096087634629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40128060204005845800718021 7524011288251096087634629)
              ·
                refine ⟨1410752116547080516431493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7524011288251096087634629 1410752116547080516431493)
                ·
                  refine ⟨264516021852577596830905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410752116547080516431493 264516021852577596830905)
                  ·
                    rfl

theorem cell20_579536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_579536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579536 prefixEnd_579536 := by exact prefixLift 579536
  have htrace : WordTrace (prefixWord ++ tailWord_579536) baseStart_579536 baseEnd_579536 := by
    simpa [prefixWord, tailWord_579536, baseEnd_579536] using wordTrace_append hprefix tailTrace_579536
  have hstable : (prefixWord ++ tailWord_579536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579536).length < 2 ^ (prefixWord ++ tailWord_579536).sum := by decide
  have hdescent : baseEnd_579536 < baseStart_579536 := by decide
  rcases family_descends (prefixWord ++ tailWord_579536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579543 : List Nat := [1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_579543 : Nat := 118140960795 + 579543 * 2 ^ 59
def prefixEnd_579543 : Nat := 4983230072969 + 3 ^ 40 * 579543 * 2
def baseEnd_579543 : Nat := 88173072281105561199181

theorem tailTrace_579543 : CollatzResearch.WordTrace tailWord_579543 prefixEnd_579543 88173072281105561199181 := by
  unfold tailWord_579543
  simp only [CollatzResearch.WordTrace]
  refine ⟨21137669739422163909463283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14091779826281442606308855 21137669739422163909463283)
  ·
    refine ⟨31706504609133245864194925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21137669739422163909463283 31706504609133245864194925)
    ·
      refine ⟨11889939228424967199073097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31706504609133245864194925 11889939228424967199073097)
      ·
        refine ⟨8917454421318725399304823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11889939228424967199073097 8917454421318725399304823)
        ·
          refine ⟨13376181631978088098957235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8917454421318725399304823 13376181631978088098957235)
          ·
            refine ⟨20064272447967132148435853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13376181631978088098957235 20064272447967132148435853)
            ·
              refine ⟨7524102167987674555663445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20064272447967132148435853 7524102167987674555663445)
              ·
                refine ⟨88173072281105561199181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7524102167987674555663445 88173072281105561199181)
                ·
                  rfl

theorem cell20_579543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_579543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579543 prefixEnd_579543 := by exact prefixLift 579543
  have htrace : WordTrace (prefixWord ++ tailWord_579543) baseStart_579543 baseEnd_579543 := by
    simpa [prefixWord, tailWord_579543, baseEnd_579543] using wordTrace_append hprefix tailTrace_579543
  have hstable : (prefixWord ++ tailWord_579543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579543).length < 2 ^ (prefixWord ++ tailWord_579543).sum := by decide
  have hdescent : baseEnd_579543 < baseStart_579543 := by decide
  rcases family_descends (prefixWord ++ tailWord_579543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579566 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_579566 : Nat := 118140960795 + 579566 * 2 ^ 59
def prefixEnd_579566 : Nat := 4983230072969 + 3 ^ 40 * 579566 * 2
def baseEnd_579566 : Nat := 264529714670030825830783

theorem tailTrace_579566 : CollatzResearch.WordTrace tailWord_579566 prefixEnd_579566 264529714670030825830783 := by
  unfold tailWord_579566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642313577292354854693819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14092339078892559225033701 2642313577292354854693819)
  ·
    refine ⟨3963470365938532282040729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2642313577292354854693819 3963470365938532282040729)
    ·
      refine ⟨2972602774453899211530547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3963470365938532282040729 2972602774453899211530547)
      ·
        refine ⟨4458904161680848817295821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972602774453899211530547 4458904161680848817295821)
        ·
          refine ⟨1672089060630318306485933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4458904161680848817295821 1672089060630318306485933)
          ·
            refine ⟨627033397736369364932225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1672089060630318306485933 627033397736369364932225)
            ·
              refine ⟨470275048302277023699169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627033397736369364932225 470275048302277023699169)
              ·
                refine ⟨352706286226707767774377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470275048302277023699169 352706286226707767774377)
                ·
                  refine ⟨264529714670030825830783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352706286226707767774377 264529714670030825830783)
                  ·
                    rfl

theorem cell20_579566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_579566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579566 prefixEnd_579566 := by exact prefixLift 579566
  have htrace : WordTrace (prefixWord ++ tailWord_579566) baseStart_579566 baseEnd_579566 := by
    simpa [prefixWord, tailWord_579566, baseEnd_579566] using wordTrace_append hprefix tailTrace_579566
  have hstable : (prefixWord ++ tailWord_579566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579566).length < 2 ^ (prefixWord ++ tailWord_579566).sum := by decide
  have hdescent : baseEnd_579566 < baseStart_579566 := by decide
  rcases family_descends (prefixWord ++ tailWord_579566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579591 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_579591 : Nat := 118140960795 + 579591 * 2 ^ 59
def prefixEnd_579591 : Nat := 4983230072969 + 3 ^ 40 * 579591 * 2
def baseEnd_579591 : Nat := 264541125351241849997347

theorem tailTrace_579591 : CollatzResearch.WordTrace tailWord_579591 prefixEnd_579591 264541125351241849997347 := by
  unfold tailWord_579591
  simp only [CollatzResearch.WordTrace]
  refine ⟨21139420443248268107210627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14092946962165512071473751 21139420443248268107210627)
  ·
    refine ⟨31709130664872402160815941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21139420443248268107210627 31709130664872402160815941)
    ·
      refine ⟨5945461999663575405152989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31709130664872402160815941 5945461999663575405152989)
      ·
        refine ⟨2229548249873840776932371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5945461999663575405152989 2229548249873840776932371)
        ·
          refine ⟨3344322374810761165398557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229548249873840776932371 3344322374810761165398557)
          ·
            refine ⟨1254120890554035437024459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3344322374810761165398557 1254120890554035437024459)
            ·
              refine ⟨1881181335831053155536689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254120890554035437024459 1881181335831053155536689)
              ·
                refine ⟨1410886001873289866652517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881181335831053155536689 1410886001873289866652517)
                ·
                  refine ⟨264541125351241849997347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410886001873289866652517 264541125351241849997347)
                  ·
                    rfl

theorem cell20_579591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_579591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579591 prefixEnd_579591 := by exact prefixLift 579591
  have htrace : WordTrace (prefixWord ++ tailWord_579591) baseStart_579591 baseEnd_579591 := by
    simpa [prefixWord, tailWord_579591, baseEnd_579591] using wordTrace_append hprefix tailTrace_579591
  have hstable : (prefixWord ++ tailWord_579591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579591).length < 2 ^ (prefixWord ++ tailWord_579591).sum := by decide
  have hdescent : baseEnd_579591 < baseStart_579591 := by decide
  rcases family_descends (prefixWord ++ tailWord_579591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579608 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 2]
def baseStart_579608 : Nat := 118140960795 + 579608 * 2 ^ 59
def prefixEnd_579608 : Nat := 4983230072969 + 3 ^ 40 * 579608 * 2
def baseEnd_579608 : Nat := 264548884614465346430611

theorem tailTrace_579608 : CollatzResearch.WordTrace tailWord_579608 prefixEnd_579608 264548884614465346430611 := by
  unfold tailWord_579608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10570020242093340005289739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14093360322791120007052985 10570020242093340005289739)
  ·
    refine ⟨15855030363140010007934609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10570020242093340005289739 15855030363140010007934609)
    ·
      refine ⟨11891272772355007505950957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15855030363140010007934609 11891272772355007505950957)
      ·
        refine ⟨4459227289633127814731609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11891272772355007505950957 4459227289633127814731609)
        ·
          refine ⟨3344420467224845861048707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4459227289633127814731609 3344420467224845861048707)
          ·
            refine ⟨5016630700837268791573061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344420467224845861048707 5016630700837268791573061)
            ·
              refine ⟨940618256406987898419949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5016630700837268791573061 940618256406987898419949)
              ·
                refine ⟨352731846152620461907481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940618256406987898419949 352731846152620461907481)
                ·
                  refine ⟨264548884614465346430611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352731846152620461907481 264548884614465346430611)
                  ·
                    rfl

theorem cell20_579608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_579608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579608 prefixEnd_579608 := by exact prefixLift 579608
  have htrace : WordTrace (prefixWord ++ tailWord_579608) baseStart_579608 baseEnd_579608 := by
    simpa [prefixWord, tailWord_579608, baseEnd_579608] using wordTrace_append hprefix tailTrace_579608
  have hstable : (prefixWord ++ tailWord_579608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579608).length < 2 ^ (prefixWord ++ tailWord_579608).sum := by decide
  have hdescent : baseEnd_579608 < baseStart_579608 := by decide
  rcases family_descends (prefixWord ++ tailWord_579608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579619 : List Nat := [1, 1, 1, 4, 3, 1, 9]
def baseStart_579619 : Nat := 118140960795 + 579619 * 2 ^ 59
def prefixEnd_579619 : Nat := 4983230072969 + 3 ^ 40 * 579619 * 2
def baseEnd_579619 : Nat := 29394878368244244118211

theorem tailTrace_579619 : CollatzResearch.WordTrace tailWord_579619 prefixEnd_579619 29394878368244244118211 := by
  unfold tailWord_579619
  simp only [CollatzResearch.WordTrace]
  refine ⟨21140441687146828889229911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14093627791431219259486607 21140441687146828889229911)
  ·
    refine ⟨31710662530720243333844867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21140441687146828889229911 31710662530720243333844867)
    ·
      refine ⟨47565993796080365000767301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31710662530720243333844867 47565993796080365000767301)
      ·
        refine ⟨8918623836765068437643869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47565993796080365000767301 8918623836765068437643869)
        ·
          refine ⟨3344483938786900664116451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8918623836765068437643869 3344483938786900664116451)
          ·
            refine ⟨5016725908180350996174677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344483938786900664116451 5016725908180350996174677)
            ·
              refine ⟨29394878368244244118211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5016725908180350996174677 29394878368244244118211)
              ·
                rfl

theorem cell20_579619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_579619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579619 prefixEnd_579619 := by exact prefixLift 579619
  have htrace : WordTrace (prefixWord ++ tailWord_579619) baseStart_579619 baseEnd_579619 := by
    simpa [prefixWord, tailWord_579619, baseEnd_579619] using wordTrace_append hprefix tailTrace_579619
  have hstable : (prefixWord ++ tailWord_579619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579619).length < 2 ^ (prefixWord ++ tailWord_579619).sum := by decide
  have hdescent : baseEnd_579619 < baseStart_579619 := by decide
  rcases family_descends (prefixWord ++ tailWord_579619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579657 : List Nat := [1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_579657 : Nat := 118140960795 + 579657 * 2 ^ 59
def prefixEnd_579657 : Nat := 4983230072969 + 3 ^ 40 * 579657 * 2
def baseEnd_579657 : Nat := 88190416516546317932359

theorem tailTrace_579657 : CollatzResearch.WordTrace tailWord_579657 prefixEnd_579657 88190416516546317932359 := by
  unfold tailWord_579657
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141827661009161379113225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14094551774006107586075483 21141827661009161379113225)
  ·
    refine ⟨15856370745756871034334919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21141827661009161379113225 15856370745756871034334919)
    ·
      refine ⟨23784556118635306551502379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15856370745756871034334919 23784556118635306551502379)
      ·
        refine ⟨35676834177952959827253569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23784556118635306551502379 35676834177952959827253569)
        ·
          refine ⟨26757625633464719870440177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35676834177952959827253569 26757625633464719870440177)
          ·
            refine ⟨20068219225098539902830133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26757625633464719870440177 20068219225098539902830133)
            ·
              refine ⟨1881395552352988115890325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20068219225098539902830133 1881395552352988115890325)
              ·
                refine ⟨88190416516546317932359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1881395552352988115890325 88190416516546317932359)
                ·
                  rfl

theorem cell20_579657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_579657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579657 prefixEnd_579657 := by exact prefixLift 579657
  have htrace : WordTrace (prefixWord ++ tailWord_579657) baseStart_579657 baseEnd_579657 := by
    simpa [prefixWord, tailWord_579657, baseEnd_579657] using wordTrace_append hprefix tailTrace_579657
  have hstable : (prefixWord ++ tailWord_579657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579657).length < 2 ^ (prefixWord ++ tailWord_579657).sum := by decide
  have hdescent : baseEnd_579657 < baseStart_579657 := by decide
  rcases family_descends (prefixWord ++ tailWord_579657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579670 : List Nat := [5, 2, 2, 1, 1, 3, 6]
def baseStart_579670 : Nat := 118140960795 + 579670 * 2 ^ 59
def prefixEnd_579670 : Nat := 4983230072969 + 3 ^ 40 * 579670 * 2
def baseEnd_579670 : Nat := 29397464789318742929299

theorem tailTrace_579670 : CollatzResearch.WordTrace tailWord_579670 prefixEnd_579670 29397464789318742929299 := by
  unfold tailWord_579670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321393863122629037458529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14094867873308043066224309 1321393863122629037458529)
  ·
    refine ⟨991045397341971778093897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1321393863122629037458529 991045397341971778093897)
    ·
      refine ⟨743284048006478833570423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 991045397341971778093897 743284048006478833570423)
      ·
        refine ⟨1114926072009718250355635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743284048006478833570423 1114926072009718250355635)
        ·
          refine ⟨1672389108014577375533453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114926072009718250355635 1672389108014577375533453)
          ·
            refine ⟨627145915505466515825045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1672389108014577375533453 627145915505466515825045)
            ·
              refine ⟨29397464789318742929299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 627145915505466515825045 29397464789318742929299)
              ·
                rfl

theorem cell20_579670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 6].length) (baseStart_579670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579670 prefixEnd_579670 := by exact prefixLift 579670
  have htrace : WordTrace (prefixWord ++ tailWord_579670) baseStart_579670 baseEnd_579670 := by
    simpa [prefixWord, tailWord_579670, baseEnd_579670] using wordTrace_append hprefix tailTrace_579670
  have hstable : (prefixWord ++ tailWord_579670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579670).length < 2 ^ (prefixWord ++ tailWord_579670).sum := by decide
  have hdescent : baseEnd_579670 < baseStart_579670 := by decide
  rcases family_descends (prefixWord ++ tailWord_579670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579681 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_579681 : Nat := 118140960795 + 579681 * 2 ^ 59
def prefixEnd_579681 : Nat := 4983230072969 + 3 ^ 40 * 579681 * 2
def baseEnd_579681 : Nat := 264582203803601536996979

theorem tailTrace_579681 : CollatzResearch.WordTrace tailWord_579681 prefixEnd_579681 264582203803601536996979 := by
  unfold tailWord_579681
  simp only [CollatzResearch.WordTrace]
  refine ⟨21142703012922213477986897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14095135341948142318657931 21142703012922213477986897)
  ·
    refine ⟨15857027259691660108490173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21142703012922213477986897 15857027259691660108490173)
    ·
      refine ⟨5946385222384372540683815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15857027259691660108490173 5946385222384372540683815)
      ·
        refine ⟨8919577833576558811025723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946385222384372540683815 8919577833576558811025723)
        ·
          refine ⟨13379366750364838216538585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919577833576558811025723 13379366750364838216538585)
          ·
            refine ⟨10034525062773628662403939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13379366750364838216538585 10034525062773628662403939)
            ·
              refine ⟨15051787594160442993605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10034525062773628662403939 15051787594160442993605909)
              ·
                refine ⟨705552543476270765325277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15051787594160442993605909 705552543476270765325277)
                ·
                  refine ⟨264582203803601536996979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705552543476270765325277 264582203803601536996979)
                  ·
                    rfl

theorem cell20_579681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_579681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579681 prefixEnd_579681 := by exact prefixLift 579681
  have htrace : WordTrace (prefixWord ++ tailWord_579681) baseStart_579681 baseEnd_579681 := by
    simpa [prefixWord, tailWord_579681, baseEnd_579681] using wordTrace_append hprefix tailTrace_579681
  have hstable : (prefixWord ++ tailWord_579681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579681).length < 2 ^ (prefixWord ++ tailWord_579681).sum := by decide
  have hdescent : baseEnd_579681 < baseStart_579681 := by decide
  rcases family_descends (prefixWord ++ tailWord_579681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579695 : List Nat := [1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_579695 : Nat := 118140960795 + 579695 * 2 ^ 59
def prefixEnd_579695 : Nat := 4983230072969 + 3 ^ 40 * 579695 * 2
def baseEnd_579695 : Nat := 88196197928359903510085

theorem tailTrace_579695 : CollatzResearch.WordTrace tailWord_579695 prefixEnd_579695 88196197928359903510085 := by
  unfold tailWord_579695
  simp only [CollatzResearch.WordTrace]
  refine ⟨21143213634871493868996539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14095475756580995912664359 21143213634871493868996539)
  ·
    refine ⟨31714820452307240803494809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21143213634871493868996539 31714820452307240803494809)
    ·
      refine ⟨23786115339230430602621107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31714820452307240803494809 23786115339230430602621107)
      ·
        refine ⟨35679173008845645903931661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23786115339230430602621107 35679173008845645903931661)
        ·
          refine ⟨13379689878317117213974373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35679173008845645903931661 13379689878317117213974373)
          ·
            refine ⟨2508691852184459477620195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13379689878317117213974373 2508691852184459477620195)
            ·
              refine ⟨3763037778276689216430293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508691852184459477620195 3763037778276689216430293)
              ·
                refine ⟨88196197928359903510085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3763037778276689216430293 88196197928359903510085)
                ·
                  rfl

theorem cell20_579695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_579695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579695 prefixEnd_579695 := by exact prefixLift 579695
  have htrace : WordTrace (prefixWord ++ tailWord_579695) baseStart_579695 baseEnd_579695 := by
    simpa [prefixWord, tailWord_579695, baseEnd_579695] using wordTrace_append hprefix tailTrace_579695
  have hstable : (prefixWord ++ tailWord_579695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579695).length < 2 ^ (prefixWord ++ tailWord_579695).sum := by decide
  have hdescent : baseEnd_579695 < baseStart_579695 := by decide
  rcases family_descends (prefixWord ++ tailWord_579695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579698 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_579698 : Nat := 118140960795 + 579698 * 2 ^ 59
def prefixEnd_579698 : Nat := 4983230072969 + 3 ^ 40 * 579698 * 2
def baseEnd_579698 : Nat := 264589963066825033430243

theorem tailTrace_579698 : CollatzResearch.WordTrace tailWord_579698 prefixEnd_579698 264589963066825033430243 := by
  unfold tailWord_579698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285830763465156345338937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14095548702573750254237165 5285830763465156345338937)
  ·
    refine ⟨3964373072598867259004203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5285830763465156345338937 3964373072598867259004203)
    ·
      refine ⟨5946559608898300888506305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964373072598867259004203 5946559608898300888506305)
      ·
        refine ⟨4459919706673725666379729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5946559608898300888506305 4459919706673725666379729)
        ·
          refine ⟨3344939780005294249784797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4459919706673725666379729 3344939780005294249784797)
          ·
            refine ⟨1254352417501985343669299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3344939780005294249784797 1254352417501985343669299)
            ·
              refine ⟨1881528626252978015503949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254352417501985343669299 1881528626252978015503949)
              ·
                refine ⟨705573234844866755813981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1881528626252978015503949 705573234844866755813981)
                ·
                  refine ⟨264589963066825033430243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705573234844866755813981 264589963066825033430243)
                  ·
                    rfl

theorem cell20_579698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_579698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579698 prefixEnd_579698 := by exact prefixLift 579698
  have htrace : WordTrace (prefixWord ++ tailWord_579698) baseStart_579698 baseEnd_579698 := by
    simpa [prefixWord, tailWord_579698, baseEnd_579698] using wordTrace_append hprefix tailTrace_579698
  have hstable : (prefixWord ++ tailWord_579698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579698).length < 2 ^ (prefixWord ++ tailWord_579698).sum := by decide
  have hdescent : baseEnd_579698 < baseStart_579698 := by decide
  rcases family_descends (prefixWord ++ tailWord_579698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579732 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_579732 : Nat := 118140960795 + 579732 * 2 ^ 59
def prefixEnd_579732 : Nat := 4983230072969 + 3 ^ 40 * 579732 * 2
def baseEnd_579732 : Nat := 264605481593272026296771

theorem tailTrace_579732 : CollatzResearch.WordTrace tailWord_579732 prefixEnd_579732 264605481593272026296771 := by
  unfold tailWord_579732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572281567868724594046725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14096375423824966125395633 10572281567868724594046725)
  ·
    refine ⟨1982302793975385861383761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10572281567868724594046725 1982302793975385861383761)
    ·
      refine ⟨1486727095481539396037821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1982302793975385861383761 1486727095481539396037821)
      ·
        refine ⟨557522660805577273514183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1486727095481539396037821 557522660805577273514183)
        ·
          refine ⟨836283991208365910271275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557522660805577273514183 836283991208365910271275)
          ·
            refine ⟨1254425986812548865406913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836283991208365910271275 1254425986812548865406913)
            ·
              refine ⟨940819490109411649055185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254425986812548865406913 940819490109411649055185)
              ·
                refine ⟨705614617582058736791389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940819490109411649055185 705614617582058736791389)
                ·
                  refine ⟨264605481593272026296771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705614617582058736791389 264605481593272026296771)
                  ·
                    rfl

theorem cell20_579732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_579732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579732 prefixEnd_579732 := by exact prefixLift 579732
  have htrace : WordTrace (prefixWord ++ tailWord_579732) baseStart_579732 baseEnd_579732 := by
    simpa [prefixWord, tailWord_579732, baseEnd_579732] using wordTrace_append hprefix tailTrace_579732
  have hstable : (prefixWord ++ tailWord_579732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579732).length < 2 ^ (prefixWord ++ tailWord_579732).sum := by decide
  have hdescent : baseEnd_579732 < baseStart_579732 := by decide
  rcases family_descends (prefixWord ++ tailWord_579732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579781 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 2]
def baseStart_579781 : Nat := 118140960795 + 579781 * 2 ^ 59
def prefixEnd_579781 : Nat := 4983230072969 + 3 ^ 40 * 579781 * 2
def baseEnd_579781 : Nat := 264627846528445633663237

theorem tailTrace_579781 : CollatzResearch.WordTrace tailWord_579781 prefixEnd_579781 264627846528445633663237 := by
  unfold tailWord_579781
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146350312559930556627197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14097566875039953704418131 21146350312559930556627197)
  ·
    refine ⟨7929881367209973958735199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21146350312559930556627197 7929881367209973958735199)
    ·
      refine ⟨11894822050814960938102799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7929881367209973958735199 11894822050814960938102799)
      ·
        refine ⟨17842233076222441407154199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11894822050814960938102799 17842233076222441407154199)
        ·
          refine ⟨26763349614333662110731299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17842233076222441407154199 26763349614333662110731299)
          ·
            refine ⟨40145024421500493166096949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26763349614333662110731299 40145024421500493166096949)
            ·
              refine ⟨3763596039515671234321589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40145024421500493166096949 3763596039515671234321589)
              ·
                refine ⟨352837128704594178217649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3763596039515671234321589 352837128704594178217649)
                ·
                  refine ⟨264627846528445633663237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352837128704594178217649 264627846528445633663237)
                  ·
                    rfl

theorem cell20_579781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_579781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579781 prefixEnd_579781 := by exact prefixLift 579781
  have htrace : WordTrace (prefixWord ++ tailWord_579781) baseStart_579781 baseEnd_579781 := by
    simpa [prefixWord, tailWord_579781, baseEnd_579781] using wordTrace_append hprefix tailTrace_579781
  have hstable : (prefixWord ++ tailWord_579781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579781).length < 2 ^ (prefixWord ++ tailWord_579781).sum := by decide
  have hdescent : baseEnd_579781 < baseStart_579781 := by decide
  rcases family_descends (prefixWord ++ tailWord_579781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579798 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_579798 : Nat := 118140960795 + 579798 * 2 ^ 59
def prefixEnd_579798 : Nat := 4983230072969 + 3 ^ 40 * 579798 * 2
def baseEnd_579798 : Nat := 264635605791669130096501

theorem tailTrace_579798 : CollatzResearch.WordTrace tailWord_579798 prefixEnd_579798 264635605791669130096501 := by
  unfold tailWord_579798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321685647093646403749753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14097980235665561639997365 1321685647093646403749753)
  ·
    refine ⟨991264235320234802812315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1321685647093646403749753 991264235320234802812315)
    ·
      refine ⟨1486896352980352204218473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991264235320234802812315 1486896352980352204218473)
      ·
        refine ⟨1115172264735264153163855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1486896352980352204218473 1115172264735264153163855)
        ·
          refine ⟨1672758397102896229745783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115172264735264153163855 1672758397102896229745783)
          ·
            refine ⟨2509137595654344344618675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672758397102896229745783 2509137595654344344618675)
            ·
              refine ⟨3763706393481516516928013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509137595654344344618675 3763706393481516516928013)
              ·
                refine ⟨1411389897555568693848005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3763706393481516516928013 1411389897555568693848005)
                ·
                  refine ⟨264635605791669130096501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411389897555568693848005 264635605791669130096501)
                  ·
                    rfl

theorem cell20_579798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_579798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579798 prefixEnd_579798 := by exact prefixLift 579798
  have htrace : WordTrace (prefixWord ++ tailWord_579798) baseStart_579798 baseEnd_579798 := by
    simpa [prefixWord, tailWord_579798, baseEnd_579798] using wordTrace_append hprefix tailTrace_579798
  have hstable : (prefixWord ++ tailWord_579798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579798).length < 2 ^ (prefixWord ++ tailWord_579798).sum := by decide
  have hdescent : baseEnd_579798 < baseStart_579798 := by decide
  rcases family_descends (prefixWord ++ tailWord_579798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579802 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_579802 : Nat := 118140960795 + 579802 * 2 ^ 59
def prefixEnd_579802 : Nat := 4983230072969 + 3 ^ 40 * 579802 * 2
def baseEnd_579802 : Nat := 264637431500662893963151

theorem tailTrace_579802 : CollatzResearch.WordTrace tailWord_579802 prefixEnd_579802 264637431500662893963151 := by
  unfold tailWord_579802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5286779061370962785785415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14098077496989234095427773 5286779061370962785785415)
  ·
    refine ⟨7930168592056444178678123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5286779061370962785785415 7930168592056444178678123)
    ·
      refine ⟨11895252888084666268017185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7930168592056444178678123 11895252888084666268017185)
      ·
        refine ⟨8921439666063499701012889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11895252888084666268017185 8921439666063499701012889)
        ·
          refine ⟨6691079749547624775759667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8921439666063499701012889 6691079749547624775759667)
          ·
            refine ⟨10036619624321437163639501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6691079749547624775759667 10036619624321437163639501)
            ·
              refine ⟨3763732359120538936364813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10036619624321437163639501 3763732359120538936364813)
              ·
                refine ⟨1411399634670202101136805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3763732359120538936364813 1411399634670202101136805)
                ·
                  refine ⟨264637431500662893963151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411399634670202101136805 264637431500662893963151)
                  ·
                    rfl

theorem cell20_579802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_579802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579802 prefixEnd_579802 := by exact prefixLift 579802
  have htrace : WordTrace (prefixWord ++ tailWord_579802) baseStart_579802 baseEnd_579802 := by
    simpa [prefixWord, tailWord_579802, baseEnd_579802] using wordTrace_append hprefix tailTrace_579802
  have hstable : (prefixWord ++ tailWord_579802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579802).length < 2 ^ (prefixWord ++ tailWord_579802).sum := by decide
  have hdescent : baseEnd_579802 < baseStart_579802 := by decide
  rcases family_descends (prefixWord ++ tailWord_579802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579809 : List Nat := [1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_579809 : Nat := 118140960795 + 579809 * 2 ^ 59
def prefixEnd_579809 : Nat := 4983230072969 + 3 ^ 40 * 579809 * 2
def baseEnd_579809 : Nat := 88213542163800660243263

theorem tailTrace_579809 : CollatzResearch.WordTrace tailWord_579809 prefixEnd_579809 88213542163800660243263 := by
  unfold tailWord_579809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21147371556458491338646481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14098247704305660892430987 21147371556458491338646481)
  ·
    refine ⟨15860528667343868503984861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21147371556458491338646481 15860528667343868503984861)
    ·
      refine ⟨5947698250253950688994323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15860528667343868503984861 5947698250253950688994323)
      ·
        refine ⟨8921547375380926033491485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947698250253950688994323 8921547375380926033491485)
        ·
          refine ⟨3345580265767847262559307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8921547375380926033491485 3345580265767847262559307)
          ·
            refine ⟨5018370398651770893838961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345580265767847262559307 5018370398651770893838961)
            ·
              refine ⟨3763777798988828170379221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5018370398651770893838961 3763777798988828170379221)
              ·
                refine ⟨88213542163800660243263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3763777798988828170379221 88213542163800660243263)
                ·
                  rfl

theorem cell20_579809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_579809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579809 prefixEnd_579809 := by exact prefixLift 579809
  have htrace : WordTrace (prefixWord ++ tailWord_579809) baseStart_579809 baseEnd_579809 := by
    simpa [prefixWord, tailWord_579809, baseEnd_579809] using wordTrace_append hprefix tailTrace_579809
  have hstable : (prefixWord ++ tailWord_579809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579809).length < 2 ^ (prefixWord ++ tailWord_579809).sum := by decide
  have hdescent : baseEnd_579809 < baseStart_579809 := by decide
  rcases family_descends (prefixWord ++ tailWord_579809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579826 : List Nat := [3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_579826 : Nat := 118140960795 + 579826 * 2 ^ 59
def prefixEnd_579826 : Nat := 4983230072969 + 3 ^ 40 * 579826 * 2
def baseEnd_579826 : Nat := 88216128584875159054351

theorem tailTrace_579826 : CollatzResearch.WordTrace tailWord_579826 prefixEnd_579826 88216128584875159054351 := by
  unfold tailWord_579826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5286997899349225810503833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14098661064931268828010221 5286997899349225810503833)
  ·
    refine ⟨3965248424511919357877875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5286997899349225810503833 3965248424511919357877875)
    ·
      refine ⟨5947872636767879036816813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965248424511919357877875 5947872636767879036816813)
      ·
        refine ⟨2230452238787954638806305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5947872636767879036816813 2230452238787954638806305)
        ·
          refine ⟨1672839179090965979104729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2230452238787954638806305 1672839179090965979104729)
          ·
            refine ⟨1254629384318224484328547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672839179090965979104729 1254629384318224484328547)
            ·
              refine ⟨1881944076477336726492821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254629384318224484328547 1881944076477336726492821)
              ·
                refine ⟨88216128584875159054351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1881944076477336726492821 88216128584875159054351)
                ·
                  rfl

theorem cell20_579826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_579826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579826 prefixEnd_579826 := by exact prefixLift 579826
  have htrace : WordTrace (prefixWord ++ tailWord_579826) baseStart_579826 baseEnd_579826 := by
    simpa [prefixWord, tailWord_579826, baseEnd_579826] using wordTrace_append hprefix tailTrace_579826
  have hstable : (prefixWord ++ tailWord_579826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579826).length < 2 ^ (prefixWord ++ tailWord_579826).sum := by decide
  have hdescent : baseEnd_579826 < baseStart_579826 := by decide
  rcases family_descends (prefixWord ++ tailWord_579826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579836 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 2]
def baseStart_579836 : Nat := 118140960795 + 579836 * 2 ^ 59
def prefixEnd_579836 : Nat := 4983230072969 + 3 ^ 40 * 579836 * 2
def baseEnd_579836 : Nat := 264652950027109886829679

theorem tailTrace_579836 : CollatzResearch.WordTrace tailWord_579836 prefixEnd_579836 264652950027109886829679 := by
  unfold tailWord_579836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574178163680337474939681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14098904218240449966586241 10574178163680337474939681)
  ·
    refine ⟨7930633622760253106204761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10574178163680337474939681 7930633622760253106204761)
    ·
      refine ⟨5947975217070189829653571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7930633622760253106204761 5947975217070189829653571)
      ·
        refine ⟨8921962825605284744480357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947975217070189829653571 8921962825605284744480357)
        ·
          refine ⟨1672868029800990889590067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8921962825605284744480357 1672868029800990889590067)
          ·
            refine ⟨2509302044701486334385101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672868029800990889590067 2509302044701486334385101)
            ·
              refine ⟨940988266763057375394413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2509302044701486334385101 940988266763057375394413)
              ·
                refine ⟨352870600036146515772905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940988266763057375394413 352870600036146515772905)
                ·
                  refine ⟨264652950027109886829679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352870600036146515772905 264652950027109886829679)
                  ·
                    rfl

theorem cell20_579836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_579836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579836 prefixEnd_579836 := by exact prefixLift 579836
  have htrace : WordTrace (prefixWord ++ tailWord_579836) baseStart_579836 baseEnd_579836 := by
    simpa [prefixWord, tailWord_579836, baseEnd_579836] using wordTrace_append hprefix tailTrace_579836
  have hstable : (prefixWord ++ tailWord_579836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579836).length < 2 ^ (prefixWord ++ tailWord_579836).sum := by decide
  have hdescent : baseEnd_579836 < baseStart_579836 := by decide
  rcases family_descends (prefixWord ++ tailWord_579836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579857 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 4]
def baseStart_579857 : Nat := 118140960795 + 579857 * 2 ^ 59
def prefixEnd_579857 : Nat := 4983230072969 + 3 ^ 40 * 579857 * 2
def baseEnd_579857 : Nat := 264662534999327147129593

theorem tailTrace_579857 : CollatzResearch.WordTrace tailWord_579857 prefixEnd_579857 264662534999327147129593 := by
  unfold tailWord_579857
  simp only [CollatzResearch.WordTrace]
  refine ⟨21149122260284595536393825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14099414840189730357595883 21149122260284595536393825)
  ·
    refine ⟨15861841695213446652295369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21149122260284595536393825 15861841695213446652295369)
    ·
      refine ⟨11896381271410084989221527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15861841695213446652295369 11896381271410084989221527)
      ·
        refine ⟨17844571907115127483832291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11896381271410084989221527 17844571907115127483832291)
        ·
          refine ⟨26766857860672691225748437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17844571907115127483832291 26766857860672691225748437)
          ·
            refine ⟨627348231109516200603479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26766857860672691225748437 627348231109516200603479)
            ·
              refine ⟨941022346664274300905219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627348231109516200603479 941022346664274300905219)
              ·
                refine ⟨1411533519996411451357829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941022346664274300905219 1411533519996411451357829)
                ·
                  refine ⟨264662534999327147129593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411533519996411451357829 264662534999327147129593)
                  ·
                    rfl

theorem cell20_579857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_579857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579857 prefixEnd_579857 := by exact prefixLift 579857
  have htrace : WordTrace (prefixWord ++ tailWord_579857) baseStart_579857 baseEnd_579857 := by
    simpa [prefixWord, tailWord_579857, baseEnd_579857] using wordTrace_append hprefix tailTrace_579857
  have hstable : (prefixWord ++ tailWord_579857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579857).length < 2 ^ (prefixWord ++ tailWord_579857).sum := by decide
  have hdescent : baseEnd_579857 < baseStart_579857 := by decide
  rcases family_descends (prefixWord ++ tailWord_579857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579905 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_579905 : Nat := 118140960795 + 579905 * 2 ^ 59
def prefixEnd_579905 : Nat := 4983230072969 + 3 ^ 40 * 579905 * 2
def baseEnd_579905 : Nat := 264684443507252313529397

theorem tailTrace_579905 : CollatzResearch.WordTrace tailWord_579905 prefixEnd_579905 264684443507252313529397 := by
  unfold tailWord_579905
  simp only [CollatzResearch.WordTrace]
  refine ⟨21150872964110699734141169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14100581976073799822760779 21150872964110699734141169)
  ·
    refine ⟨15863154723083024800605877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21150872964110699734141169 15863154723083024800605877)
    ·
      refine ⟨1487170755289033575056801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15863154723083024800605877 1487170755289033575056801)
      ·
        refine ⟨1115378066466775181292601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487170755289033575056801 1115378066466775181292601)
        ·
          refine ⟨836533549850081385969451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115378066466775181292601 836533549850081385969451)
          ·
            refine ⟨1254800324775122078954177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836533549850081385969451 1254800324775122078954177)
            ·
              refine ⟨941100243581341559215633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254800324775122078954177 941100243581341559215633)
              ·
                refine ⟨705825182686006169411725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941100243581341559215633 705825182686006169411725)
                ·
                  refine ⟨264684443507252313529397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705825182686006169411725 264684443507252313529397)
                  ·
                    rfl

theorem cell20_579905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_579905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579905 prefixEnd_579905 := by exact prefixLift 579905
  have htrace : WordTrace (prefixWord ++ tailWord_579905) baseStart_579905 baseEnd_579905 := by
    simpa [prefixWord, tailWord_579905, baseEnd_579905] using wordTrace_append hprefix tailTrace_579905
  have hstable : (prefixWord ++ tailWord_579905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579905).length < 2 ^ (prefixWord ++ tailWord_579905).sum := by decide
  have hdescent : baseEnd_579905 < baseStart_579905 := by decide
  rcases family_descends (prefixWord ++ tailWord_579905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579912 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 2]
def baseStart_579912 : Nat := 118140960795 + 579912 * 2 ^ 59
def prefixEnd_579912 : Nat := 4983230072969 + 3 ^ 40 * 579912 * 2
def baseEnd_579912 : Nat := 264687638497991400296035

theorem tailTrace_579912 : CollatzResearch.WordTrace tailWord_579912 prefixEnd_579912 264687638497991400296035 := by
  unfold tailWord_579912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10575564137542669964822995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14100752183390226619763993 10575564137542669964822995)
  ·
    refine ⟨15863346206314004947234493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10575564137542669964822995 15863346206314004947234493)
    ·
      refine ⟨5948754827367751855212935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15863346206314004947234493 5948754827367751855212935)
      ·
        refine ⟨8923132241051627782819403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5948754827367751855212935 8923132241051627782819403)
        ·
          refine ⟨13384698361577441674229105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8923132241051627782819403 13384698361577441674229105)
          ·
            refine ⟨10038523771183081255671829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13384698361577441674229105 10038523771183081255671829)
            ·
              refine ⟨470555801774206933859617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10038523771183081255671829 470555801774206933859617)
              ·
                refine ⟨352916851330655200394713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470555801774206933859617 352916851330655200394713)
                ·
                  refine ⟨264687638497991400296035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352916851330655200394713 264687638497991400296035)
                  ·
                    rfl

theorem cell20_579912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_579912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579912 prefixEnd_579912 := by exact prefixLift 579912
  have htrace : WordTrace (prefixWord ++ tailWord_579912) baseStart_579912 baseEnd_579912 := by
    simpa [prefixWord, tailWord_579912, baseEnd_579912] using wordTrace_append hprefix tailTrace_579912
  have hstable : (prefixWord ++ tailWord_579912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579912).length < 2 ^ (prefixWord ++ tailWord_579912).sum := by decide
  have hdescent : baseEnd_579912 < baseStart_579912 := by decide
  rcases family_descends (prefixWord ++ tailWord_579912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579916 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_579916 : Nat := 118140960795 + 579916 * 2 ^ 59
def prefixEnd_579916 : Nat := 4983230072969 + 3 ^ 40 * 579916 * 2
def baseEnd_579916 : Nat := 264689464206985164162685

theorem tailTrace_579916 : CollatzResearch.WordTrace tailWord_579916 prefixEnd_579916 264689464206985164162685 := by
  unfold tailWord_579916
  simp only [CollatzResearch.WordTrace]
  refine ⟨10575637083535424306395801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14100849444713899075194401 10575637083535424306395801)
  ·
    refine ⟨7931727812651568229796851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10575637083535424306395801 7931727812651568229796851)
    ·
      refine ⟨11897591718977352344695277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7931727812651568229796851 11897591718977352344695277)
      ·
        refine ⟨4461596894616507129260729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11897591718977352344695277 4461596894616507129260729)
        ·
          refine ⟨3346197670962380346945547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4461596894616507129260729 3346197670962380346945547)
          ·
            refine ⟨5019296506443570520418321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346197670962380346945547 5019296506443570520418321)
            ·
              refine ⟨3764472379832677890313741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5019296506443570520418321 3764472379832677890313741)
              ·
                refine ⟨1411677142437254208867653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3764472379832677890313741 1411677142437254208867653)
                ·
                  refine ⟨264689464206985164162685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411677142437254208867653 264689464206985164162685)
                  ·
                    rfl

theorem cell20_579916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_579916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579916 prefixEnd_579916 := by exact prefixLift 579916
  have htrace : WordTrace (prefixWord ++ tailWord_579916) baseStart_579916 baseEnd_579916 := by
    simpa [prefixWord, tailWord_579916, baseEnd_579916] using wordTrace_append hprefix tailTrace_579916
  have hstable : (prefixWord ++ tailWord_579916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579916).length < 2 ^ (prefixWord ++ tailWord_579916).sum := by decide
  have hdescent : baseEnd_579916 < baseStart_579916 := by decide
  rcases family_descends (prefixWord ++ tailWord_579916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579930 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_579930 : Nat := 118140960795 + 579930 * 2 ^ 59
def prefixEnd_579930 : Nat := 4983230072969 + 3 ^ 40 * 579930 * 2
def baseEnd_579930 : Nat := 264695854188463337695961

theorem tailTrace_579930 : CollatzResearch.WordTrace tailWord_579930 prefixEnd_579930 264695854188463337695961 := by
  unfold tailWord_579930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287946197255032250950311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14101189859346752669200829 5287946197255032250950311)
  ·
    refine ⟨7931919295882548376425467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287946197255032250950311 7931919295882548376425467)
    ·
      refine ⟨11897878943823822564638201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7931919295882548376425467 11897878943823822564638201)
      ·
        refine ⟨8923409207867866923478651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11897878943823822564638201 8923409207867866923478651)
        ·
          refine ⟨13385113811801800385217977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8923409207867866923478651 13385113811801800385217977)
          ·
            refine ⟨10038835358851350288913483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13385113811801800385217977 10038835358851350288913483)
            ·
              refine ⟨15058253038277025433370225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10038835358851350288913483 15058253038277025433370225)
              ·
                refine ⟨11293689778707769075027669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15058253038277025433370225 11293689778707769075027669)
                ·
                  refine ⟨264695854188463337695961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11293689778707769075027669 264695854188463337695961)
                  ·
                    rfl

theorem cell20_579930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_579930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579930 prefixEnd_579930 := by exact prefixLift 579930
  have htrace : WordTrace (prefixWord ++ tailWord_579930) baseStart_579930 baseEnd_579930 := by
    simpa [prefixWord, tailWord_579930, baseEnd_579930] using wordTrace_append hprefix tailTrace_579930
  have hstable : (prefixWord ++ tailWord_579930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579930).length < 2 ^ (prefixWord ++ tailWord_579930).sum := by decide
  have hdescent : baseEnd_579930 < baseStart_579930 := by decide
  rcases family_descends (prefixWord ++ tailWord_579930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579940 : List Nat := [2, 3, 1, 1, 3, 1, 5, 4]
def baseStart_579940 : Nat := 118140960795 + 579940 * 2 ^ 59
def prefixEnd_579940 : Nat := 4983230072969 + 3 ^ 40 * 579940 * 2
def baseEnd_579940 : Nat := 88233472820315915787529

theorem tailTrace_579940 : CollatzResearch.WordTrace tailWord_579940 prefixEnd_579940 88233472820315915787529 := by
  unfold tailWord_579940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10576074759491950355832637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14101433012655933807776849 10576074759491950355832637)
  ·
    refine ⟨3966028034809481383437239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10576074759491950355832637 3966028034809481383437239)
    ·
      refine ⟨5949042052214222075155859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3966028034809481383437239 5949042052214222075155859)
      ·
        refine ⟨8923563078321333112733789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5949042052214222075155859 8923563078321333112733789)
        ·
          refine ⟨3346336154370499917275171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8923563078321333112733789 3346336154370499917275171)
          ·
            refine ⟨5019504231555749875912757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346336154370499917275171 5019504231555749875912757)
            ·
              refine ⟨470578521708351550866821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5019504231555749875912757 470578521708351550866821)
              ·
                refine ⟨88233472820315915787529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470578521708351550866821 88233472820315915787529)
                ·
                  rfl

theorem cell20_579940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_579940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579940 prefixEnd_579940 := by exact prefixLift 579940
  have htrace : WordTrace (prefixWord ++ tailWord_579940) baseStart_579940 baseEnd_579940 := by
    simpa [prefixWord, tailWord_579940, baseEnd_579940] using wordTrace_append hprefix tailTrace_579940
  have hstable : (prefixWord ++ tailWord_579940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579940).length < 2 ^ (prefixWord ++ tailWord_579940).sum := by decide
  have hdescent : baseEnd_579940 < baseStart_579940 := by decide
  rcases family_descends (prefixWord ++ tailWord_579940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579971 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_579971 : Nat := 118140960795 + 579971 * 2 ^ 59
def prefixEnd_579971 : Nat := 4983230072969 + 3 ^ 40 * 579971 * 2
def baseEnd_579971 : Nat := 264714567705649417329127

theorem tailTrace_579971 : CollatzResearch.WordTrace tailWord_579971 prefixEnd_579971 264714567705649417329127 := by
  unfold tailWord_579971
  simp only [CollatzResearch.WordTrace]
  refine ⟨21153280181871593006043767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14102186787914395337362511 21153280181871593006043767)
  ·
    refine ⟨31729920272807389509065651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21153280181871593006043767 31729920272807389509065651)
    ·
      refine ⟨47594880409211084263598477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31729920272807389509065651 47594880409211084263598477)
      ·
        refine ⟨17848080153454156598849429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47594880409211084263598477 17848080153454156598849429)
        ·
          refine ⟨836628757193163590571067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17848080153454156598849429 836628757193163590571067)
          ·
            refine ⟨1254943135789745385856601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836628757193163590571067 1254943135789745385856601)
            ·
              refine ⟨941207351842309039392451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254943135789745385856601 941207351842309039392451)
              ·
                refine ⟨1411811027763463559088677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941207351842309039392451 1411811027763463559088677)
                ·
                  refine ⟨264714567705649417329127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411811027763463559088677 264714567705649417329127)
                  ·
                    rfl

theorem cell20_579971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_579971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579971 prefixEnd_579971 := by exact prefixLift 579971
  have htrace : WordTrace (prefixWord ++ tailWord_579971) baseStart_579971 baseEnd_579971 := by
    simpa [prefixWord, tailWord_579971, baseEnd_579971] using wordTrace_append hprefix tailTrace_579971
  have hstable : (prefixWord ++ tailWord_579971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579971).length < 2 ^ (prefixWord ++ tailWord_579971).sum := by decide
  have hdescent : baseEnd_579971 < baseStart_579971 := by decide
  rcases family_descends (prefixWord ++ tailWord_579971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579999 : List Nat := [1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_579999 : Nat := 118140960795 + 579999 * 2 ^ 59
def prefixEnd_579999 : Nat := 4983230072969 + 3 ^ 40 * 579999 * 2
def baseEnd_579999 : Nat := 88242449222868588131893

theorem tailTrace_579999 : CollatzResearch.WordTrace tailWord_579999 prefixEnd_579999 88242449222868588131893 := by
  unfold tailWord_579999
  simp only [CollatzResearch.WordTrace]
  refine ⟨21154301425770153788063051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14102867617180102525375367 21154301425770153788063051)
  ·
    refine ⟨31731452138655230682094577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21154301425770153788063051 31731452138655230682094577)
    ·
      refine ⟨23798589103991423011570933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31731452138655230682094577 23798589103991423011570933)
      ·
        refine ⟨2231117728499195907334775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23798589103991423011570933 2231117728499195907334775)
        ·
          refine ⟨3346676592748793861002163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231117728499195907334775 3346676592748793861002163)
          ·
            refine ⟨5020014889123190791503245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346676592748793861002163 5020014889123190791503245)
            ·
              refine ⟨1882505583421196546813717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5020014889123190791503245 1882505583421196546813717)
              ·
                refine ⟨88242449222868588131893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1882505583421196546813717 88242449222868588131893)
                ·
                  rfl

theorem cell20_579999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_579999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_579999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_579999 prefixEnd_579999 := by exact prefixLift 579999
  have htrace : WordTrace (prefixWord ++ tailWord_579999) baseStart_579999 baseEnd_579999 := by
    simpa [prefixWord, tailWord_579999, baseEnd_579999] using wordTrace_append hprefix tailTrace_579999
  have hstable : (prefixWord ++ tailWord_579999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579999).length < 2 ^ (prefixWord ++ tailWord_579999).sum := by decide
  have hdescent : baseEnd_579999 < baseStart_579999 := by decide
  rcases family_descends (prefixWord ++ tailWord_579999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580036 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_580036 : Nat := 118140960795 + 580036 * 2 ^ 59
def prefixEnd_580036 : Nat := 4983230072969 + 3 ^ 40 * 580036 * 2
def baseEnd_580036 : Nat := 264744235476798080162195

theorem tailTrace_580036 : CollatzResearch.WordTrace tailWord_580036 prefixEnd_580036 264744235476798080162195 := by
  unfold tailWord_580036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577825463318054553579981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14103767284424072738106641 10577825463318054553579981)
  ·
    refine ⟨3966684548744270457592493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10577825463318054553579981 3966684548744270457592493)
    ·
      refine ⟨1487506705779101421597185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3966684548744270457592493 1487506705779101421597185)
      ·
        refine ⟨1115630029334326066197889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487506705779101421597185 1115630029334326066197889)
        ·
          refine ⟨836722522000744549648417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115630029334326066197889 836722522000744549648417)
          ·
            refine ⟨627541891500558412236313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836722522000744549648417 627541891500558412236313)
            ·
              refine ⟨470656418625418809177235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627541891500558412236313 470656418625418809177235)
              ·
                refine ⟨705984627938128213765853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470656418625418809177235 705984627938128213765853)
                ·
                  refine ⟨264744235476798080162195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705984627938128213765853 264744235476798080162195)
                  ·
                    rfl

theorem cell20_580036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_580036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580036 prefixEnd_580036 := by exact prefixLift 580036
  have htrace : WordTrace (prefixWord ++ tailWord_580036) baseStart_580036 baseEnd_580036 := by
    simpa [prefixWord, tailWord_580036, baseEnd_580036] using wordTrace_append hprefix tailTrace_580036
  have hstable : (prefixWord ++ tailWord_580036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580036).length < 2 ^ (prefixWord ++ tailWord_580036).sum := by decide
  have hdescent : baseEnd_580036 < baseStart_580036 := by decide
  rcases family_descends (prefixWord ++ tailWord_580036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580040 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_580040 : Nat := 118140960795 + 580040 * 2 ^ 59
def prefixEnd_580040 : Nat := 4983230072969 + 3 ^ 40 * 580040 * 2
def baseEnd_580040 : Nat := 264746061185791844028845

theorem tailTrace_580040 : CollatzResearch.WordTrace tailWord_580040 prefixEnd_580040 264746061185791844028845 := by
  unfold tailWord_580040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577898409310808895152787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14103864545747745193537049 10577898409310808895152787)
  ·
    refine ⟨15866847613966213342729181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10577898409310808895152787 15866847613966213342729181)
    ·
      refine ⟨5950067855237330003523443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15866847613966213342729181 5950067855237330003523443)
      ·
        refine ⟨8925101782855995005285165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950067855237330003523443 8925101782855995005285165)
        ·
          refine ⟨3346913168570998126981937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8925101782855995005285165 3346913168570998126981937)
          ·
            refine ⟨2510184876428248595236453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3346913168570998126981937 2510184876428248595236453)
            ·
              refine ⟨470659664330296611606835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2510184876428248595236453 470659664330296611606835)
              ·
                refine ⟨705989496495444917410253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470659664330296611606835 705989496495444917410253)
                ·
                  refine ⟨264746061185791844028845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705989496495444917410253 264746061185791844028845)
                  ·
                    rfl

theorem cell20_580040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_580040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580040 prefixEnd_580040 := by exact prefixLift 580040
  have htrace : WordTrace (prefixWord ++ tailWord_580040) baseStart_580040 baseEnd_580040 := by
    simpa [prefixWord, tailWord_580040, baseEnd_580040] using wordTrace_append hprefix tailTrace_580040
  have hstable : (prefixWord ++ tailWord_580040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580040).length < 2 ^ (prefixWord ++ tailWord_580040).sum := by decide
  have hdescent : baseEnd_580040 < baseStart_580040 := by decide
  rcases family_descends (prefixWord ++ tailWord_580040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580054 : List Nat := [5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_580054 : Nat := 118140960795 + 580054 * 2 ^ 59
def prefixEnd_580054 : Nat := 4983230072969 + 3 ^ 40 * 580054 * 2
def baseEnd_580054 : Nat := 88250817055756672520707

theorem tailTrace_580054 : CollatzResearch.WordTrace tailWord_580054 prefixEnd_580054 88250817055756672520707 := by
  unfold tailWord_580054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322269215035681136332201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14104204960380598787543477 1322269215035681136332201)
  ·
    refine ⟨991701911276760852249151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1322269215035681136332201 991701911276760852249151)
    ·
      refine ⟨1487552866915141278373727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991701911276760852249151 1487552866915141278373727)
      ·
        refine ⟨2231329300372711917560591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487552866915141278373727 2231329300372711917560591)
        ·
          refine ⟨3346993950559067876340887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231329300372711917560591 3346993950559067876340887)
          ·
            refine ⟨5020490925838601814511331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346993950559067876340887 5020490925838601814511331)
            ·
              refine ⟨7530736388757902721766997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020490925838601814511331 7530736388757902721766997)
              ·
                refine ⟨88250817055756672520707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7530736388757902721766997 88250817055756672520707)
                ·
                  rfl

theorem cell20_580054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_580054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580054 prefixEnd_580054 := by exact prefixLift 580054
  have htrace : WordTrace (prefixWord ++ tailWord_580054) baseStart_580054 baseEnd_580054 := by
    simpa [prefixWord, tailWord_580054, baseEnd_580054] using wordTrace_append hprefix tailTrace_580054
  have hstable : (prefixWord ++ tailWord_580054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580054).length < 2 ^ (prefixWord ++ tailWord_580054).sum := by decide
  have hdescent : baseEnd_580054 < baseStart_580054 := by decide
  rcases family_descends (prefixWord ++ tailWord_580054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580078 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_580078 : Nat := 118140960795 + 580078 * 2 ^ 59
def prefixEnd_580078 : Nat := 4983230072969 + 3 ^ 40 * 580078 * 2
def baseEnd_580078 : Nat := 264763405421232600762023

theorem tailTrace_580078 : CollatzResearch.WordTrace tailWord_580078 prefixEnd_580078 264763405421232600762023 := by
  unfold tailWord_580078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644647849060493785023611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14104788528322633520125925 2644647849060493785023611)
  ·
    refine ⟨3966971773590740677535417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2644647849060493785023611 3966971773590740677535417)
    ·
      refine ⟨2975228830193055508151563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3966971773590740677535417 2975228830193055508151563)
      ·
        refine ⟨4462843245289583262227345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975228830193055508151563 4462843245289583262227345)
        ·
          refine ⟨3347132433967187446670509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4462843245289583262227345 3347132433967187446670509)
          ·
            refine ⟨1255174662737695292501441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3347132433967187446670509 1255174662737695292501441)
            ·
              refine ⟨941380997053271469376081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255174662737695292501441 941380997053271469376081)
              ·
                refine ⟨706035747789953602032061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941380997053271469376081 706035747789953602032061)
                ·
                  refine ⟨264763405421232600762023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706035747789953602032061 264763405421232600762023)
                  ·
                    rfl

theorem cell20_580078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_580078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580078 prefixEnd_580078 := by exact prefixLift 580078
  have htrace : WordTrace (prefixWord ++ tailWord_580078) baseStart_580078 baseEnd_580078 := by
    simpa [prefixWord, tailWord_580078, baseEnd_580078] using wordTrace_append hprefix tailTrace_580078
  have hstable : (prefixWord ++ tailWord_580078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580078).length < 2 ^ (prefixWord ++ tailWord_580078).sum := by decide
  have hdescent : baseEnd_580078 < baseStart_580078 := by decide
  rcases family_descends (prefixWord ++ tailWord_580078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580106 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_580106 : Nat := 118140960795 + 580106 * 2 ^ 59
def prefixEnd_580106 : Nat := 4983230072969 + 3 ^ 40 * 580106 * 2
def baseEnd_580106 : Nat := 264776185384188947828575

theorem tailTrace_580106 : CollatzResearch.WordTrace tailWord_580106 prefixEnd_580106 264776185384188947828575 := by
  unfold tailWord_580106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289551009095627765552043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14105469357588340708138781 5289551009095627765552043)
  ·
    refine ⟨7934326513643441648328065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5289551009095627765552043 7934326513643441648328065)
    ·
      refine ⟨5950744885232581236246049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7934326513643441648328065 5950744885232581236246049)
      ·
        refine ⟨4463058663924435927184537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5950744885232581236246049 4463058663924435927184537)
        ·
          refine ⟨3347293997943326945388403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4463058663924435927184537 3347293997943326945388403)
          ·
            refine ⟨5020940996914990418082605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347293997943326945388403 5020940996914990418082605)
            ·
              refine ⟨1882852873843121406780977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5020940996914990418082605 1882852873843121406780977)
              ·
                refine ⟨1412139655382341055085733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882852873843121406780977 1412139655382341055085733)
                ·
                  refine ⟨264776185384188947828575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412139655382341055085733 264776185384188947828575)
                  ·
                    rfl

theorem cell20_580106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_580106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580106 prefixEnd_580106 := by exact prefixLift 580106
  have htrace : WordTrace (prefixWord ++ tailWord_580106) baseStart_580106 baseEnd_580106 := by
    simpa [prefixWord, tailWord_580106, baseEnd_580106] using wordTrace_append hprefix tailTrace_580106
  have hstable : (prefixWord ++ tailWord_580106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580106).length < 2 ^ (prefixWord ++ tailWord_580106).sum := by decide
  have hdescent : baseEnd_580106 < baseStart_580106 := by decide
  rcases family_descends (prefixWord ++ tailWord_580106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580119 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 2]
def baseStart_580119 : Nat := 118140960795 + 580119 * 2 ^ 59
def prefixEnd_580119 : Nat := 4983230072969 + 3 ^ 40 * 580119 * 2
def baseEnd_580119 : Nat := 264782118938418680395189

theorem tailTrace_580119 : CollatzResearch.WordTrace tailWord_580119 prefixEnd_580119 264782118938418680395189 := by
  unfold tailWord_580119
  simp only [CollatzResearch.WordTrace]
  refine ⟨21158678185335414282431411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14105785456890276188287607 21158678185335414282431411)
  ·
    refine ⟨31738017278003121423647117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21158678185335414282431411 31738017278003121423647117)
    ·
      refine ⟨11901756479251170533867669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31738017278003121423647117 11901756479251170533867669)
      ·
        refine ⟨557894834964898618775047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11901756479251170533867669 557894834964898618775047)
        ·
          refine ⟨836842252447347928162571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557894834964898618775047 836842252447347928162571)
          ·
            refine ⟨1255263378671021892243857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836842252447347928162571 1255263378671021892243857)
            ·
              refine ⟨941447534003266419182893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255263378671021892243857 941447534003266419182893)
              ·
                refine ⟨353042825251224907193585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 941447534003266419182893 353042825251224907193585)
                ·
                  refine ⟨264782118938418680395189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353042825251224907193585 264782118938418680395189)
                  ·
                    rfl

theorem cell20_580119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 2].length) (baseStart_580119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580119 prefixEnd_580119 := by exact prefixLift 580119
  have htrace : WordTrace (prefixWord ++ tailWord_580119) baseStart_580119 baseEnd_580119 := by
    simpa [prefixWord, tailWord_580119, baseEnd_580119] using wordTrace_append hprefix tailTrace_580119
  have hstable : (prefixWord ++ tailWord_580119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580119).length < 2 ^ (prefixWord ++ tailWord_580119).sum := by decide
  have hdescent : baseEnd_580119 < baseStart_580119 := by decide
  rcases family_descends (prefixWord ++ tailWord_580119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580127 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_580127 : Nat := 118140960795 + 580127 * 2 ^ 59
def prefixEnd_580127 : Nat := 4983230072969 + 3 ^ 40 * 580127 * 2
def baseEnd_580127 : Nat := 264785770356406208128489

theorem tailTrace_580127 : CollatzResearch.WordTrace tailWord_580127 prefixEnd_580127 264785770356406208128489 := by
  unfold tailWord_580127
  simp only [CollatzResearch.WordTrace]
  refine ⟨21158969969306431648722635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14105979979537621099148423 21158969969306431648722635)
  ·
    refine ⟨31738454953959647473083953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21158969969306431648722635 31738454953959647473083953)
    ·
      refine ⟨23803841215469735604812965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31738454953959647473083953 23803841215469735604812965)
      ·
        refine ⟨4463220227900575425902431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23803841215469735604812965 4463220227900575425902431)
        ·
          refine ⟨6694830341850863138853647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4463220227900575425902431 6694830341850863138853647)
          ·
            refine ⟨10042245512776294708280471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6694830341850863138853647 10042245512776294708280471)
            ·
              refine ⟨15063368269164442062420707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10042245512776294708280471 15063368269164442062420707)
              ·
                refine ⟨22595052403746663093631061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15063368269164442062420707 22595052403746663093631061)
                ·
                  refine ⟨264785770356406208128489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22595052403746663093631061 264785770356406208128489)
                  ·
                    rfl

theorem cell20_580127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_580127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580127 prefixEnd_580127 := by exact prefixLift 580127
  have htrace : WordTrace (prefixWord ++ tailWord_580127) baseStart_580127 baseEnd_580127 := by
    simpa [prefixWord, tailWord_580127, baseEnd_580127] using wordTrace_append hprefix tailTrace_580127
  have hstable : (prefixWord ++ tailWord_580127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580127).length < 2 ^ (prefixWord ++ tailWord_580127).sum := by decide
  have hdescent : baseEnd_580127 < baseStart_580127 := by decide
  rcases family_descends (prefixWord ++ tailWord_580127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580154 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_580154 : Nat := 118140960795 + 580154 * 2 ^ 59
def prefixEnd_580154 : Nat := 4983230072969 + 3 ^ 40 * 580154 * 2
def baseEnd_580154 : Nat := 264798093892114114228379

theorem tailTrace_580154 : CollatzResearch.WordTrace tailWord_580154 prefixEnd_580154 264798093892114114228379 := by
  unfold tailWord_580154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289988685052153814988879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14106636493472410173303677 5289988685052153814988879)
  ·
    refine ⟨7934983027578230722483319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5289988685052153814988879 7934983027578230722483319)
    ·
      refine ⟨11902474541367346083724979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7934983027578230722483319 11902474541367346083724979)
      ·
        refine ⟨17853711812051019125587469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11902474541367346083724979 17853711812051019125587469)
        ·
          refine ⟨6695141929519132172095301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17853711812051019125587469 6695141929519132172095301)
          ·
            refine ⟨1255339111784837282267869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6695141929519132172095301 1255339111784837282267869)
            ·
              refine ⟨470752166919313980850451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1255339111784837282267869 470752166919313980850451)
              ·
                refine ⟨706128250378970971275677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470752166919313980850451 706128250378970971275677)
                ·
                  refine ⟨264798093892114114228379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706128250378970971275677 264798093892114114228379)
                  ·
                    rfl

theorem cell20_580154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_580154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580154 prefixEnd_580154 := by exact prefixLift 580154
  have htrace : WordTrace (prefixWord ++ tailWord_580154) baseStart_580154 baseEnd_580154 := by
    simpa [prefixWord, tailWord_580154, baseEnd_580154] using wordTrace_append hprefix tailTrace_580154
  have hstable : (prefixWord ++ tailWord_580154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580154).length < 2 ^ (prefixWord ++ tailWord_580154).sum := by decide
  have hdescent : baseEnd_580154 < baseStart_580154 := by decide
  rcases family_descends (prefixWord ++ tailWord_580154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580164 : List Nat := [2, 3, 5, 1, 1, 1, 1, 6]
def baseStart_580164 : Nat := 118140960795 + 580164 * 2 ^ 59
def prefixEnd_580164 : Nat := 4983230072969 + 3 ^ 40 * 580164 * 2
def baseEnd_580164 : Nat := 88267552721532841298335

theorem tailTrace_580164 : CollatzResearch.WordTrace tailWord_580164 prefixEnd_580164 88267552721532841298335 := by
  unfold tailWord_580164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10580159735086193483909773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14106879646781591311879697 10580159735086193483909773)
  ·
    refine ⟨3967559900657322556466165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10580159735086193483909773 3967559900657322556466165)
    ·
      refine ⟨371958740686623989668703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3967559900657322556466165 371958740686623989668703)
      ·
        refine ⟨557938111029935984503055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371958740686623989668703 557938111029935984503055)
        ·
          refine ⟨836907166544903976754583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557938111029935984503055 836907166544903976754583)
          ·
            refine ⟨1255360749817355965131875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836907166544903976754583 1255360749817355965131875)
            ·
              refine ⟨1883041124726033947697813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255360749817355965131875 1883041124726033947697813)
              ·
                refine ⟨88267552721532841298335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1883041124726033947697813 88267552721532841298335)
                ·
                  rfl

theorem cell20_580164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_580164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580164 prefixEnd_580164 := by exact prefixLift 580164
  have htrace : WordTrace (prefixWord ++ tailWord_580164) baseStart_580164 baseEnd_580164 := by
    simpa [prefixWord, tailWord_580164, baseEnd_580164] using wordTrace_append hprefix tailTrace_580164
  have hstable : (prefixWord ++ tailWord_580164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580164).length < 2 ^ (prefixWord ++ tailWord_580164).sum := by decide
  have hdescent : baseEnd_580164 < baseStart_580164 := by decide
  rcases family_descends (prefixWord ++ tailWord_580164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580196 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_580196 : Nat := 118140960795 + 580196 * 2 ^ 59
def prefixEnd_580196 : Nat := 4983230072969 + 3 ^ 40 * 580196 * 2
def baseEnd_580196 : Nat := 264817263836548634828207

theorem tailTrace_580196 : CollatzResearch.WordTrace tailWord_580196 prefixEnd_580196 264817263836548634828207 := by
  unfold tailWord_580196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10580743303028228216492221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14107657737370970955322961 10580743303028228216492221)
  ·
    refine ⟨3967778738635585581184583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10580743303028228216492221 3967778738635585581184583)
    ·
      refine ⟨5951668107953378371776875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3967778738635585581184583 5951668107953378371776875)
      ·
        refine ⟨8927502161930067557665313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951668107953378371776875 8927502161930067557665313)
        ·
          refine ⟨6695626621447550668248985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8927502161930067557665313 6695626621447550668248985)
          ·
            refine ⟨5021719966085663001186739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6695626621447550668248985 5021719966085663001186739)
            ·
              refine ⟨7532579949128494501780109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021719966085663001186739 7532579949128494501780109)
              ·
                refine ⟨2824717480923185438167541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7532579949128494501780109 2824717480923185438167541)
                ·
                  refine ⟨264817263836548634828207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2824717480923185438167541 264817263836548634828207)
                  ·
                    rfl

theorem cell20_580196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_580196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580196 prefixEnd_580196 := by exact prefixLift 580196
  have htrace : WordTrace (prefixWord ++ tailWord_580196) baseStart_580196 baseEnd_580196 := by
    simpa [prefixWord, tailWord_580196, baseEnd_580196] using wordTrace_append hprefix tailTrace_580196
  have hstable : (prefixWord ++ tailWord_580196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580196).length < 2 ^ (prefixWord ++ tailWord_580196).sum := by decide
  have hdescent : baseEnd_580196 < baseStart_580196 := by decide
  rcases family_descends (prefixWord ++ tailWord_580196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580203 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_580203 : Nat := 118140960795 + 580203 * 2 ^ 59
def prefixEnd_580203 : Nat := 4983230072969 + 3 ^ 40 * 580203 * 2
def baseEnd_580203 : Nat := 264820458827287721594845

theorem tailTrace_580203 : CollatzResearch.WordTrace tailWord_580203 prefixEnd_580203 264820458827287721594845 := by
  unfold tailWord_580203
  simp only [CollatzResearch.WordTrace]
  refine ⟨21161741917031096628489263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14107827944687397752326175 21161741917031096628489263)
  ·
    refine ⟨31742612875546644942733895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21161741917031096628489263 31742612875546644942733895)
    ·
      refine ⟨47613919313319967414100843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31742612875546644942733895 47613919313319967414100843)
      ·
        refine ⟨71420878969979951121151265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47613919313319967414100843 71420878969979951121151265)
        ·
          refine ⟨53565659227484963340863449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71420878969979951121151265 53565659227484963340863449)
          ·
            refine ⟨40174244420613722505647587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53565659227484963340863449 40174244420613722505647587)
            ·
              refine ⟨60261366630920583758471381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40174244420613722505647587 60261366630920583758471381)
              ·
                refine ⟨1412375780412201181839173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60261366630920583758471381 1412375780412201181839173)
                ·
                  refine ⟨264820458827287721594845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412375780412201181839173 264820458827287721594845)
                  ·
                    rfl

theorem cell20_580203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_580203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580203 prefixEnd_580203 := by exact prefixLift 580203
  have htrace : WordTrace (prefixWord ++ tailWord_580203) baseStart_580203 baseEnd_580203 := by
    simpa [prefixWord, tailWord_580203, baseEnd_580203] using wordTrace_append hprefix tailTrace_580203
  have hstable : (prefixWord ++ tailWord_580203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580203).length < 2 ^ (prefixWord ++ tailWord_580203).sum := by decide
  have hdescent : baseEnd_580203 < baseStart_580203 := by decide
  rcases family_descends (prefixWord ++ tailWord_580203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580206 : List Nat := [4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_580206 : Nat := 118140960795 + 580206 * 2 ^ 59
def prefixEnd_580206 : Nat := 4983230072969 + 3 ^ 40 * 580206 * 2
def baseEnd_580206 : Nat := 88273942703011014831611

theorem tailTrace_580206 : CollatzResearch.WordTrace tailWord_580206 prefixEnd_580206 88273942703011014831611 := by
  unfold tailWord_580206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645231417002528517606059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14107900890680152093898981 2645231417002528517606059)
  ·
    refine ⟨3967847125503792776409089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645231417002528517606059 3967847125503792776409089)
    ·
      refine ⟨2975885344127844582306817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3967847125503792776409089 2975885344127844582306817)
      ·
        refine ⟨2231914008095883436730113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2975885344127844582306817 2231914008095883436730113)
        ·
          refine ⟨1673935506071912577547585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2231914008095883436730113 1673935506071912577547585)
          ·
            refine ⟨1255451629553934433160689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673935506071912577547585 1255451629553934433160689)
            ·
              refine ⟨941588722165450824870517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255451629553934433160689 941588722165450824870517)
              ·
                refine ⟨88273942703011014831611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 941588722165450824870517 88273942703011014831611)
                ·
                  rfl

theorem cell20_580206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_580206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580206 prefixEnd_580206 := by exact prefixLift 580206
  have htrace : WordTrace (prefixWord ++ tailWord_580206) baseStart_580206 baseEnd_580206 := by
    simpa [prefixWord, tailWord_580206, baseEnd_580206] using wordTrace_append hprefix tailTrace_580206
  have hstable : (prefixWord ++ tailWord_580206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580206).length < 2 ^ (prefixWord ++ tailWord_580206).sum := by decide
  have hdescent : baseEnd_580206 < baseStart_580206 := by decide
  rcases family_descends (prefixWord ++ tailWord_580206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580250 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_580250 : Nat := 118140960795 + 580250 * 2 ^ 59
def prefixEnd_580250 : Nat := 4983230072969 + 3 ^ 40 * 580250 * 2
def baseEnd_580250 : Nat := 264841910907964447027987

theorem tailTrace_580250 : CollatzResearch.WordTrace tailWord_580250 prefixEnd_580250 264841910907964447027987 := by
  unfold tailWord_580250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290864036965205913862551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14108970765240549103633469 5290864036965205913862551)
  ·
    refine ⟨7936296055447808870793827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5290864036965205913862551 7936296055447808870793827)
    ·
      refine ⟨11904444083171713306190741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7936296055447808870793827 11904444083171713306190741)
      ·
        refine ⟨558020816398674061227691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11904444083171713306190741 558020816398674061227691)
        ·
          refine ⟨837031224598011091841537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558020816398674061227691 837031224598011091841537)
          ·
            refine ⟨627773418448508318881153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837031224598011091841537 627773418448508318881153)
            ·
              refine ⟨470830063836381239160865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627773418448508318881153 470830063836381239160865)
              ·
                refine ⟨353122547877285929370649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470830063836381239160865 353122547877285929370649)
                ·
                  refine ⟨264841910907964447027987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353122547877285929370649 264841910907964447027987)
                  ·
                    rfl

theorem cell20_580250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_580250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580250 prefixEnd_580250 := by exact prefixLift 580250
  have htrace : WordTrace (prefixWord ++ tailWord_580250) baseStart_580250 baseEnd_580250 := by
    simpa [prefixWord, tailWord_580250, baseEnd_580250] using wordTrace_append hprefix tailTrace_580250
  have hstable : (prefixWord ++ tailWord_580250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580250).length < 2 ^ (prefixWord ++ tailWord_580250).sum := by decide
  have hdescent : baseEnd_580250 < baseStart_580250 := by decide
  rcases family_descends (prefixWord ++ tailWord_580250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580254 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_580254 : Nat := 118140960795 + 580254 * 2 ^ 59
def prefixEnd_580254 : Nat := 4983230072969 + 3 ^ 40 * 580254 * 2
def baseEnd_580254 : Nat := 264843736616958210894637

theorem tailTrace_580254 : CollatzResearch.WordTrace tailWord_580254 prefixEnd_580254 264843736616958210894637 := by
  unfold tailWord_580254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645450254980791542324477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14109068026564221559063877 2645450254980791542324477)
  ·
    refine ⟨992043845617796828371679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2645450254980791542324477 992043845617796828371679)
    ·
      refine ⟨1488065768426695242557519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992043845617796828371679 1488065768426695242557519)
      ·
        refine ⟨2232098652640042863836279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488065768426695242557519 2232098652640042863836279)
        ·
          refine ⟨3348147978960064295754419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232098652640042863836279 3348147978960064295754419)
          ·
            refine ⟨5022221968440096443631629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348147978960064295754419 5022221968440096443631629)
            ·
              refine ⟨1883333238165036166361861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5022221968440096443631629 1883333238165036166361861)
              ·
                refine ⟨353124982155944281192849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1883333238165036166361861 353124982155944281192849)
                ·
                  refine ⟨264843736616958210894637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353124982155944281192849 264843736616958210894637)
                  ·
                    rfl

theorem cell20_580254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_580254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580254 prefixEnd_580254 := by exact prefixLift 580254
  have htrace : WordTrace (prefixWord ++ tailWord_580254) baseStart_580254 baseEnd_580254 := by
    simpa [prefixWord, tailWord_580254, baseEnd_580254] using wordTrace_append hprefix tailTrace_580254
  have hstable : (prefixWord ++ tailWord_580254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580254).length < 2 ^ (prefixWord ++ tailWord_580254).sum := by decide
  have hdescent : baseEnd_580254 < baseStart_580254 := by decide
  rcases family_descends (prefixWord ++ tailWord_580254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580278 : List Nat := [5, 1, 3, 1, 2, 1, 3, 4]
def baseStart_580278 : Nat := 118140960795 + 580278 * 2 ^ 59
def prefixEnd_580278 : Nat := 4983230072969 + 3 ^ 40 * 580278 * 2
def baseEnd_580278 : Nat := 88284896956973598031513

theorem tailTrace_580278 : CollatzResearch.WordTrace tailWord_580278 prefixEnd_580278 88284896956973598031513 := by
  unfold tailWord_580278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322779836984961527341843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14109651594506256291646325 1322779836984961527341843)
  ·
    refine ⟨1984169755477442291012765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322779836984961527341843 1984169755477442291012765)
    ·
      refine ⟨744063658304040859129787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1984169755477442291012765 744063658304040859129787)
      ·
        refine ⟨1116095487456061288694681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744063658304040859129787 1116095487456061288694681)
        ·
          refine ⟨837071615592045966521011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116095487456061288694681 837071615592045966521011)
          ·
            refine ⟨1255607423388068949781517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837071615592045966521011 1255607423388068949781517)
            ·
              refine ⟨470852783770525856168069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1255607423388068949781517 470852783770525856168069)
              ·
                refine ⟨88284896956973598031513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470852783770525856168069 88284896956973598031513)
                ·
                  rfl

theorem cell20_580278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_580278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580278 prefixEnd_580278 := by exact prefixLift 580278
  have htrace : WordTrace (prefixWord ++ tailWord_580278) baseStart_580278 baseEnd_580278 := by
    simpa [prefixWord, tailWord_580278, baseEnd_580278] using wordTrace_append hprefix tailTrace_580278
  have hstable : (prefixWord ++ tailWord_580278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580278).length < 2 ^ (prefixWord ++ tailWord_580278).sum := by decide
  have hdescent : baseEnd_580278 < baseStart_580278 := by decide
  rcases family_descends (prefixWord ++ tailWord_580278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580292 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 2]
def baseStart_580292 : Nat := 118140960795 + 580292 * 2 ^ 59
def prefixEnd_580292 : Nat := 4983230072969 + 3 ^ 40 * 580292 * 2
def baseEnd_580292 : Nat := 264861080852398967627815

theorem tailTrace_580292 : CollatzResearch.WordTrace tailWord_580292 prefixEnd_580292 264861080852398967627815 := by
  unfold tailWord_580292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10582494006854332414239565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14109992009139109885652753 10582494006854332414239565)
  ·
    refine ⟨3968435252570374655339837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10582494006854332414239565 3968435252570374655339837)
    ·
      refine ⟨1488163219713890495752439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3968435252570374655339837 1488163219713890495752439)
      ·
        refine ⟨2232244829570835743628659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488163219713890495752439 2232244829570835743628659)
        ·
          refine ⟨3348367244356253615442989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232244829570835743628659 3348367244356253615442989)
          ·
            refine ⟨1255637716633595105791121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3348367244356253615442989 1255637716633595105791121)
            ·
              refine ⟨941728287475196329343341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255637716633595105791121 941728287475196329343341)
              ·
                refine ⟨353148107803198623503753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 941728287475196329343341 353148107803198623503753)
                ·
                  refine ⟨264861080852398967627815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353148107803198623503753 264861080852398967627815)
                  ·
                    rfl

theorem cell20_580292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_580292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580292 prefixEnd_580292 := by exact prefixLift 580292
  have htrace : WordTrace (prefixWord ++ tailWord_580292) baseStart_580292 baseEnd_580292 := by
    simpa [prefixWord, tailWord_580292, baseEnd_580292] using wordTrace_append hprefix tailTrace_580292
  have hstable : (prefixWord ++ tailWord_580292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580292).length < 2 ^ (prefixWord ++ tailWord_580292).sum := by decide
  have hdescent : baseEnd_580292 < baseStart_580292 := by decide
  rcases family_descends (prefixWord ++ tailWord_580292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580334 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_580334 : Nat := 118140960795 + 580334 * 2 ^ 59
def prefixEnd_580334 : Nat := 4983230072969 + 3 ^ 40 * 580334 * 2
def baseEnd_580334 : Nat := 264880250796833488227643

theorem tailTrace_580334 : CollatzResearch.WordTrace tailWord_580334 prefixEnd_580334 264880250796833488227643 := by
  unfold tailWord_580334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645814984944563250188507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14111013253037670667672037 2645814984944563250188507)
  ·
    refine ⟨3968722477416844875282761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645814984944563250188507 3968722477416844875282761)
    ·
      refine ⟨2976541858062633656462071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3968722477416844875282761 2976541858062633656462071)
      ·
        refine ⟨4464812787093950484693107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2976541858062633656462071 4464812787093950484693107)
        ·
          refine ⟨6697219180640925727039661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464812787093950484693107 6697219180640925727039661)
          ·
            refine ⟨2511457192740347147639873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6697219180640925727039661 2511457192740347147639873)
            ·
              refine ⟨1883592894555260360729905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511457192740347147639873 1883592894555260360729905)
              ·
                refine ⟨1412694670916445270547429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883592894555260360729905 1412694670916445270547429)
                ·
                  refine ⟨264880250796833488227643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412694670916445270547429 264880250796833488227643)
                  ·
                    rfl

theorem cell20_580334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_580334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580334 prefixEnd_580334 := by exact prefixLift 580334
  have htrace : WordTrace (prefixWord ++ tailWord_580334) baseStart_580334 baseEnd_580334 := by
    simpa [prefixWord, tailWord_580334, baseEnd_580334] using wordTrace_append hprefix tailTrace_580334
  have hstable : (prefixWord ++ tailWord_580334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580334).length < 2 ^ (prefixWord ++ tailWord_580334).sum := by decide
  have hdescent : baseEnd_580334 < baseStart_580334 := by decide
  rcases family_descends (prefixWord ++ tailWord_580334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580348 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_580348 : Nat := 118140960795 + 580348 * 2 ^ 59
def prefixEnd_580348 : Nat := 4983230072969 + 3 ^ 40 * 580348 * 2
def baseEnd_580348 : Nat := 264886640778311661760919

theorem tailTrace_580348 : CollatzResearch.WordTrace tailWord_580348 prefixEnd_580348 264886640778311661760919 := by
  unfold tailWord_580348
  simp only [CollatzResearch.WordTrace]
  refine ⟨10583515250752893196258849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14111353667670524261678465 10583515250752893196258849)
  ·
    refine ⟨7937636438064669897194137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10583515250752893196258849 7937636438064669897194137)
    ·
      refine ⟨5953227328548502422895603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7937636438064669897194137 5953227328548502422895603)
      ·
        refine ⟨8929840992822753634343405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5953227328548502422895603 8929840992822753634343405)
        ·
          refine ⟨3348690372308532612878777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8929840992822753634343405 3348690372308532612878777)
          ·
            refine ⟨2511517779231399459659083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3348690372308532612878777 2511517779231399459659083)
            ·
              refine ⟨3767276668847099189488625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511517779231399459659083 3767276668847099189488625)
              ·
                refine ⟨2825457501635324392116469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3767276668847099189488625 2825457501635324392116469)
                ·
                  refine ⟨264886640778311661760919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2825457501635324392116469 264886640778311661760919)
                  ·
                    rfl

theorem cell20_580348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_580348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580348 prefixEnd_580348 := by exact prefixLift 580348
  have htrace : WordTrace (prefixWord ++ tailWord_580348) baseStart_580348 baseEnd_580348 := by
    simpa [prefixWord, tailWord_580348, baseEnd_580348] using wordTrace_append hprefix tailTrace_580348
  have hstable : (prefixWord ++ tailWord_580348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580348).length < 2 ^ (prefixWord ++ tailWord_580348).sum := by decide
  have hdescent : baseEnd_580348 < baseStart_580348 := by decide
  rcases family_descends (prefixWord ++ tailWord_580348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580417 : List Nat := [1, 2, 5, 3, 9]
def baseStart_580417 : Nat := 118140960795 + 580417 * 2 ^ 59
def prefixEnd_580417 : Nat := 4983230072969 + 3 ^ 40 * 580417 * 2
def baseEnd_580417 : Nat := 3270594250104371462477

theorem tailTrace_580417 : CollatzResearch.WordTrace tailWord_580417 prefixEnd_580417 3270594250104371462477 := by
  unfold tailWord_580417
  simp only [CollatzResearch.WordTrace]
  refine ⟨21169547138255811176779505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14113031425503874117853003 21169547138255811176779505)
  ·
    refine ⟨15877160353691858382584629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21169547138255811176779505 15877160353691858382584629)
    ·
      refine ⟨1488483783158611723367309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15877160353691858382584629 1488483783158611723367309)
      ·
        refine ⟨558181418684479396262741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1488483783158611723367309 558181418684479396262741)
        ·
          refine ⟨3270594250104371462477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 558181418684479396262741 3270594250104371462477)
          ·
            rfl

theorem cell20_580417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 9].length) (baseStart_580417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580417 prefixEnd_580417 := by exact prefixLift 580417
  have htrace : WordTrace (prefixWord ++ tailWord_580417) baseStart_580417 baseEnd_580417 := by
    simpa [prefixWord, tailWord_580417, baseEnd_580417] using wordTrace_append hprefix tailTrace_580417
  have hstable : (prefixWord ++ tailWord_580417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580417).length < 2 ^ (prefixWord ++ tailWord_580417).sum := by decide
  have hdescent : baseEnd_580417 < baseStart_580417 := by decide
  rcases family_descends (prefixWord ++ tailWord_580417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580465 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 2]
def baseStart_580465 : Nat := 118140960795 + 580465 * 2 ^ 59
def prefixEnd_580465 : Nat := 4983230072969 + 3 ^ 40 * 580465 * 2
def baseEnd_580465 : Nat := 264940042766379254860441

theorem tailTrace_580465 : CollatzResearch.WordTrace tailWord_580465 prefixEnd_580465 264940042766379254860441 := by
  unfold tailWord_580465
  simp only [CollatzResearch.WordTrace]
  refine ⟨21171297842081915374526849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14114198561387943583017899 21171297842081915374526849)
  ·
    refine ⟨15878473381561436530895137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21171297842081915374526849 15878473381561436530895137)
    ·
      refine ⟨11908855036171077398171353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15878473381561436530895137 11908855036171077398171353)
      ·
        refine ⟨8931641277128308048628515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11908855036171077398171353 8931641277128308048628515)
        ·
          refine ⟨13397461915692462072942773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8931641277128308048628515 13397461915692462072942773)
          ·
            refine ⟨1256012054596168319338385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13397461915692462072942773 1256012054596168319338385)
            ·
              refine ⟨942009040947126239503789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256012054596168319338385 942009040947126239503789)
              ·
                refine ⟨353253390355172339813921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942009040947126239503789 353253390355172339813921)
                ·
                  refine ⟨264940042766379254860441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353253390355172339813921 264940042766379254860441)
                  ·
                    rfl

theorem cell20_580465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_580465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580465 prefixEnd_580465 := by exact prefixLift 580465
  have htrace : WordTrace (prefixWord ++ tailWord_580465) baseStart_580465 baseEnd_580465 := by
    simpa [prefixWord, tailWord_580465, baseEnd_580465] using wordTrace_append hprefix tailTrace_580465
  have hstable : (prefixWord ++ tailWord_580465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580465).length < 2 ^ (prefixWord ++ tailWord_580465).sum := by decide
  have hdescent : baseEnd_580465 < baseStart_580465 := by decide
  rcases family_descends (prefixWord ++ tailWord_580465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580521 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_580521 : Nat := 118140960795 + 580521 * 2 ^ 59
def prefixEnd_580521 : Nat := 4983230072969 + 3 ^ 40 * 580521 * 2
def baseEnd_580521 : Nat := 264965602692291948993545

theorem tailTrace_580521 : CollatzResearch.WordTrace tailWord_580521 prefixEnd_580521 264965602692291948993545 := by
  unfold tailWord_580521
  simp only [CollatzResearch.WordTrace]
  refine ⟨21173340329879036938565417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14115560219919357959043611 21173340329879036938565417)
  ·
    refine ⟨15880005247409277703924063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21173340329879036938565417 15880005247409277703924063)
    ·
      refine ⟨23820007871113916555886095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15880005247409277703924063 23820007871113916555886095)
      ·
        refine ⟨35730011806670874833829143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23820007871113916555886095 35730011806670874833829143)
        ·
          refine ⟨53595017710006312250743715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35730011806670874833829143 53595017710006312250743715)
          ·
            refine ⟨80392526565009468376115573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53595017710006312250743715 80392526565009468376115573)
            ·
              refine ⟨7536799365469637660260835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80392526565009468376115573 7536799365469637660260835)
              ·
                refine ⟨11305199048204456490391253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7536799365469637660260835 11305199048204456490391253)
                ·
                  refine ⟨264965602692291948993545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11305199048204456490391253 264965602692291948993545)
                  ·
                    rfl

theorem cell20_580521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_580521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580521 prefixEnd_580521 := by exact prefixLift 580521
  have htrace : WordTrace (prefixWord ++ tailWord_580521) baseStart_580521 baseEnd_580521 := by
    simpa [prefixWord, tailWord_580521, baseEnd_580521] using wordTrace_append hprefix tailTrace_580521
  have hstable : (prefixWord ++ tailWord_580521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580521).length < 2 ^ (prefixWord ++ tailWord_580521).sum := by decide
  have hdescent : baseEnd_580521 < baseStart_580521 := by decide
  rcases family_descends (prefixWord ++ tailWord_580521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580538 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_580538 : Nat := 118140960795 + 580538 * 2 ^ 59
def prefixEnd_580538 : Nat := 4983230072969 + 3 ^ 40 * 580538 * 2
def baseEnd_580538 : Nat := 264973361955515445426809

theorem tailTrace_580538 : CollatzResearch.WordTrace tailWord_580538 prefixEnd_580538 264973361955515445426809 := by
  unfold tailWord_580538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293490092704362210483567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14115973580544965894622845 5293490092704362210483567)
  ·
    refine ⟨7940235139056543315725351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5293490092704362210483567 7940235139056543315725351)
    ·
      refine ⟨11910352708584814973588027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7940235139056543315725351 11910352708584814973588027)
      ·
        refine ⟨17865529062877222460382041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11910352708584814973588027 17865529062877222460382041)
        ·
          refine ⟨13399146797157916845286531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17865529062877222460382041 13399146797157916845286531)
          ·
            refine ⟨20098720195736875267929797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13399146797157916845286531 20098720195736875267929797)
            ·
              refine ⟨3768510036700664112736837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20098720195736875267929797 3768510036700664112736837)
              ·
                refine ⟨706595631881374521138157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3768510036700664112736837 706595631881374521138157)
                ·
                  refine ⟨264973361955515445426809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706595631881374521138157 264973361955515445426809)
                  ·
                    rfl

theorem cell20_580538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_580538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580538 prefixEnd_580538 := by exact prefixLift 580538
  have htrace : WordTrace (prefixWord ++ tailWord_580538) baseStart_580538 baseEnd_580538 := by
    simpa [prefixWord, tailWord_580538, baseEnd_580538] using wordTrace_append hprefix tailTrace_580538
  have hstable : (prefixWord ++ tailWord_580538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580538).length < 2 ^ (prefixWord ++ tailWord_580538).sum := by decide
  have hdescent : baseEnd_580538 < baseStart_580538 := by decide
  rcases family_descends (prefixWord ++ tailWord_580538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580541 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 4]
def baseStart_580541 : Nat := 118140960795 + 580541 * 2 ^ 59
def prefixEnd_580541 : Nat := 4983230072969 + 3 ^ 40 * 580541 * 2
def baseEnd_580541 : Nat := 264974731237260768326797

theorem tailTrace_580541 : CollatzResearch.WordTrace tailWord_580541 prefixEnd_580541 264974731237260768326797 := by
  unfold tailWord_580541
  simp only [CollatzResearch.WordTrace]
  refine ⟨21174069789806580354293477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14116046526537720236195651 21174069789806580354293477)
  ·
    refine ⟨3970138085588733816430027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21174069789806580354293477 3970138085588733816430027)
    ·
      refine ⟨5955207128383100724645041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970138085588733816430027 5955207128383100724645041)
      ·
        refine ⟨4466405346287325543483781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5955207128383100724645041 4466405346287325543483781)
        ·
          refine ⟨837451002428873539403209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4466405346287325543483781 837451002428873539403209)
          ·
            refine ⟨628088251821655154552407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837451002428873539403209 628088251821655154552407)
            ·
              refine ⟨942132377732482731828611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628088251821655154552407 942132377732482731828611)
              ·
                refine ⟨1413198566598724097742917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942132377732482731828611 1413198566598724097742917)
                ·
                  refine ⟨264974731237260768326797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413198566598724097742917 264974731237260768326797)
                  ·
                    rfl

theorem cell20_580541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_580541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580541 prefixEnd_580541 := by exact prefixLift 580541
  have htrace : WordTrace (prefixWord ++ tailWord_580541) baseStart_580541 baseEnd_580541 := by
    simpa [prefixWord, tailWord_580541, baseEnd_580541] using wordTrace_append hprefix tailTrace_580541
  have hstable : (prefixWord ++ tailWord_580541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580541).length < 2 ^ (prefixWord ++ tailWord_580541).sum := by decide
  have hdescent : baseEnd_580541 < baseStart_580541 := by decide
  rcases family_descends (prefixWord ++ tailWord_580541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580555 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 3]
def baseStart_580555 : Nat := 118140960795 + 580555 * 2 ^ 59
def prefixEnd_580555 : Nat := 4983230072969 + 3 ^ 40 * 580555 * 2
def baseEnd_580555 : Nat := 264981121218738941860073

theorem tailTrace_580555 : CollatzResearch.WordTrace tailWord_580555 prefixEnd_580555 264981121218738941860073 := by
  unfold tailWord_580555
  simp only [CollatzResearch.WordTrace]
  refine ⟨21174580411755860745303119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14116386941170573830202079 21174580411755860745303119)
  ·
    refine ⟨31761870617633791117954679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21174580411755860745303119 31761870617633791117954679)
    ·
      refine ⟨47642805926450686676932019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31761870617633791117954679 47642805926450686676932019)
      ·
        refine ⟨71464208889676030015398029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47642805926450686676932019 71464208889676030015398029)
        ·
          refine ⟨26799078333628511255774261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71464208889676030015398029 26799078333628511255774261)
          ·
            refine ⟨2512413593777672930228837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26799078333628511255774261 2512413593777672930228837)
            ·
              refine ⟨471077548833313674417907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2512413593777672930228837 471077548833313674417907)
              ·
                refine ⟨706616323249970511626861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471077548833313674417907 706616323249970511626861)
                ·
                  refine ⟨264981121218738941860073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706616323249970511626861 264981121218738941860073)
                  ·
                    rfl

theorem cell20_580555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_580555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580555 prefixEnd_580555 := by exact prefixLift 580555
  have htrace : WordTrace (prefixWord ++ tailWord_580555) baseStart_580555 baseEnd_580555 := by
    simpa [prefixWord, tailWord_580555, baseEnd_580555] using wordTrace_append hprefix tailTrace_580555
  have hstable : (prefixWord ++ tailWord_580555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580555).length < 2 ^ (prefixWord ++ tailWord_580555).sum := by decide
  have hdescent : baseEnd_580555 < baseStart_580555 := by decide
  rcases family_descends (prefixWord ++ tailWord_580555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580590 : List Nat := [4, 1, 2, 1, 12]
def baseStart_580590 : Nat := 118140960795 + 580590 * 2 ^ 59
def prefixEnd_580590 : Nat := 4983230072969 + 3 ^ 40 * 580590 * 2
def baseEnd_580590 : Nat := 3271569088548572539423

theorem tailTrace_580590 : CollatzResearch.WordTrace tailWord_580590 prefixEnd_580590 3271569088548572539423 := by
  unfold tailWord_580590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646982120828632715353403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14117237977752707815218149 2646982120828632715353403)
  ·
    refine ⟨3970473181242949073030105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646982120828632715353403 3970473181242949073030105)
    ·
      refine ⟨2977854885932211804772579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3970473181242949073030105 2977854885932211804772579)
      ·
        refine ⟨4466782328898317707158869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2977854885932211804772579 4466782328898317707158869)
        ·
          refine ⟨3271569088548572539423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4466782328898317707158869 3271569088548572539423)
          ·
            rfl

theorem cell20_580590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 12].length) (baseStart_580590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580590 prefixEnd_580590 := by exact prefixLift 580590
  have htrace : WordTrace (prefixWord ++ tailWord_580590) baseStart_580590 baseEnd_580590 := by
    simpa [prefixWord, tailWord_580590, baseEnd_580590] using wordTrace_append hprefix tailTrace_580590
  have hstable : (prefixWord ++ tailWord_580590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580590).length < 2 ^ (prefixWord ++ tailWord_580590).sum := by decide
  have hdescent : baseEnd_580590 < baseStart_580590 := by decide
  rcases family_descends (prefixWord ++ tailWord_580590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580593 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_580593 : Nat := 118140960795 + 580593 * 2 ^ 59
def prefixEnd_580593 : Nat := 4983230072969 + 3 ^ 40 * 580593 * 2
def baseEnd_580593 : Nat := 264998465454179698593251

theorem tailTrace_580593 : CollatzResearch.WordTrace tailWord_580593 prefixEnd_580593 264998465454179698593251 := by
  unfold tailWord_580593
  simp only [CollatzResearch.WordTrace]
  refine ⟨21175966385618193235186433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14117310923745462156790955 21175966385618193235186433)
  ·
    refine ⟨15881974789213644926389825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21175966385618193235186433 15881974789213644926389825)
    ·
      refine ⟨11911481091910233694792369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15881974789213644926389825 11911481091910233694792369)
      ·
        refine ⟨8933610818932675271094277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11911481091910233694792369 8933610818932675271094277)
        ·
          refine ⟨1675052028549876613330177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8933610818932675271094277 1675052028549876613330177)
          ·
            refine ⟨1256289021412407459997633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1675052028549876613330177 1256289021412407459997633)
            ·
              refine ⟨942216766059305594998225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256289021412407459997633 942216766059305594998225)
              ·
                refine ⟨706662574544479196248669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942216766059305594998225 706662574544479196248669)
                ·
                  refine ⟨264998465454179698593251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706662574544479196248669 264998465454179698593251)
                  ·
                    rfl

theorem cell20_580593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_580593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580593 prefixEnd_580593 := by exact prefixLift 580593
  have htrace : WordTrace (prefixWord ++ tailWord_580593) baseStart_580593 baseEnd_580593 := by
    simpa [prefixWord, tailWord_580593, baseEnd_580593] using wordTrace_append hprefix tailTrace_580593
  have hstable : (prefixWord ++ tailWord_580593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580593).length < 2 ^ (prefixWord ++ tailWord_580593).sum := by decide
  have hdescent : baseEnd_580593 < baseStart_580593 := by decide
  rcases family_descends (prefixWord ++ tailWord_580593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580690 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_580690 : Nat := 118140960795 + 580690 * 2 ^ 59
def prefixEnd_580690 : Nat := 4983230072969 + 3 ^ 40 * 580690 * 2
def baseEnd_580690 : Nat := 265042738897278472359521

theorem tailTrace_580690 : CollatzResearch.WordTrace tailWord_580690 prefixEnd_580690 265042738897278472359521 := by
  unfold tailWord_580690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294876066566694700366881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14119669510844519200978349 5294876066566694700366881)
  ·
    refine ⟨3971157049925021025275161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5294876066566694700366881 3971157049925021025275161)
    ·
      refine ⟨2978367787443765768956371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3971157049925021025275161 2978367787443765768956371)
      ·
        refine ⟨4467551681165648653434557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978367787443765768956371 4467551681165648653434557)
        ·
          refine ⟨1675331880437118245037959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4467551681165648653434557 1675331880437118245037959)
          ·
            refine ⟨2512997820655677367556939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675331880437118245037959 2512997820655677367556939)
            ·
              refine ⟨3769496730983516051335409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512997820655677367556939 3769496730983516051335409)
              ·
                refine ⟨2827122548237637038501557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3769496730983516051335409 2827122548237637038501557)
                ·
                  refine ⟨265042738897278472359521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827122548237637038501557 265042738897278472359521)
                  ·
                    rfl

theorem cell20_580690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_580690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580690 prefixEnd_580690 := by exact prefixLift 580690
  have htrace : WordTrace (prefixWord ++ tailWord_580690) baseStart_580690 baseEnd_580690 := by
    simpa [prefixWord, tailWord_580690, baseEnd_580690] using wordTrace_append hprefix tailTrace_580690
  have hstable : (prefixWord ++ tailWord_580690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580690).length < 2 ^ (prefixWord ++ tailWord_580690).sum := by decide
  have hdescent : baseEnd_580690 < baseStart_580690 := by decide
  rcases family_descends (prefixWord ++ tailWord_580690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580714 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_580714 : Nat := 118140960795 + 580714 * 2 ^ 59
def prefixEnd_580714 : Nat := 4983230072969 + 3 ^ 40 * 580714 * 2
def baseEnd_580714 : Nat := 265053693151241055559423

theorem tailTrace_580714 : CollatzResearch.WordTrace tailWord_580714 prefixEnd_580714 265053693151241055559423 := by
  unfold tailWord_580714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5295094904544957725085299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14120253078786553933560797 5295094904544957725085299)
  ·
    refine ⟨7942642356817436587627949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5295094904544957725085299 7942642356817436587627949)
    ·
      refine ⟨2978490883806538720360481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7942642356817436587627949 2978490883806538720360481)
      ·
        refine ⟨2233868162854904040270361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2978490883806538720360481 2233868162854904040270361)
        ·
          refine ⟨1675401122141178030202771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2233868162854904040270361 1675401122141178030202771)
          ·
            refine ⟨2513101683211767045304157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675401122141178030202771 2513101683211767045304157)
            ·
              refine ⟨942413131204412641989059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2513101683211767045304157 942413131204412641989059)
              ·
                refine ⟨1413619696806618962983589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942413131204412641989059 1413619696806618962983589)
                ·
                  refine ⟨265053693151241055559423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413619696806618962983589 265053693151241055559423)
                  ·
                    rfl

theorem cell20_580714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_580714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580714 prefixEnd_580714 := by exact prefixLift 580714
  have htrace : WordTrace (prefixWord ++ tailWord_580714) baseStart_580714 baseEnd_580714 := by
    simpa [prefixWord, tailWord_580714, baseEnd_580714] using wordTrace_append hprefix tailTrace_580714
  have hstable : (prefixWord ++ tailWord_580714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580714).length < 2 ^ (prefixWord ++ tailWord_580714).sum := by decide
  have hdescent : baseEnd_580714 < baseStart_580714 := by decide
  rcases family_descends (prefixWord ++ tailWord_580714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580818 : List Nat := [3, 2, 2, 2, 1, 1, 9]
def baseStart_580818 : Nat := 118140960795 + 580818 * 2 ^ 59
def prefixEnd_580818 : Nat := 4983230072969 + 3 ^ 40 * 580818 * 2
def baseEnd_580818 : Nat := 29455684620564324010259

theorem tailTrace_580818 : CollatzResearch.WordTrace tailWord_580818 prefixEnd_580818 29455684620564324010259 := by
  unfold tailWord_580818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5296043202450764165531777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14122781873202037774751405 5296043202450764165531777)
  ·
    refine ⟨3972032401838073124148833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5296043202450764165531777 3972032401838073124148833)
    ·
      refine ⟨2979024301378554843111625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3972032401838073124148833 2979024301378554843111625)
      ·
        refine ⟨2234268226033916132333719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2979024301378554843111625 2234268226033916132333719)
        ·
          refine ⟨3351402339050874198500579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234268226033916132333719 3351402339050874198500579)
          ·
            refine ⟨5027103508576311297750869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351402339050874198500579 5027103508576311297750869)
            ·
              refine ⟨29455684620564324010259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5027103508576311297750869 29455684620564324010259)
              ·
                rfl

theorem cell20_580818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_580818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580818 prefixEnd_580818 := by exact prefixLift 580818
  have htrace : WordTrace (prefixWord ++ tailWord_580818) baseStart_580818 baseEnd_580818 := by
    simpa [prefixWord, tailWord_580818, baseEnd_580818] using wordTrace_append hprefix tailTrace_580818
  have hstable : (prefixWord ++ tailWord_580818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580818).length < 2 ^ (prefixWord ++ tailWord_580818).sum := by decide
  have hdescent : baseEnd_580818 < baseStart_580818 := by decide
  rcases family_descends (prefixWord ++ tailWord_580818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580821 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_580821 : Nat := 118140960795 + 580821 * 2 ^ 59
def prefixEnd_580821 : Nat := 4983230072969 + 3 ^ 40 * 580821 * 2
def baseEnd_580821 : Nat := 265102530866824238992319

theorem tailTrace_580821 : CollatzResearch.WordTrace tailWord_580821 prefixEnd_580821 265102530866824238992319 := by
  unfold tailWord_580821
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184282228792188174486317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14122854819194792116324211 21184282228792188174486317)
  ·
    refine ⟨7944105835797070565432369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21184282228792188174486317 7944105835797070565432369)
    ·
      refine ⟨5958079376847802924074277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7944105835797070565432369 5958079376847802924074277)
      ·
        refine ⟨1117139883158963048263927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5958079376847802924074277 1117139883158963048263927)
        ·
          refine ⟨1675709824738444572395891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117139883158963048263927 1675709824738444572395891)
          ·
            refine ⟨2513564737107666858593837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675709824738444572395891 2513564737107666858593837)
            ·
              refine ⟨942586776415375071972689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2513564737107666858593837 942586776415375071972689)
              ·
                refine ⟨706940082311531303979517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942586776415375071972689 706940082311531303979517)
                ·
                  refine ⟨265102530866824238992319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706940082311531303979517 265102530866824238992319)
                  ·
                    rfl

theorem cell20_580821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_580821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580821 prefixEnd_580821 := by exact prefixLift 580821
  have htrace : WordTrace (prefixWord ++ tailWord_580821) baseStart_580821 baseEnd_580821 := by
    simpa [prefixWord, tailWord_580821, baseEnd_580821] using wordTrace_append hprefix tailTrace_580821
  have hstable : (prefixWord ++ tailWord_580821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580821).length < 2 ^ (prefixWord ++ tailWord_580821).sum := by decide
  have hdescent : baseEnd_580821 < baseStart_580821 := by decide
  rcases family_descends (prefixWord ++ tailWord_580821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580862 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_580862 : Nat := 118140960795 + 580862 * 2 ^ 59
def prefixEnd_580862 : Nat := 4983230072969 + 3 ^ 40 * 580862 * 2
def baseEnd_580862 : Nat := 265121244384010318625485

theorem tailTrace_580862 : CollatzResearch.WordTrace tailWord_580862 prefixEnd_580862 265121244384010318625485 := by
  unfold tailWord_580862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648222202705456522091105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14123851747762434784485893 2648222202705456522091105)
  ·
    refine ⟨1986166652029092391568329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2648222202705456522091105 1986166652029092391568329)
    ·
      refine ⟨1489624989021819293676247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1986166652029092391568329 1489624989021819293676247)
      ·
        refine ⟨2234437483532728940514371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489624989021819293676247 2234437483532728940514371)
        ·
          refine ⟨3351656225299093410771557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234437483532728940514371 3351656225299093410771557)
          ·
            refine ⟨628435542243580014519667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3351656225299093410771557 628435542243580014519667)
            ·
              refine ⟨942653313365370021779501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628435542243580014519667 942653313365370021779501)
              ·
                refine ⟨353494992512013758167313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942653313365370021779501 353494992512013758167313)
                ·
                  refine ⟨265121244384010318625485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353494992512013758167313 265121244384010318625485)
                  ·
                    rfl

theorem cell20_580862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_580862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580862 prefixEnd_580862 := by exact prefixLift 580862
  have htrace : WordTrace (prefixWord ++ tailWord_580862) baseStart_580862 baseEnd_580862 := by
    simpa [prefixWord, tailWord_580862, baseEnd_580862] using wordTrace_append hprefix tailTrace_580862
  have hstable : (prefixWord ++ tailWord_580862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580862).length < 2 ^ (prefixWord ++ tailWord_580862).sum := by decide
  have hdescent : baseEnd_580862 < baseStart_580862 := by decide
  rcases family_descends (prefixWord ++ tailWord_580862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580863 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_580863 : Nat := 118140960795 + 580863 * 2 ^ 59
def prefixEnd_580863 : Nat := 4983230072969 + 3 ^ 40 * 580863 * 2
def baseEnd_580863 : Nat := 265121700811258759592147

theorem tailTrace_580863 : CollatzResearch.WordTrace tailWord_580863 prefixEnd_580863 265121700811258759592147 := by
  unfold tailWord_580863
  simp only [CollatzResearch.WordTrace]
  refine ⟨21185814094640029347515243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14123876063093352898343495 21185814094640029347515243)
  ·
    refine ⟨31778721141960044021272865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21185814094640029347515243 31778721141960044021272865)
    ·
      refine ⟨23834040856470033015954649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31778721141960044021272865 23834040856470033015954649)
      ·
        refine ⟨17875530642352524761965987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23834040856470033015954649 17875530642352524761965987)
        ·
          refine ⟨26813295963528787142948981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17875530642352524761965987 26813295963528787142948981)
          ·
            refine ⟨2513746496580823794651467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26813295963528787142948981 2513746496580823794651467)
            ·
              refine ⟨3770619744871235691977201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513746496580823794651467 3770619744871235691977201)
              ·
                refine ⟨2827964808653426768982901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770619744871235691977201 2827964808653426768982901)
                ·
                  refine ⟨265121700811258759592147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827964808653426768982901 265121700811258759592147)
                  ·
                    rfl

theorem cell20_580863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_580863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580863 prefixEnd_580863 := by exact prefixLift 580863
  have htrace : WordTrace (prefixWord ++ tailWord_580863) baseStart_580863 baseEnd_580863 := by
    simpa [prefixWord, tailWord_580863, baseEnd_580863] using wordTrace_append hprefix tailTrace_580863
  have hstable : (prefixWord ++ tailWord_580863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580863).length < 2 ^ (prefixWord ++ tailWord_580863).sum := by decide
  have hdescent : baseEnd_580863 < baseStart_580863 := by decide
  rcases family_descends (prefixWord ++ tailWord_580863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580908 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_580908 : Nat := 118140960795 + 580908 * 2 ^ 59
def prefixEnd_580908 : Nat := 4983230072969 + 3 ^ 40 * 580908 * 2
def baseEnd_580908 : Nat := 265142240037438603091963

theorem tailTrace_580908 : CollatzResearch.WordTrace tailWord_580908 prefixEnd_580908 265142240037438603091963 := by
  unfold tailWord_580908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10593727689738501016451689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14124970252984668021935585 10593727689738501016451689)
  ·
    refine ⟨7945295767303875762338767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10593727689738501016451689 7945295767303875762338767)
    ·
      refine ⟨11917943650955813643508151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7945295767303875762338767 11917943650955813643508151)
      ·
        refine ⟨17876915476433720465262227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11917943650955813643508151 17876915476433720465262227)
        ·
          refine ⟨26815373214650580697893341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17876915476433720465262227 26815373214650580697893341)
          ·
            refine ⟨10055764955493967761710003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26815373214650580697893341 10055764955493967761710003)
            ·
              refine ⟨15083647433240951642565005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10055764955493967761710003 15083647433240951642565005)
              ·
                refine ⟨5656367787465356865961877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15083647433240951642565005 5656367787465356865961877)
                ·
                  refine ⟨265142240037438603091963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5656367787465356865961877 265142240037438603091963)
                  ·
                    rfl

theorem cell20_580908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_580908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580908 prefixEnd_580908 := by exact prefixLift 580908
  have htrace : WordTrace (prefixWord ++ tailWord_580908) baseStart_580908 baseEnd_580908 := by
    simpa [prefixWord, tailWord_580908, baseEnd_580908] using wordTrace_append hprefix tailTrace_580908
  have hstable : (prefixWord ++ tailWord_580908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580908).length < 2 ^ (prefixWord ++ tailWord_580908).sum := by decide
  have hdescent : baseEnd_580908 < baseStart_580908 := by decide
  rcases family_descends (prefixWord ++ tailWord_580908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580942 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_580942 : Nat := 118140960795 + 580942 * 2 ^ 59
def prefixEnd_580942 : Nat := 4983230072969 + 3 ^ 40 * 580942 * 2
def baseEnd_580942 : Nat := 265157758563885595958491

theorem tailTrace_580942 : CollatzResearch.WordTrace tailWord_580942 prefixEnd_580942 265157758563885595958491 := by
  unfold tailWord_580942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648586932669228229955135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14125796974235883893094053 2648586932669228229955135)
  ·
    refine ⟨3972880399003842344932703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2648586932669228229955135 3972880399003842344932703)
    ·
      refine ⟨5959320598505763517399055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3972880399003842344932703 5959320598505763517399055)
      ·
        refine ⟨8938980897758645276098583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959320598505763517399055 8938980897758645276098583)
        ·
          refine ⟨13408471346637967914147875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8938980897758645276098583 13408471346637967914147875)
          ·
            refine ⟨20112707019956951871221813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13408471346637967914147875 20112707019956951871221813)
            ·
              refine ⟨1885566283120964237927045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20112707019956951871221813 1885566283120964237927045)
              ·
                refine ⟨353543678085180794611321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1885566283120964237927045 353543678085180794611321)
                ·
                  refine ⟨265157758563885595958491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353543678085180794611321 265157758563885595958491)
                  ·
                    rfl

theorem cell20_580942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_580942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580942 prefixEnd_580942 := by exact prefixLift 580942
  have htrace : WordTrace (prefixWord ++ tailWord_580942) baseStart_580942 baseEnd_580942 := by
    simpa [prefixWord, tailWord_580942, baseEnd_580942] using wordTrace_append hprefix tailTrace_580942
  have hstable : (prefixWord ++ tailWord_580942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580942).length < 2 ^ (prefixWord ++ tailWord_580942).sum := by decide
  have hdescent : baseEnd_580942 < baseStart_580942 := by decide
  rcases family_descends (prefixWord ++ tailWord_580942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580949 : List Nat := [1, 3, 2, 2, 3, 3, 1, 5]
def baseStart_580949 : Nat := 118140960795 + 580949 * 2 ^ 59
def prefixEnd_580949 : Nat := 4983230072969 + 3 ^ 40 * 580949 * 2
def baseEnd_580949 : Nat := 88386984518208227575043

theorem tailTrace_580949 : CollatzResearch.WordTrace tailWord_580949 prefixEnd_580949 88386984518208227575043 := by
  unfold tailWord_580949
  simp only [CollatzResearch.WordTrace]
  refine ⟨21188950772328466035145901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14125967181552310690097267 21188950772328466035145901)
  ·
    refine ⟨7945856539623174763179713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21188950772328466035145901 7945856539623174763179713)
    ·
      refine ⟨5959392404717381072384785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7945856539623174763179713 5959392404717381072384785)
      ·
        refine ⟨4469544303538035804288589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5959392404717381072384785 4469544303538035804288589)
        ·
          refine ⟨1676079113826763426608221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4469544303538035804288589 1676079113826763426608221)
          ·
            refine ⟨628529667685036284978083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1676079113826763426608221 628529667685036284978083)
            ·
              refine ⟨942794501527554427467125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628529667685036284978083 942794501527554427467125)
              ·
                refine ⟨88386984518208227575043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 942794501527554427467125 88386984518208227575043)
                ·
                  rfl

theorem cell20_580949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_580949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580949 prefixEnd_580949 := by exact prefixLift 580949
  have htrace : WordTrace (prefixWord ++ tailWord_580949) baseStart_580949 baseEnd_580949 := by
    simpa [prefixWord, tailWord_580949, baseEnd_580949] using wordTrace_append hprefix tailTrace_580949
  have hstable : (prefixWord ++ tailWord_580949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580949).length < 2 ^ (prefixWord ++ tailWord_580949).sum := by decide
  have hdescent : baseEnd_580949 < baseStart_580949 := by decide
  rcases family_descends (prefixWord ++ tailWord_580949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580963 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_580963 : Nat := 118140960795 + 580963 * 2 ^ 59
def prefixEnd_580963 : Nat := 4983230072969 + 3 ^ 40 * 580963 * 2
def baseEnd_580963 : Nat := 265167343536102856258405

theorem tailTrace_580963 : CollatzResearch.WordTrace tailWord_580963 prefixEnd_580963 265167343536102856258405 := by
  unfold tailWord_580963
  simp only [CollatzResearch.WordTrace]
  refine ⟨21189461394277746426155543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14126307596185164284103695 21189461394277746426155543)
  ·
    refine ⟨31784192091416619639233315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21189461394277746426155543 31784192091416619639233315)
    ·
      refine ⟨47676288137124929458849973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31784192091416619639233315 47676288137124929458849973)
      ·
        refine ⟨4469652012855462136767185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47676288137124929458849973 4469652012855462136767185)
        ·
          refine ⟨3352239009641596602575389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4469652012855462136767185 3352239009641596602575389)
          ·
            refine ⟨1257089628615598725965771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3352239009641596602575389 1257089628615598725965771)
            ·
              refine ⟨1885634442923398088948657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257089628615598725965771 1885634442923398088948657)
              ·
                refine ⟨1414225832192548566711493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885634442923398088948657 1414225832192548566711493)
                ·
                  refine ⟨265167343536102856258405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414225832192548566711493 265167343536102856258405)
                  ·
                    rfl

theorem cell20_580963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_580963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580963 prefixEnd_580963 := by exact prefixLift 580963
  have htrace : WordTrace (prefixWord ++ tailWord_580963) baseStart_580963 baseEnd_580963 := by
    simpa [prefixWord, tailWord_580963, baseEnd_580963] using wordTrace_append hprefix tailTrace_580963
  have hstable : (prefixWord ++ tailWord_580963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580963).length < 2 ^ (prefixWord ++ tailWord_580963).sum := by decide
  have hdescent : baseEnd_580963 < baseStart_580963 := by decide
  rcases family_descends (prefixWord ++ tailWord_580963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580990 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_580990 : Nat := 118140960795 + 580990 * 2 ^ 59
def prefixEnd_580990 : Nat := 4983230072969 + 3 ^ 40 * 580990 * 2
def baseEnd_580990 : Nat := 265179667071810762358295

theorem tailTrace_580990 : CollatzResearch.WordTrace tailWord_580990 prefixEnd_580990 265179667071810762358295 := by
  unfold tailWord_580990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648805770647491254673553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14126964110119953358258949 2648805770647491254673553)
  ·
    refine ⟨1986604327985618441005165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2648805770647491254673553 1986604327985618441005165)
    ·
      refine ⟨744976622994606915376937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1986604327985618441005165 744976622994606915376937)
      ·
        refine ⟨558732467245955186532703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 744976622994606915376937 558732467245955186532703)
        ·
          refine ⟨838098700868932779799055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558732467245955186532703 838098700868932779799055)
          ·
            refine ⟨1257148051303399169698583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838098700868932779799055 1257148051303399169698583)
            ·
              refine ⟨1885722076955098754547875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257148051303399169698583 1885722076955098754547875)
              ·
                refine ⟨2828583115432648131821813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885722076955098754547875 2828583115432648131821813)
                ·
                  refine ⟨265179667071810762358295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2828583115432648131821813 265179667071810762358295)
                  ·
                    rfl

theorem cell20_580990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_580990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_580990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_580990 prefixEnd_580990 := by exact prefixLift 580990
  have htrace : WordTrace (prefixWord ++ tailWord_580990) baseStart_580990 baseEnd_580990 := by
    simpa [prefixWord, tailWord_580990, baseEnd_580990] using wordTrace_append hprefix tailTrace_580990
  have hstable : (prefixWord ++ tailWord_580990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580990).length < 2 ^ (prefixWord ++ tailWord_580990).sum := by decide
  have hdescent : baseEnd_580990 < baseStart_580990 := by decide
  rcases family_descends (prefixWord ++ tailWord_580990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581052 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 2]
def baseStart_581052 : Nat := 118140960795 + 581052 * 2 ^ 59
def prefixEnd_581052 : Nat := 4983230072969 + 3 ^ 40 * 581052 * 2
def baseEnd_581052 : Nat := 265207965561214102291375

theorem tailTrace_581052 : CollatzResearch.WordTrace tailWord_581052 prefixEnd_581052 265207965561214102291375 := by
  unfold tailWord_581052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596353745477657313072705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14128471660636876417430273 10596353745477657313072705)
  ·
    refine ⟨7947265309108242984804529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10596353745477657313072705 7947265309108242984804529)
    ·
      refine ⟨5960448981831182238603397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7947265309108242984804529 5960448981831182238603397)
      ·
        refine ⟨1117584184093346669738137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5960448981831182238603397 1117584184093346669738137)
        ·
          refine ⟨838188138070010002303603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117584184093346669738137 838188138070010002303603)
          ·
            refine ⟨1257282207105015003455405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838188138070010002303603 1257282207105015003455405)
            ·
              refine ⟨471480827664380626295777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1257282207105015003455405 471480827664380626295777)
              ·
                refine ⟨353610620748285469721833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471480827664380626295777 353610620748285469721833)
                ·
                  refine ⟨265207965561214102291375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353610620748285469721833 265207965561214102291375)
                  ·
                    rfl

theorem cell20_581052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_581052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581052 prefixEnd_581052 := by exact prefixLift 581052
  have htrace : WordTrace (prefixWord ++ tailWord_581052) baseStart_581052 baseEnd_581052 := by
    simpa [prefixWord, tailWord_581052, baseEnd_581052] using wordTrace_append hprefix tailTrace_581052
  have hstable : (prefixWord ++ tailWord_581052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581052).length < 2 ^ (prefixWord ++ tailWord_581052).sum := by decide
  have hdescent : baseEnd_581052 < baseStart_581052 := by decide
  rcases family_descends (prefixWord ++ tailWord_581052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581053 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_581053 : Nat := 118140960795 + 581053 * 2 ^ 59
def prefixEnd_581053 : Nat := 4983230072969 + 3 ^ 40 * 581053 * 2
def baseEnd_581053 : Nat := 265208421988462543258037

theorem tailTrace_581053 : CollatzResearch.WordTrace tailWord_581053 prefixEnd_581053 265208421988462543258037 := by
  unfold tailWord_581053
  simp only [CollatzResearch.WordTrace]
  refine ⟨21192743963951691796931813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14128495975967794531287875 21192743963951691796931813)
  ·
    refine ⟨3973639493240942211924715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21192743963951691796931813 3973639493240942211924715)
    ·
      refine ⟨5960459239861413317887073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973639493240942211924715 5960459239861413317887073)
      ·
        refine ⟨4470344429896059988415305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5960459239861413317887073 4470344429896059988415305)
        ·
          refine ⟨3352758322422044991311479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4470344429896059988415305 3352758322422044991311479)
          ·
            refine ⟨5029137483633067486967219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352758322422044991311479 5029137483633067486967219)
            ·
              refine ⟨7543706225449601230450829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5029137483633067486967219 7543706225449601230450829)
              ·
                refine ⟨2828889834543600461419061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7543706225449601230450829 2828889834543600461419061)
                ·
                  refine ⟨265208421988462543258037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2828889834543600461419061 265208421988462543258037)
                  ·
                    rfl

theorem cell20_581053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_581053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581053 prefixEnd_581053 := by exact prefixLift 581053
  have htrace : WordTrace (prefixWord ++ tailWord_581053) baseStart_581053 baseEnd_581053 := by
    simpa [prefixWord, tailWord_581053, baseEnd_581053] using wordTrace_append hprefix tailTrace_581053
  have hstable : (prefixWord ++ tailWord_581053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581053).length < 2 ^ (prefixWord ++ tailWord_581053).sum := by decide
  have hdescent : baseEnd_581053 < baseStart_581053 := by decide
  rcases family_descends (prefixWord ++ tailWord_581053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581058 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_581058 : Nat := 118140960795 + 581058 * 2 ^ 59
def prefixEnd_581058 : Nat := 4983230072969 + 3 ^ 40 * 581058 * 2
def baseEnd_581058 : Nat := 265210704124704748091351

theorem tailTrace_581058 : CollatzResearch.WordTrace tailWord_581058 prefixEnd_581058 265210704124704748091351 := by
  unfold tailWord_581058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298231582233394412715957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14128617552622385100575885 5298231582233394412715957)
  ·
    refine ⟨496709210834380726192121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5298231582233394412715957 496709210834380726192121)
    ·
      refine ⟨372531908125785544644091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 496709210834380726192121 372531908125785544644091)
      ·
        refine ⟨558797862188678316966137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372531908125785544644091 558797862188678316966137)
        ·
          refine ⟨419098396641508737724603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558797862188678316966137 419098396641508737724603)
          ·
            refine ⟨628647594962263106586905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419098396641508737724603 628647594962263106586905)
            ·
              refine ⟨471485696221697329940179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628647594962263106586905 471485696221697329940179)
              ·
                refine ⟨707228544332545994910269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471485696221697329940179 707228544332545994910269)
                ·
                  refine ⟨265210704124704748091351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707228544332545994910269 265210704124704748091351)
                  ·
                    rfl

theorem cell20_581058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_581058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581058 prefixEnd_581058 := by exact prefixLift 581058
  have htrace : WordTrace (prefixWord ++ tailWord_581058) baseStart_581058 baseEnd_581058 := by
    simpa [prefixWord, tailWord_581058, baseEnd_581058] using wordTrace_append hprefix tailTrace_581058
  have hstable : (prefixWord ++ tailWord_581058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581058).length < 2 ^ (prefixWord ++ tailWord_581058).sum := by decide
  have hdescent : baseEnd_581058 < baseStart_581058 := by decide
  rcases family_descends (prefixWord ++ tailWord_581058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581067 : List Nat := [1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_581067 : Nat := 118140960795 + 581067 * 2 ^ 59
def prefixEnd_581067 : Nat := 4983230072969 + 3 ^ 40 * 581067 * 2
def baseEnd_581067 : Nat := 88404937323313572263771

theorem tailTrace_581067 : CollatzResearch.WordTrace tailWord_581067 prefixEnd_581067 88404937323313572263771 := by
  unfold tailWord_581067
  simp only [CollatzResearch.WordTrace]
  refine ⟨21193254585900972187941455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14128836390600648125294303 21193254585900972187941455)
  ·
    refine ⟨31789881878851458281912183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21193254585900972187941455 31789881878851458281912183)
    ·
      refine ⟨47684822818277187422868275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31789881878851458281912183 47684822818277187422868275)
      ·
        refine ⟨71527234227415781134302413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47684822818277187422868275 71527234227415781134302413)
        ·
          refine ⟨26822712835280917925363405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71527234227415781134302413 26822712835280917925363405)
          ·
            refine ⟨10058517313230344222011277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26822712835280917925363405 10058517313230344222011277)
            ·
              refine ⟨3771943992461379083254229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10058517313230344222011277 3771943992461379083254229)
              ·
                refine ⟨88404937323313572263771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3771943992461379083254229 88404937323313572263771)
                ·
                  rfl

theorem cell20_581067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_581067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581067 prefixEnd_581067 := by exact prefixLift 581067
  have htrace : WordTrace (prefixWord ++ tailWord_581067) baseStart_581067 baseEnd_581067 := by
    simpa [prefixWord, tailWord_581067, baseEnd_581067] using wordTrace_append hprefix tailTrace_581067
  have hstable : (prefixWord ++ tailWord_581067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581067).length < 2 ^ (prefixWord ++ tailWord_581067).sum := by decide
  have hdescent : baseEnd_581067 < baseStart_581067 := by decide
  rcases family_descends (prefixWord ++ tailWord_581067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581101 : List Nat := [1, 5, 1, 3, 3, 7]
def baseStart_581101 : Nat := 118140960795 + 581101 * 2 ^ 59
def prefixEnd_581101 : Nat := 4983230072969 + 3 ^ 40 * 581101 * 2
def baseEnd_581101 : Nat := 9823345573940285542883

theorem tailTrace_581101 : CollatzResearch.WordTrace tailWord_581101 prefixEnd_581101 9823345573940285542883 := by
  unfold tailWord_581101
  simp only [CollatzResearch.WordTrace]
  refine ⟨21194494667777795994679157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14129663111851863996452771 21194494667777795994679157)
  ·
    refine ⟨1986983875104168374501171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21194494667777795994679157 1986983875104168374501171)
    ·
      refine ⟨2980475812656252561751757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1986983875104168374501171 2980475812656252561751757)
      ·
        refine ⟨1117678429746094710656909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2980475812656252561751757 1117678429746094710656909)
        ·
          refine ⟨419129411154785516496341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1117678429746094710656909 419129411154785516496341)
          ·
            refine ⟨9823345573940285542883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 419129411154785516496341 9823345573940285542883)
            ·
              rfl

theorem cell20_581101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 7].length) (baseStart_581101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581101 prefixEnd_581101 := by exact prefixLift 581101
  have htrace : WordTrace (prefixWord ++ tailWord_581101) baseStart_581101 baseEnd_581101 := by
    simpa [prefixWord, tailWord_581101, baseEnd_581101] using wordTrace_append hprefix tailTrace_581101
  have hstable : (prefixWord ++ tailWord_581101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581101).length < 2 ^ (prefixWord ++ tailWord_581101).sum := by decide
  have hdescent : baseEnd_581101 < baseStart_581101 := by decide
  rcases family_descends (prefixWord ++ tailWord_581101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581105 : List Nat := [1, 2, 2, 2, 3, 10]
def baseStart_581105 : Nat := 118140960795 + 581105 * 2 ^ 59
def prefixEnd_581105 : Nat := 4983230072969 + 3 ^ 40 * 581105 * 2
def baseEnd_581105 : Nat := 9823413192791906426833

theorem tailTrace_581105 : CollatzResearch.WordTrace tailWord_581105 prefixEnd_581105 9823413192791906426833 := by
  unfold tailWord_581105
  simp only [CollatzResearch.WordTrace]
  refine ⟨21194640559763304677824769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14129760373175536451883179 21194640559763304677824769)
  ·
    refine ⟨15895980419822478508368577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21194640559763304677824769 15895980419822478508368577)
    ·
      refine ⟨11921985314866858881276433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15895980419822478508368577 11921985314866858881276433)
      ·
        refine ⟨8941488986150144160957325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11921985314866858881276433 8941488986150144160957325)
        ·
          refine ⟨3353058369806304060358997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8941488986150144160957325 3353058369806304060358997)
          ·
            refine ⟨9823413192791906426833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3353058369806304060358997 9823413192791906426833)
            ·
              rfl

theorem cell20_581105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 10].length) (baseStart_581105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581105 prefixEnd_581105 := by exact prefixLift 581105
  have htrace : WordTrace (prefixWord ++ tailWord_581105) baseStart_581105 baseEnd_581105 := by
    simpa [prefixWord, tailWord_581105, baseEnd_581105] using wordTrace_append hprefix tailTrace_581105
  have hstable : (prefixWord ++ tailWord_581105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581105).length < 2 ^ (prefixWord ++ tailWord_581105).sum := by decide
  have hdescent : baseEnd_581105 < baseStart_581105 := by decide
  rcases family_descends (prefixWord ++ tailWord_581105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581115 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 2]
def baseStart_581115 : Nat := 118140960795 + 581115 * 2 ^ 59
def prefixEnd_581115 : Nat := 4983230072969 + 3 ^ 40 * 581115 * 2
def baseEnd_581115 : Nat := 265236720477865883191117

theorem tailTrace_581115 : CollatzResearch.WordTrace tailWord_581115 prefixEnd_581115 265236720477865883191117 := by
  unfold tailWord_581115
  simp only [CollatzResearch.WordTrace]
  refine ⟨21195005289727076385688799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14130003526484717590459199 21195005289727076385688799)
  ·
    refine ⟨31792507934590614578533199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21195005289727076385688799 31792507934590614578533199)
    ·
      refine ⟨47688761901885921867799799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31792507934590614578533199 47688761901885921867799799)
      ·
        refine ⟨71533142852828882801699699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47688761901885921867799799 71533142852828882801699699)
        ·
          refine ⟨107299714279243324202549549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71533142852828882801699699 107299714279243324202549549)
          ·
            refine ⟨40237392854716246575956081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107299714279243324202549549 40237392854716246575956081)
            ·
              refine ⟨30178044641037184931967061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40237392854716246575956081 30178044641037184931967061)
              ·
                refine ⟨353648960637154510921489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30178044641037184931967061 353648960637154510921489)
                ·
                  refine ⟨265236720477865883191117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353648960637154510921489 265236720477865883191117)
                  ·
                    rfl

theorem cell20_581115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 2].length) (baseStart_581115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581115 prefixEnd_581115 := by exact prefixLift 581115
  have htrace : WordTrace (prefixWord ++ tailWord_581115) baseStart_581115 baseEnd_581115 := by
    simpa [prefixWord, tailWord_581115, baseEnd_581115] using wordTrace_append hprefix tailTrace_581115
  have hstable : (prefixWord ++ tailWord_581115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581115).length < 2 ^ (prefixWord ++ tailWord_581115).sum := by decide
  have hdescent : baseEnd_581115 < baseStart_581115 := by decide
  rcases family_descends (prefixWord ++ tailWord_581115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581129 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_581129 : Nat := 118140960795 + 581129 * 2 ^ 59
def prefixEnd_581129 : Nat := 4983230072969 + 3 ^ 40 * 581129 * 2
def baseEnd_581129 : Nat := 265243110459344056724393

theorem tailTrace_581129 : CollatzResearch.WordTrace tailWord_581129 prefixEnd_581129 265243110459344056724393 := by
  unfold tailWord_581129
  simp only [CollatzResearch.WordTrace]
  refine ⟨21195515911676356776698441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14130343941117571184465627 21195515911676356776698441)
  ·
    refine ⟨15896636933757267582523831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21195515911676356776698441 15896636933757267582523831)
    ·
      refine ⟨23844955400635901373785747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15896636933757267582523831 23844955400635901373785747)
      ·
        refine ⟨35767433100953852060678621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23844955400635901373785747 35767433100953852060678621)
        ·
          refine ⟨13412787412857694522754483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35767433100953852060678621 13412787412857694522754483)
          ·
            refine ⟨20119181119286541784131725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13412787412857694522754483 20119181119286541784131725)
            ·
              refine ⟨7544692919732453169049397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20119181119286541784131725 7544692919732453169049397)
              ·
                refine ⟨707314961224917484598381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7544692919732453169049397 707314961224917484598381)
                ·
                  refine ⟨265243110459344056724393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707314961224917484598381 265243110459344056724393)
                  ·
                    rfl

theorem cell20_581129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_581129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581129 prefixEnd_581129 := by exact prefixLift 581129
  have htrace : WordTrace (prefixWord ++ tailWord_581129) baseStart_581129 baseEnd_581129 := by
    simpa [prefixWord, tailWord_581129, baseEnd_581129] using wordTrace_append hprefix tailTrace_581129
  have hstable : (prefixWord ++ tailWord_581129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581129).length < 2 ^ (prefixWord ++ tailWord_581129).sum := by decide
  have hdescent : baseEnd_581129 < baseStart_581129 := by decide
  rcases family_descends (prefixWord ++ tailWord_581129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581190 : List Nat := [6, 1, 1, 1, 4, 1, 2, 4]
def baseStart_581190 : Nat := 118140960795 + 581190 * 2 ^ 59
def prefixEnd_581190 : Nat := 4983230072969 + 3 ^ 40 * 581190 * 2
def baseEnd_581190 : Nat := 88423650840499651896937

theorem tailTrace_581190 : CollatzResearch.WordTrace tailWord_581190 prefixEnd_581190 88423650840499651896937 := by
  unfold tailWord_581190
  simp only [CollatzResearch.WordTrace]
  refine ⟨662429398889230131083407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14131827176303576129779349 662429398889230131083407)
  ·
    refine ⟨993644098333845196625111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662429398889230131083407 993644098333845196625111)
    ·
      refine ⟨1490466147500767794937667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993644098333845196625111 1490466147500767794937667)
      ·
        refine ⟨2235699221251151692406501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490466147500767794937667 2235699221251151692406501)
        ·
          refine ⟨419193603984590942326219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2235699221251151692406501 419193603984590942326219)
          ·
            refine ⟨628790405976886413489329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419193603984590942326219 628790405976886413489329)
            ·
              refine ⟨471592804482664810116997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628790405976886413489329 471592804482664810116997)
              ·
                refine ⟨88423650840499651896937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 471592804482664810116997 88423650840499651896937)
                ·
                  rfl

theorem cell20_581190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_581190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581190 prefixEnd_581190 := by exact prefixLift 581190
  have htrace : WordTrace (prefixWord ++ tailWord_581190) baseStart_581190 baseEnd_581190 := by
    simpa [prefixWord, tailWord_581190, baseEnd_581190] using wordTrace_append hprefix tailTrace_581190
  have hstable : (prefixWord ++ tailWord_581190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581190).length < 2 ^ (prefixWord ++ tailWord_581190).sum := by decide
  have hdescent : baseEnd_581190 < baseStart_581190 := by decide
  rcases family_descends (prefixWord ++ tailWord_581190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581219 : List Nat := [1, 1, 1, 5, 1, 3, 8]
def baseStart_581219 : Nat := 118140960795 + 581219 * 2 ^ 59
def prefixEnd_581219 : Nat := 4983230072969 + 3 ^ 40 * 581219 * 2
def baseEnd_581219 : Nat := 29476020990189304858225

theorem tailTrace_581219 : CollatzResearch.WordTrace tailWord_581219 prefixEnd_581219 29476020990189304858225 := by
  unfold tailWord_581219
  simp only [CollatzResearch.WordTrace]
  refine ⟨21198798481350302147474711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14132532320900201431649807 21198798481350302147474711)
  ·
    refine ⟨31798197722025453221212067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21198798481350302147474711 31798197722025453221212067)
    ·
      refine ⟨47697296583038179831818101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31798197722025453221212067 47697296583038179831818101)
      ·
        refine ⟨4471621554659829359232947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47697296583038179831818101 4471621554659829359232947)
        ·
          refine ⟨6707432331989744038849421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471621554659829359232947 6707432331989744038849421)
          ·
            refine ⟨2515287124496154014568533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6707432331989744038849421 2515287124496154014568533)
            ·
              refine ⟨29476020990189304858225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2515287124496154014568533 29476020990189304858225)
              ·
                rfl

theorem cell20_581219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_581219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581219 prefixEnd_581219 := by exact prefixLift 581219
  have htrace : WordTrace (prefixWord ++ tailWord_581219) baseStart_581219 baseEnd_581219 := by
    simpa [prefixWord, tailWord_581219, baseEnd_581219] using wordTrace_append hprefix tailTrace_581219
  have hstable : (prefixWord ++ tailWord_581219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581219).length < 2 ^ (prefixWord ++ tailWord_581219).sum := by decide
  have hdescent : baseEnd_581219 < baseStart_581219 := by decide
  rcases family_descends (prefixWord ++ tailWord_581219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581243 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_581243 : Nat := 118140960795 + 581243 * 2 ^ 59
def prefixEnd_581243 : Nat := 4983230072969 + 3 ^ 40 * 581243 * 2
def baseEnd_581243 : Nat := 265295143165666326923927

theorem tailTrace_581243 : CollatzResearch.WordTrace tailWord_581243 prefixEnd_581243 265295143165666326923927 := by
  unfold tailWord_581243
  simp only [CollatzResearch.WordTrace]
  refine ⟨21199673833263354246348383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14133115888842236164232255 21199673833263354246348383)
  ·
    refine ⟨31799510749895031369522575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21199673833263354246348383 31799510749895031369522575)
    ·
      refine ⟨47699266124842547054283863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31799510749895031369522575 47699266124842547054283863)
      ·
        refine ⟨71548899187263820581425795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47699266124842547054283863 71548899187263820581425795)
        ·
          refine ⟨107323348780895730872138693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71548899187263820581425795 107323348780895730872138693)
          ·
            refine ⟨20123127896417949538526005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107323348780895730872138693 20123127896417949538526005)
            ·
              refine ⟨1886543240289182769236813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20123127896417949538526005 1886543240289182769236813)
              ·
                refine ⟨707453715108443538463805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886543240289182769236813 707453715108443538463805)
                ·
                  refine ⟨265295143165666326923927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707453715108443538463805 265295143165666326923927)
                  ·
                    rfl

theorem cell20_581243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_581243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581243 prefixEnd_581243 := by exact prefixLift 581243
  have htrace : WordTrace (prefixWord ++ tailWord_581243) baseStart_581243 baseEnd_581243 := by
    simpa [prefixWord, tailWord_581243, baseEnd_581243] using wordTrace_append hprefix tailTrace_581243
  have hstable : (prefixWord ++ tailWord_581243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581243).length < 2 ^ (prefixWord ++ tailWord_581243).sum := by decide
  have hdescent : baseEnd_581243 < baseStart_581243 := by decide
  rcases family_descends (prefixWord ++ tailWord_581243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581257 : List Nat := [1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_581257 : Nat := 118140960795 + 581257 * 2 ^ 59
def prefixEnd_581257 : Nat := 4983230072969 + 3 ^ 40 * 581257 * 2
def baseEnd_581257 : Nat := 88433844382381500152401

theorem tailTrace_581257 : CollatzResearch.WordTrace tailWord_581257 prefixEnd_581257 88433844382381500152401 := by
  unfold tailWord_581257
  simp only [CollatzResearch.WordTrace]
  refine ⟨21200184455212634637358025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14133456303475089758238683 21200184455212634637358025)
  ·
    refine ⟨15900138341409475978018519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21200184455212634637358025 15900138341409475978018519)
    ·
      refine ⟨23850207512114213967027779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15900138341409475978018519 23850207512114213967027779)
      ·
        refine ⟨35775311268171320950541669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23850207512114213967027779 35775311268171320950541669)
        ·
          refine ⟨6707870862782122678226563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35775311268171320950541669 6707870862782122678226563)
          ·
            refine ⟨10061806294173184017339845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6707870862782122678226563 10061806294173184017339845)
            ·
              refine ⟨1886588680157472003251221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10061806294173184017339845 1886588680157472003251221)
              ·
                refine ⟨88433844382381500152401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1886588680157472003251221 88433844382381500152401)
                ·
                  rfl

theorem cell20_581257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_581257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581257 prefixEnd_581257 := by exact prefixLift 581257
  have htrace : WordTrace (prefixWord ++ tailWord_581257) baseStart_581257 baseEnd_581257 := by
    simpa [prefixWord, tailWord_581257, baseEnd_581257] using wordTrace_append hprefix tailTrace_581257
  have hstable : (prefixWord ++ tailWord_581257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581257).length < 2 ^ (prefixWord ++ tailWord_581257).sum := by decide
  have hdescent : baseEnd_581257 < baseStart_581257 := by decide
  rcases family_descends (prefixWord ++ tailWord_581257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581264 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_581264 : Nat := 118140960795 + 581264 * 2 ^ 59
def prefixEnd_581264 : Nat := 4983230072969 + 3 ^ 40 * 581264 * 2
def baseEnd_581264 : Nat := 265304728137883587223841

theorem tailTrace_581264 : CollatzResearch.WordTrace tailWord_581264 prefixEnd_581264 265304728137883587223841 := by
  unfold tailWord_581264
  simp only [CollatzResearch.WordTrace]
  refine ⟨10600219883093637416431423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14133626510791516555241897 10600219883093637416431423)
  ·
    refine ⟨15900329824640456124647135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10600219883093637416431423 15900329824640456124647135)
    ·
      refine ⟨23850494736960684186970703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15900329824640456124647135 23850494736960684186970703)
      ·
        refine ⟨35775742105441026280456055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23850494736960684186970703 35775742105441026280456055)
        ·
          refine ⟨53663613158161539420684083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35775742105441026280456055 53663613158161539420684083)
          ·
            refine ⟨80495419737242309131026125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53663613158161539420684083 80495419737242309131026125)
            ·
              refine ⟨30185782401465865924134797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80495419737242309131026125 30185782401465865924134797)
              ·
                refine ⟨11319668400549699721550549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30185782401465865924134797 11319668400549699721550549)
                ·
                  refine ⟨265304728137883587223841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11319668400549699721550549 265304728137883587223841)
                  ·
                    rfl

theorem cell20_581264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_581264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581264 prefixEnd_581264 := by exact prefixLift 581264
  have htrace : WordTrace (prefixWord ++ tailWord_581264) baseStart_581264 baseEnd_581264 := by
    simpa [prefixWord, tailWord_581264, baseEnd_581264] using wordTrace_append hprefix tailTrace_581264
  have hstable : (prefixWord ++ tailWord_581264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581264).length < 2 ^ (prefixWord ++ tailWord_581264).sum := by decide
  have hdescent : baseEnd_581264 < baseStart_581264 := by decide
  rcases family_descends (prefixWord ++ tailWord_581264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581284 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 2]
def baseStart_581284 : Nat := 118140960795 + 581284 * 2 ^ 59
def prefixEnd_581284 : Nat := 4983230072969 + 3 ^ 40 * 581284 * 2
def baseEnd_581284 : Nat := 265313856682852406557093

theorem tailTrace_581284 : CollatzResearch.WordTrace tailWord_581284 prefixEnd_581284 265313856682852406557093 := by
  unfold tailWord_581284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10600584613057409124295453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14134112817409878832393937 10600584613057409124295453)
  ·
    refine ⟨3975219229896528421610795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10600584613057409124295453 3975219229896528421610795)
    ·
      refine ⟨5962828844844792632416193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975219229896528421610795 5962828844844792632416193)
      ·
        refine ⟨4472121633633594474312145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5962828844844792632416193 4472121633633594474312145)
        ·
          refine ⟨3354091225225195855734109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4472121633633594474312145 3354091225225195855734109)
          ·
            refine ⟨1257784209459448445900291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3354091225225195855734109 1257784209459448445900291)
            ·
              refine ⟨1886676314189172668850437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257784209459448445900291 1886676314189172668850437)
              ·
                refine ⟨353751808910469875409457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1886676314189172668850437 353751808910469875409457)
                ·
                  refine ⟨265313856682852406557093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353751808910469875409457 265313856682852406557093)
                  ·
                    rfl

theorem cell20_581284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_581284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581284 prefixEnd_581284 := by exact prefixLift 581284
  have htrace : WordTrace (prefixWord ++ tailWord_581284) baseStart_581284 baseEnd_581284 := by
    simpa [prefixWord, tailWord_581284, baseEnd_581284] using wordTrace_append hprefix tailTrace_581284
  have hstable : (prefixWord ++ tailWord_581284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581284).length < 2 ^ (prefixWord ++ tailWord_581284).sum := by decide
  have hdescent : baseEnd_581284 < baseStart_581284 := by decide
  rcases family_descends (prefixWord ++ tailWord_581284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581312 : List Nat := [2, 1, 1, 2, 4, 1, 5, 4]
def baseStart_581312 : Nat := 118140960795 + 581312 * 2 ^ 59
def prefixEnd_581312 : Nat := 4983230072969 + 3 ^ 40 * 581312 * 2
def baseEnd_581312 : Nat := 88442212215269584541215

theorem tailTrace_581312 : CollatzResearch.WordTrace tailWord_581312 prefixEnd_581312 88442212215269584541215 := by
  unfold tailWord_581312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10601095235006689515305095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14134793646675586020406793 10601095235006689515305095)
  ·
    refine ⟨15901642852510034272957643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10601095235006689515305095 15901642852510034272957643)
    ·
      refine ⟨23852464278765051409436465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15901642852510034272957643 23852464278765051409436465)
      ·
        refine ⟨17889348209073788557077349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23852464278765051409436465 17889348209073788557077349)
        ·
          refine ⟨3354252789201335354452003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17889348209073788557077349 3354252789201335354452003)
          ·
            refine ⟨5031379183802003031678005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354252789201335354452003 5031379183802003031678005)
            ·
              refine ⟨471691798481437784219813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5031379183802003031678005 471691798481437784219813)
              ·
                refine ⟨88442212215269584541215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 471691798481437784219813 88442212215269584541215)
                ·
                  rfl

theorem cell20_581312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_581312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581312 prefixEnd_581312 := by exact prefixLift 581312
  have htrace : WordTrace (prefixWord ++ tailWord_581312) baseStart_581312 baseEnd_581312 := by
    simpa [prefixWord, tailWord_581312, baseEnd_581312] using wordTrace_append hprefix tailTrace_581312
  have hstable : (prefixWord ++ tailWord_581312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581312).length < 2 ^ (prefixWord ++ tailWord_581312).sum := by decide
  have hdescent : baseEnd_581312 < baseStart_581312 := by decide
  rcases family_descends (prefixWord ++ tailWord_581312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581318 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_581318 : Nat := 118140960795 + 581318 * 2 ^ 59
def prefixEnd_581318 : Nat := 4983230072969 + 3 ^ 40 * 581318 * 2
def baseEnd_581318 : Nat := 265329375209299399423621

theorem tailTrace_581318 : CollatzResearch.WordTrace tailWord_581318 prefixEnd_581318 265329375209299399423621 := by
  unfold tailWord_581318
  simp only [CollatzResearch.WordTrace]
  refine ⟨662575290874738814229019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14134939538661094703552405 662575290874738814229019)
  ·
    refine ⟨993862936312108221343529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662575290874738814229019 993862936312108221343529)
    ·
      refine ⟨745397202234081166007647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 993862936312108221343529 745397202234081166007647)
      ·
        refine ⟨1118095803351121749011471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745397202234081166007647 1118095803351121749011471)
        ·
          refine ⟨1677143705026682623517207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118095803351121749011471 1677143705026682623517207)
          ·
            refine ⟨2515715557540023935275811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677143705026682623517207 2515715557540023935275811)
            ·
              refine ⟨3773573336310035902913717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515715557540023935275811 3773573336310035902913717)
              ·
                refine ⟨353772500279065865898161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3773573336310035902913717 353772500279065865898161)
                ·
                  refine ⟨265329375209299399423621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353772500279065865898161 265329375209299399423621)
                  ·
                    rfl

theorem cell20_581318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_581318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581318 prefixEnd_581318 := by exact prefixLift 581318
  have htrace : WordTrace (prefixWord ++ tailWord_581318) baseStart_581318 baseEnd_581318 := by
    simpa [prefixWord, tailWord_581318, baseEnd_581318] using wordTrace_append hprefix tailTrace_581318
  have hstable : (prefixWord ++ tailWord_581318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581318).length < 2 ^ (prefixWord ++ tailWord_581318).sum := by decide
  have hdescent : baseEnd_581318 < baseStart_581318 := by decide
  rcases family_descends (prefixWord ++ tailWord_581318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581326 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_581326 : Nat := 118140960795 + 581326 * 2 ^ 59
def prefixEnd_581326 : Nat := 4983230072969 + 3 ^ 40 * 581326 * 2
def baseEnd_581326 : Nat := 265333026627286927156921

theorem tailTrace_581326 : CollatzResearch.WordTrace tailWord_581326 prefixEnd_581326 265333026627286927156921 := by
  unfold tailWord_581326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650337636495332427702479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14135134061308439614413221 2650337636495332427702479)
  ·
    refine ⟨3975506454742998641553719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650337636495332427702479 3975506454742998641553719)
    ·
      refine ⟨5963259682114497962330579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975506454742998641553719 5963259682114497962330579)
      ·
        refine ⟨8944889523171746943495869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5963259682114497962330579 8944889523171746943495869)
        ·
          refine ⟨3354333571189405103810951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8944889523171746943495869 3354333571189405103810951)
          ·
            refine ⟨5031500356784107655716427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354333571189405103810951 5031500356784107655716427)
            ·
              refine ⟨7547250535176161483574641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031500356784107655716427 7547250535176161483574641)
              ·
                refine ⟨5660437901382121112680981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7547250535176161483574641 5660437901382121112680981)
                ·
                  refine ⟨265333026627286927156921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5660437901382121112680981 265333026627286927156921)
                  ·
                    rfl

theorem cell20_581326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_581326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581326 prefixEnd_581326 := by exact prefixLift 581326
  have htrace : WordTrace (prefixWord ++ tailWord_581326) baseStart_581326 baseEnd_581326 := by
    simpa [prefixWord, tailWord_581326, baseEnd_581326] using wordTrace_append hprefix tailTrace_581326
  have hstable : (prefixWord ++ tailWord_581326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581326).length < 2 ^ (prefixWord ++ tailWord_581326).sum := by decide
  have hdescent : baseEnd_581326 < baseStart_581326 := by decide
  rcases family_descends (prefixWord ++ tailWord_581326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581343 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 2]
def baseStart_581343 : Nat := 118140960795 + 581343 * 2 ^ 59
def prefixEnd_581343 : Nat := 4983230072969 + 3 ^ 40 * 581343 * 2
def baseEnd_581343 : Nat := 265340785890510423590185

theorem tailTrace_581343 : CollatzResearch.WordTrace tailWord_581343 prefixEnd_581343 265340785890510423590185 := by
  unfold tailWord_581343
  simp only [CollatzResearch.WordTrace]
  refine ⟨21203321132901071324988683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14135547421934047549992455 21203321132901071324988683)
  ·
    refine ⟨31804981699351606987483025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21203321132901071324988683 31804981699351606987483025)
    ·
      refine ⟨23853736274513705240612269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31804981699351606987483025 23853736274513705240612269)
      ·
        refine ⟨8945151102942639465229601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23853736274513705240612269 8945151102942639465229601)
        ·
          refine ⟨6708863327206979598922201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8945151102942639465229601 6708863327206979598922201)
          ·
            refine ⟨5031647495405234699191651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6708863327206979598922201 5031647495405234699191651)
            ·
              refine ⟨7547471243107852048787477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031647495405234699191651 7547471243107852048787477)
              ·
                refine ⟨353787714520680564786913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7547471243107852048787477 353787714520680564786913)
                ·
                  refine ⟨265340785890510423590185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353787714520680564786913 265340785890510423590185)
                  ·
                    rfl

theorem cell20_581343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 2].length) (baseStart_581343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581343 prefixEnd_581343 := by exact prefixLift 581343
  have htrace : WordTrace (prefixWord ++ tailWord_581343) baseStart_581343 baseEnd_581343 := by
    simpa [prefixWord, tailWord_581343, baseEnd_581343] using wordTrace_append hprefix tailTrace_581343
  have hstable : (prefixWord ++ tailWord_581343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581343).length < 2 ^ (prefixWord ++ tailWord_581343).sum := by decide
  have hdescent : baseEnd_581343 < baseStart_581343 := by decide
  rcases family_descends (prefixWord ++ tailWord_581343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581394 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_581394 : Nat := 118140960795 + 581394 * 2 ^ 59
def prefixEnd_581394 : Nat := 4983230072969 + 3 ^ 40 * 581394 * 2
def baseEnd_581394 : Nat := 265364063680180912889977

theorem tailTrace_581394 : CollatzResearch.WordTrace tailWord_581394 prefixEnd_581394 265364063680180912889977 := by
  unfold tailWord_581394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5301295313929076758773809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14136787503810871356730157 5301295313929076758773809)
  ·
    refine ⟨3975971485446807569080357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5301295313929076758773809 3975971485446807569080357)
    ·
      refine ⟨745494653521276419202567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3975971485446807569080357 745494653521276419202567)
      ·
        refine ⟨1118241980281914628803851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745494653521276419202567 1118241980281914628803851)
        ·
          refine ⟨1677362970422871943205777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118241980281914628803851 1677362970422871943205777)
          ·
            refine ⟨1258022227817153957404333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677362970422871943205777 1258022227817153957404333)
            ·
              refine ⟨471758335431432734026625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1258022227817153957404333 471758335431432734026625)
              ·
                refine ⟨353818751573574550519969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471758335431432734026625 353818751573574550519969)
                ·
                  refine ⟨265364063680180912889977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353818751573574550519969 265364063680180912889977)
                  ·
                    rfl

theorem cell20_581394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_581394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581394 prefixEnd_581394 := by exact prefixLift 581394
  have htrace : WordTrace (prefixWord ++ tailWord_581394) baseStart_581394 baseEnd_581394 := by
    simpa [prefixWord, tailWord_581394, baseEnd_581394] using wordTrace_append hprefix tailTrace_581394
  have hstable : (prefixWord ++ tailWord_581394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581394).length < 2 ^ (prefixWord ++ tailWord_581394).sum := by decide
  have hdescent : baseEnd_581394 < baseStart_581394 := by decide
  rcases family_descends (prefixWord ++ tailWord_581394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581409 : List Nat := [1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_581409 : Nat := 118140960795 + 581409 * 2 ^ 59
def prefixEnd_581409 : Nat := 4983230072969 + 3 ^ 40 * 581409 * 2
def baseEnd_581409 : Nat := 88456970029635842463305

theorem tailTrace_581409 : CollatzResearch.WordTrace tailWord_581409 prefixEnd_581409 88456970029635842463305 := by
  unfold tailWord_581409
  simp only [CollatzResearch.WordTrace]
  refine ⟨21205728350661964596891281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14137152233774643064594187 21205728350661964596891281)
  ·
    refine ⟨15904296262996473447668461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21205728350661964596891281 15904296262996473447668461)
    ·
      refine ⟨5964111098623677542875673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15904296262996473447668461 5964111098623677542875673)
      ·
        refine ⟨4473083323967758157156755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5964111098623677542875673 4473083323967758157156755)
        ·
          refine ⟨6709624985951637235735133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4473083323967758157156755 6709624985951637235735133)
          ·
            refine ⟨2516109369731863963400675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6709624985951637235735133 2516109369731863963400675)
            ·
              refine ⟨3774164054597795945101013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516109369731863963400675 3774164054597795945101013)
              ·
                refine ⟨88456970029635842463305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3774164054597795945101013 88456970029635842463305)
                ·
                  rfl

theorem cell20_581409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_581409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581409 prefixEnd_581409 := by exact prefixLift 581409
  have htrace : WordTrace (prefixWord ++ tailWord_581409) baseStart_581409 baseEnd_581409 := by
    simpa [prefixWord, tailWord_581409, baseEnd_581409] using wordTrace_append hprefix tailTrace_581409
  have hstable : (prefixWord ++ tailWord_581409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581409).length < 2 ^ (prefixWord ++ tailWord_581409).sum := by decide
  have hdescent : baseEnd_581409 < baseStart_581409 := by decide
  rcases family_descends (prefixWord ++ tailWord_581409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581412 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_581412 : Nat := 118140960795 + 581412 * 2 ^ 59
def prefixEnd_581412 : Nat := 4983230072969 + 3 ^ 40 * 581412 * 2
def baseEnd_581412 : Nat := 265372279370652850289903

theorem tailTrace_581412 : CollatzResearch.WordTrace tailWord_581412 prefixEnd_581412 265372279370652850289903 := by
  unfold tailWord_581412
  simp only [CollatzResearch.WordTrace]
  refine ⟨10602918884825548054625245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14137225179767397406166993 10602918884825548054625245)
  ·
    refine ⟨3976094581809580520484467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10602918884825548054625245 3976094581809580520484467)
    ·
      refine ⟨5964141872714370780726701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3976094581809580520484467 5964141872714370780726701)
      ·
        refine ⟨2236553202267889042772513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5964141872714370780726701 2236553202267889042772513)
        ·
          refine ⟨1677414901700916782079385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2236553202267889042772513 1677414901700916782079385)
          ·
            refine ⟨1258061176275687586559539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677414901700916782079385 1258061176275687586559539)
            ·
              refine ⟨1887091764413531379839309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258061176275687586559539 1887091764413531379839309)
              ·
                refine ⟨707659411655074267439741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1887091764413531379839309 707659411655074267439741)
                ·
                  refine ⟨265372279370652850289903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707659411655074267439741 265372279370652850289903)
                  ·
                    rfl

theorem cell20_581412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_581412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581412 prefixEnd_581412 := by exact prefixLift 581412
  have htrace : WordTrace (prefixWord ++ tailWord_581412) baseStart_581412 baseEnd_581412 := by
    simpa [prefixWord, tailWord_581412, baseEnd_581412] using wordTrace_append hprefix tailTrace_581412
  have hstable : (prefixWord ++ tailWord_581412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581412).length < 2 ^ (prefixWord ++ tailWord_581412).sum := by decide
  have hdescent : baseEnd_581412 < baseStart_581412 := by decide
  rcases family_descends (prefixWord ++ tailWord_581412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581446 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_581446 : Nat := 118140960795 + 581446 * 2 ^ 59
def prefixEnd_581446 : Nat := 4983230072969 + 3 ^ 40 * 581446 * 2
def baseEnd_581446 : Nat := 265387797897099843156431

theorem tailTrace_581446 : CollatzResearch.WordTrace tailWord_581446 prefixEnd_581446 265387797897099843156431 := by
  unfold tailWord_581446
  simp only [CollatzResearch.WordTrace]
  refine ⟨662721182860247497374631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14138051901018613277325461 662721182860247497374631)
  ·
    refine ⟨994081774290371246061947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662721182860247497374631 994081774290371246061947)
    ·
      refine ⟨1491122661435556869092921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994081774290371246061947 1491122661435556869092921)
      ·
        refine ⟨1118341996076667651819691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491122661435556869092921 1118341996076667651819691)
        ·
          refine ⟨1677512994115001477729537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118341996076667651819691 1677512994115001477729537)
          ·
            refine ⟨1258134745586251108297153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677512994115001477729537 1258134745586251108297153)
            ·
              refine ⟨943601059189688331222865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258134745586251108297153 943601059189688331222865)
              ·
                refine ⟨707700794392266248417149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943601059189688331222865 707700794392266248417149)
                ·
                  refine ⟨265387797897099843156431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707700794392266248417149 265387797897099843156431)
                  ·
                    rfl

theorem cell20_581446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_581446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581446 prefixEnd_581446 := by exact prefixLift 581446
  have htrace : WordTrace (prefixWord ++ tailWord_581446) baseStart_581446 baseEnd_581446 := by
    simpa [prefixWord, tailWord_581446, baseEnd_581446] using wordTrace_append hprefix tailTrace_581446
  have hstable : (prefixWord ++ tailWord_581446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581446).length < 2 ^ (prefixWord ++ tailWord_581446).sum := by decide
  have hdescent : baseEnd_581446 < baseStart_581446 := by decide
  rcases family_descends (prefixWord ++ tailWord_581446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581453 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 2]
def baseStart_581453 : Nat := 118140960795 + 581453 * 2 ^ 59
def prefixEnd_581453 : Nat := 4983230072969 + 3 ^ 40 * 581453 * 2
def baseEnd_581453 : Nat := 265390992887838929923069

theorem tailTrace_581453 : CollatzResearch.WordTrace tailWord_581453 prefixEnd_581453 265390992887838929923069 := by
  unfold tailWord_581453
  simp only [CollatzResearch.WordTrace]
  refine ⟨21207333162502560111493013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14138222108335040074328675 21207333162502560111493013)
  ·
    refine ⟨994093741992307505226235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21207333162502560111493013 994093741992307505226235)
    ·
      refine ⟨1491140612988461257839353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994093741992307505226235 1491140612988461257839353)
      ·
        refine ⟨1118355459741345943379515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491140612988461257839353 1118355459741345943379515)
        ·
          refine ⟨1677533189612018915069273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118355459741345943379515 1677533189612018915069273)
          ·
            refine ⟨1258149892209014186301955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677533189612018915069273 1258149892209014186301955)
            ·
              refine ⟨1887224838313521279452933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258149892209014186301955 1887224838313521279452933)
              ·
                refine ⟨353854657183785239897425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1887224838313521279452933 353854657183785239897425)
                ·
                  refine ⟨265390992887838929923069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353854657183785239897425 265390992887838929923069)
                  ·
                    rfl

theorem cell20_581453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_581453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581453 prefixEnd_581453 := by exact prefixLift 581453
  have htrace : WordTrace (prefixWord ++ tailWord_581453) baseStart_581453 baseEnd_581453 := by
    simpa [prefixWord, tailWord_581453, baseEnd_581453] using wordTrace_append hprefix tailTrace_581453
  have hstable : (prefixWord ++ tailWord_581453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581453).length < 2 ^ (prefixWord ++ tailWord_581453).sum := by decide
  have hdescent : baseEnd_581453 < baseStart_581453 := by decide
  rcases family_descends (prefixWord ++ tailWord_581453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581471 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_581471 : Nat := 118140960795 + 581471 * 2 ^ 59
def prefixEnd_581471 : Nat := 4983230072969 + 3 ^ 40 * 581471 * 2
def baseEnd_581471 : Nat := 265399208578310867322995

theorem tailTrace_581471 : CollatzResearch.WordTrace tailWord_581471 prefixEnd_581471 265399208578310867322995 := by
  unfold tailWord_581471
  simp only [CollatzResearch.WordTrace]
  refine ⟨21207989676437349185648267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14138659784291566123765511 21207989676437349185648267)
  ·
    refine ⟨31811984514656023778472401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21207989676437349185648267 31811984514656023778472401)
    ·
      refine ⟨23858988385992017833854301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31811984514656023778472401 23858988385992017833854301)
      ·
        refine ⟨8947120644747006687695363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23858988385992017833854301 8947120644747006687695363)
        ·
          refine ⟨13420680967120510031543045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8947120644747006687695363 13420680967120510031543045)
          ·
            refine ⟨2516377681335095630914321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13420680967120510031543045 2516377681335095630914321)
            ·
              refine ⟨1887283261001321723185741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516377681335095630914321 1887283261001321723185741)
              ·
                refine ⟨707731222875495646194653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1887283261001321723185741 707731222875495646194653)
                ·
                  refine ⟨265399208578310867322995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707731222875495646194653 265399208578310867322995)
                  ·
                    rfl

theorem cell20_581471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_581471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581471 prefixEnd_581471 := by exact prefixLift 581471
  have htrace : WordTrace (prefixWord ++ tailWord_581471) baseStart_581471 baseEnd_581471 := by
    simpa [prefixWord, tailWord_581471, baseEnd_581471] using wordTrace_append hprefix tailTrace_581471
  have hstable : (prefixWord ++ tailWord_581471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581471).length < 2 ^ (prefixWord ++ tailWord_581471).sum := by decide
  have hdescent : baseEnd_581471 < baseStart_581471 := by decide
  rcases family_descends (prefixWord ++ tailWord_581471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581485 : List Nat := [1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_581485 : Nat := 118140960795 + 581485 * 2 ^ 59
def prefixEnd_581485 : Nat := 4983230072969 + 3 ^ 40 * 581485 * 2
def baseEnd_581485 : Nat := 88468532853263013618757

theorem tailTrace_581485 : CollatzResearch.WordTrace tailWord_581485 prefixEnd_581485 88468532853263013618757 := by
  unfold tailWord_581485
  simp only [CollatzResearch.WordTrace]
  refine ⟨21208500298386629576657909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14139000198924419717771939 21208500298386629576657909)
  ·
    refine ⟨1988296902973746522811679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21208500298386629576657909 1988296902973746522811679)
    ·
      refine ⟨2982445354460619784217519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1988296902973746522811679 2982445354460619784217519)
      ·
        refine ⟨4473668031690929676326279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982445354460619784217519 4473668031690929676326279)
        ·
          refine ⟨6710502047536394514489419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4473668031690929676326279 6710502047536394514489419)
          ·
            refine ⟨10065753071304591771734129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6710502047536394514489419 10065753071304591771734129)
            ·
              refine ⟨7549314803478443828800597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10065753071304591771734129 7549314803478443828800597)
              ·
                refine ⟨88468532853263013618757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7549314803478443828800597 88468532853263013618757)
                ·
                  rfl

theorem cell20_581485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_581485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581485 prefixEnd_581485 := by exact prefixLift 581485
  have htrace : WordTrace (prefixWord ++ tailWord_581485) baseStart_581485 baseEnd_581485 := by
    simpa [prefixWord, tailWord_581485, baseEnd_581485] using wordTrace_append hprefix tailTrace_581485
  have hstable : (prefixWord ++ tailWord_581485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581485).length < 2 ^ (prefixWord ++ tailWord_581485).sum := by decide
  have hdescent : baseEnd_581485 < baseStart_581485 := by decide
  rcases family_descends (prefixWord ++ tailWord_581485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581499 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_581499 : Nat := 118140960795 + 581499 * 2 ^ 59
def prefixEnd_581499 : Nat := 4983230072969 + 3 ^ 40 * 581499 * 2
def baseEnd_581499 : Nat := 265411988541267214389547

theorem tailTrace_581499 : CollatzResearch.WordTrace tailWord_581499 prefixEnd_581499 265411988541267214389547 := by
  unfold tailWord_581499
  simp only [CollatzResearch.WordTrace]
  refine ⟨21209010920335909967667551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14139340613557273311778367 21209010920335909967667551)
  ·
    refine ⟨31813516380503864951501327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21209010920335909967667551 31813516380503864951501327)
    ·
      refine ⟨47720274570755797427251991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31813516380503864951501327 47720274570755797427251991)
      ·
        refine ⟨71580411856133696140877987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47720274570755797427251991 71580411856133696140877987)
        ·
          refine ⟨107370617784200544211316981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71580411856133696140877987 107370617784200544211316981)
          ·
            refine ⟨10065995417268801019810967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107370617784200544211316981 10065995417268801019810967)
            ·
              refine ⟨15098993125903201529716451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10065995417268801019810967 15098993125903201529716451)
              ·
                refine ⟨22648489688854802294574677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15098993125903201529716451 22648489688854802294574677)
                ·
                  refine ⟨265411988541267214389547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22648489688854802294574677 265411988541267214389547)
                  ·
                    rfl

theorem cell20_581499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_581499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581499 prefixEnd_581499 := by exact prefixLift 581499
  have htrace : WordTrace (prefixWord ++ tailWord_581499) baseStart_581499 baseEnd_581499 := by
    simpa [prefixWord, tailWord_581499, baseEnd_581499] using wordTrace_append hprefix tailTrace_581499
  have hstable : (prefixWord ++ tailWord_581499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581499).length < 2 ^ (prefixWord ++ tailWord_581499).sum := by decide
  have hdescent : baseEnd_581499 < baseStart_581499 := by decide
  rcases family_descends (prefixWord ++ tailWord_581499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581540 : List Nat := [2, 3, 1, 2, 1, 3, 4, 4]
def baseStart_581540 : Nat := 118140960795 + 581540 * 2 ^ 59
def prefixEnd_581540 : Nat := 4983230072969 + 3 ^ 40 * 581540 * 2
def baseEnd_581540 : Nat := 88476900686151098007571

theorem tailTrace_581540 : CollatzResearch.WordTrace tailWord_581540 prefixEnd_581540 88476900686151098007571 := by
  unfold tailWord_581540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605253156593686984955037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14140337542124915979940049 10605253156593686984955037)
  ·
    refine ⟨3976969933722632619358139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10605253156593686984955037 3976969933722632619358139)
    ·
      refine ⟨5965454900583948929037209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3976969933722632619358139 5965454900583948929037209)
      ·
        refine ⟨4474091175437961696777907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5965454900583948929037209 4474091175437961696777907)
        ·
          refine ⟨6711136763156942545166861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4474091175437961696777907 6711136763156942545166861)
          ·
            refine ⟨2516676286183853454437573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6711136763156942545166861 2516676286183853454437573)
            ·
              refine ⟨471876803659472522707045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2516676286183853454437573 471876803659472522707045)
              ·
                refine ⟨88476900686151098007571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 471876803659472522707045 88476900686151098007571)
                ·
                  rfl

theorem cell20_581540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_581540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581540 prefixEnd_581540 := by exact prefixLift 581540
  have htrace : WordTrace (prefixWord ++ tailWord_581540) baseStart_581540 baseEnd_581540 := by
    simpa [prefixWord, tailWord_581540, baseEnd_581540] using wordTrace_append hprefix tailTrace_581540
  have hstable : (prefixWord ++ tailWord_581540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581540).length < 2 ^ (prefixWord ++ tailWord_581540).sum := by decide
  have hdescent : baseEnd_581540 < baseStart_581540 := by decide
  rcases family_descends (prefixWord ++ tailWord_581540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581568 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_581568 : Nat := 118140960795 + 581568 * 2 ^ 59
def prefixEnd_581568 : Nat := 4983230072969 + 3 ^ 40 * 581568 * 2
def baseEnd_581568 : Nat := 265443482021409641089265

theorem tailTrace_581568 : CollatzResearch.WordTrace tailWord_581568 prefixEnd_581568 265443482021409641089265 := by
  unfold tailWord_581568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605763778542967375964679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14141018371390623167952905 10605763778542967375964679)
  ·
    refine ⟨15908645667814451063947019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10605763778542967375964679 15908645667814451063947019)
    ·
      refine ⟨23862968501721676595920529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15908645667814451063947019 23862968501721676595920529)
      ·
        refine ⟨17897226376291257446940397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23862968501721676595920529 17897226376291257446940397)
        ·
          refine ⟨6711459891109221542602649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17897226376291257446940397 6711459891109221542602649)
          ·
            refine ⟨5033594918331916156951987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6711459891109221542602649 5033594918331916156951987)
            ·
              refine ⟨7550392377497874235427981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033594918331916156951987 7550392377497874235427981)
              ·
                refine ⟨2831397141561702838285493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7550392377497874235427981 2831397141561702838285493)
                ·
                  refine ⟨265443482021409641089265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2831397141561702838285493 265443482021409641089265)
                  ·
                    rfl

theorem cell20_581568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_581568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581568 prefixEnd_581568 := by exact prefixLift 581568
  have htrace : WordTrace (prefixWord ++ tailWord_581568) baseStart_581568 baseEnd_581568 := by
    simpa [prefixWord, tailWord_581568, baseEnd_581568] using wordTrace_append hprefix tailTrace_581568
  have hstable : (prefixWord ++ tailWord_581568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581568).length < 2 ^ (prefixWord ++ tailWord_581568).sum := by decide
  have hdescent : baseEnd_581568 < baseStart_581568 := by decide
  rcases family_descends (prefixWord ++ tailWord_581568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581599 : List Nat := [1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_581599 : Nat := 118140960795 + 581599 * 2 ^ 59
def prefixEnd_581599 : Nat := 4983230072969 + 3 ^ 40 * 581599 * 2
def baseEnd_581599 : Nat := 88485877088703770351935

theorem tailTrace_581599 : CollatzResearch.WordTrace tailWord_581599 prefixEnd_581599 88485877088703770351935 := by
  unfold tailWord_581599
  simp only [CollatzResearch.WordTrace]
  refine ⟨21212658219973627046307851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14141772146649084697538567 21212658219973627046307851)
  ·
    refine ⟨31818987329960440569461777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21212658219973627046307851 31818987329960440569461777)
    ·
      refine ⟨23864240497470330427096333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31818987329960440569461777 23864240497470330427096333)
      ·
        refine ⟨8949090186551373910161125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23864240497470330427096333 8949090186551373910161125)
        ·
          refine ⟨1677954409978382608155211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8949090186551373910161125 1677954409978382608155211)
          ·
            refine ⟨2516931614967573912232817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677954409978382608155211 2516931614967573912232817)
            ·
              refine ⟨1887698711225680434174613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516931614967573912232817 1887698711225680434174613)
              ·
                refine ⟨88485877088703770351935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1887698711225680434174613 88485877088703770351935)
                ·
                  rfl

theorem cell20_581599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_581599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581599 prefixEnd_581599 := by exact prefixLift 581599
  have htrace : WordTrace (prefixWord ++ tailWord_581599) baseStart_581599 baseEnd_581599 := by
    simpa [prefixWord, tailWord_581599, baseEnd_581599] using wordTrace_append hprefix tailTrace_581599
  have hstable : (prefixWord ++ tailWord_581599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581599).length < 2 ^ (prefixWord ++ tailWord_581599).sum := by decide
  have hdescent : baseEnd_581599 < baseStart_581599 := by decide
  rcases family_descends (prefixWord ++ tailWord_581599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581622 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_581622 : Nat := 118140960795 + 581622 * 2 ^ 59
def prefixEnd_581622 : Nat := 4983230072969 + 3 ^ 40 * 581622 * 2
def baseEnd_581622 : Nat := 265468129092825453289045

theorem tailTrace_581622 : CollatzResearch.WordTrace tailWord_581622 prefixEnd_581622 265468129092825453289045 := by
  unfold tailWord_581622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325843568680643873399695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14142331399260201316263413 1325843568680643873399695)
  ·
    refine ⟨1988765353020965810099543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1325843568680643873399695 1988765353020965810099543)
    ·
      refine ⟨2983148029531448715149315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1988765353020965810099543 2983148029531448715149315)
      ·
        refine ⟨4474722044297173072723973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983148029531448715149315 4474722044297173072723973)
        ·
          refine ⟨839010383305719951135745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4474722044297173072723973 839010383305719951135745)
          ·
            refine ⟨629257787479289963351809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839010383305719951135745 629257787479289963351809)
            ·
              refine ⟨471943340609467472513857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629257787479289963351809 471943340609467472513857)
              ·
                refine ⟨353957505457100604385393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471943340609467472513857 353957505457100604385393)
                ·
                  refine ⟨265468129092825453289045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353957505457100604385393 265468129092825453289045)
                  ·
                    rfl

theorem cell20_581622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_581622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581622 prefixEnd_581622 := by exact prefixLift 581622
  have htrace : WordTrace (prefixWord ++ tailWord_581622) baseStart_581622 baseEnd_581622 := by
    simpa [prefixWord, tailWord_581622, baseEnd_581622] using wordTrace_append hprefix tailTrace_581622
  have hstable : (prefixWord ++ tailWord_581622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581622).length < 2 ^ (prefixWord ++ tailWord_581622).sum := by decide
  have hdescent : baseEnd_581622 < baseStart_581622 := by decide
  rcases family_descends (prefixWord ++ tailWord_581622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581637 : List Nat := [1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_581637 : Nat := 118140960795 + 581637 * 2 ^ 59
def prefixEnd_581637 : Nat := 4983230072969 + 3 ^ 40 * 581637 * 2
def baseEnd_581637 : Nat := 88491658500517355929661

theorem tailTrace_581637 : CollatzResearch.WordTrace tailWord_581637 prefixEnd_581637 88491658500517355929661 := by
  unfold tailWord_581637
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214044193835959536191165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14142696129223973024127443 21214044193835959536191165)
  ·
    refine ⟨7955266572688484826071687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21214044193835959536191165 7955266572688484826071687)
    ·
      refine ⟨11932899859032727239107531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7955266572688484826071687 11932899859032727239107531)
      ·
        refine ⟨17899349788549090858661297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11932899859032727239107531 17899349788549090858661297)
        ·
          refine ⟨13424512341411818143995973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17899349788549090858661297 13424512341411818143995973)
          ·
            refine ⟨2517096064014715901999245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13424512341411818143995973 2517096064014715901999245)
            ·
              refine ⟨943911024005518463249717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517096064014715901999245 943911024005518463249717)
              ·
                refine ⟨88491658500517355929661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 943911024005518463249717 88491658500517355929661)
                ·
                  rfl

theorem cell20_581637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_581637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581637 prefixEnd_581637 := by exact prefixLift 581637
  have htrace : WordTrace (prefixWord ++ tailWord_581637) baseStart_581637 baseEnd_581637 := by
    simpa [prefixWord, tailWord_581637, baseEnd_581637] using wordTrace_append hprefix tailTrace_581637
  have hstable : (prefixWord ++ tailWord_581637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581637).length < 2 ^ (prefixWord ++ tailWord_581637).sum := by decide
  have hdescent : baseEnd_581637 < baseStart_581637 := by decide
  rcases family_descends (prefixWord ++ tailWord_581637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581651 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_581651 : Nat := 118140960795 + 581651 * 2 ^ 59
def prefixEnd_581651 : Nat := 4983230072969 + 3 ^ 40 * 581651 * 2
def baseEnd_581651 : Nat := 265481365483030241322259

theorem tailTrace_581651 : CollatzResearch.WordTrace tailWord_581651 prefixEnd_581651 265481365483030241322259 := by
  unfold tailWord_581651
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214554815785239927200807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14143036543856826618133871 21214554815785239927200807)
  ·
    refine ⟨31821832223677859890801211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214554815785239927200807 31821832223677859890801211)
    ·
      refine ⟨47732748335516789836201817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31821832223677859890801211 47732748335516789836201817)
      ·
        refine ⟨35799561251637592377151363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47732748335516789836201817 35799561251637592377151363)
        ·
          refine ⟨53699341877456388565727045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35799561251637592377151363 53699341877456388565727045)
          ·
            refine ⟨10068626602023072856073821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53699341877456388565727045 10068626602023072856073821)
            ·
              refine ⟨3775734975758652321027683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10068626602023072856073821 3775734975758652321027683)
              ·
                refine ⟨5663602463637978481541525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775734975758652321027683 5663602463637978481541525)
                ·
                  refine ⟨265481365483030241322259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5663602463637978481541525 265481365483030241322259)
                  ·
                    rfl

theorem cell20_581651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_581651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581651 prefixEnd_581651 := by exact prefixLift 581651
  have htrace : WordTrace (prefixWord ++ tailWord_581651) baseStart_581651 baseEnd_581651 := by
    simpa [prefixWord, tailWord_581651, baseEnd_581651] using wordTrace_append hprefix tailTrace_581651
  have hstable : (prefixWord ++ tailWord_581651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581651).length < 2 ^ (prefixWord ++ tailWord_581651).sum := by decide
  have hdescent : baseEnd_581651 < baseStart_581651 := by decide
  rcases family_descends (prefixWord ++ tailWord_581651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581678 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_581678 : Nat := 118140960795 + 581678 * 2 ^ 59
def prefixEnd_581678 : Nat := 4983230072969 + 3 ^ 40 * 581678 * 2
def baseEnd_581678 : Nat := 265493689018738147422149

theorem tailTrace_581678 : CollatzResearch.WordTrace tailWord_581678 prefixEnd_581678 265493689018738147422149 := by
  unfold tailWord_581678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651942448335927942304211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14143693057791615692289125 2651942448335927942304211)
  ·
    refine ⟨3977913672503891913456317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2651942448335927942304211 3977913672503891913456317)
    ·
      refine ⟨1491717627188959467546119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3977913672503891913456317 1491717627188959467546119)
      ·
        refine ⟨2237576440783439201319179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491717627188959467546119 2237576440783439201319179)
        ·
          refine ⟨3356364661175158801978769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237576440783439201319179 3356364661175158801978769)
          ·
            refine ⟨2517273495881369101484077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356364661175158801978769 2517273495881369101484077)
            ·
              refine ⟨943977560955513413056529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517273495881369101484077 943977560955513413056529)
              ·
                refine ⟨707983170716635059792397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943977560955513413056529 707983170716635059792397)
                ·
                  refine ⟨265493689018738147422149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707983170716635059792397 265493689018738147422149)
                  ·
                    rfl

theorem cell20_581678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_581678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581678 prefixEnd_581678 := by exact prefixLift 581678
  have htrace : WordTrace (prefixWord ++ tailWord_581678) baseStart_581678 baseEnd_581678 := by
    simpa [prefixWord, tailWord_581678, baseEnd_581678] using wordTrace_append hprefix tailTrace_581678
  have hstable : (prefixWord ++ tailWord_581678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581678).length < 2 ^ (prefixWord ++ tailWord_581678).sum := by decide
  have hdescent : baseEnd_581678 < baseStart_581678 := by decide
  rcases family_descends (prefixWord ++ tailWord_581678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581685 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 2]
def baseStart_581685 : Nat := 118140960795 + 581685 * 2 ^ 59
def prefixEnd_581685 : Nat := 4983230072969 + 3 ^ 40 * 581685 * 2
def baseEnd_581685 : Nat := 265496884009477234188787

theorem tailTrace_581685 : CollatzResearch.WordTrace tailWord_581685 prefixEnd_581685 265496884009477234188787 := by
  unfold tailWord_581685
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215794897662063733938509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14143863265108042489292339 21215794897662063733938509)
  ·
    refine ⟨7955923086623273900226941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21215794897662063733938509 7955923086623273900226941)
    ·
      refine ⟨2983471157483727712585103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7955923086623273900226941 2983471157483727712585103)
      ·
        refine ⟨4475206736225591568877655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983471157483727712585103 4475206736225591568877655)
        ·
          refine ⟨6712810104338387353316483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4475206736225591568877655 6712810104338387353316483)
          ·
            refine ⟨10069215156507581029974725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6712810104338387353316483 10069215156507581029974725)
            ·
              refine ⟨1887977841845171443120261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10069215156507581029974725 1887977841845171443120261)
              ·
                refine ⟨353995845345969645585049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1887977841845171443120261 353995845345969645585049)
                ·
                  refine ⟨265496884009477234188787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353995845345969645585049 265496884009477234188787)
                  ·
                    rfl

theorem cell20_581685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_581685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581685 prefixEnd_581685 := by exact prefixLift 581685
  have htrace : WordTrace (prefixWord ++ tailWord_581685) baseStart_581685 baseEnd_581685 := by
    simpa [prefixWord, tailWord_581685, baseEnd_581685] using wordTrace_append hprefix tailTrace_581685
  have hstable : (prefixWord ++ tailWord_581685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581685).length < 2 ^ (prefixWord ++ tailWord_581685).sum := by decide
  have hdescent : baseEnd_581685 < baseStart_581685 := by decide
  rcases family_descends (prefixWord ++ tailWord_581685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581720 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_581720 : Nat := 118140960795 + 581720 * 2 ^ 59
def prefixEnd_581720 : Nat := 4983230072969 + 3 ^ 40 * 581720 * 2
def baseEnd_581720 : Nat := 265512858963172668021977

theorem tailTrace_581720 : CollatzResearch.WordTrace tailWord_581720 prefixEnd_581720 265512858963172668021977 := by
  unfold tailWord_581720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608535726267632355731307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14144714301690176474308409 10608535726267632355731307)
  ·
    refine ⟨15912803589401448533596961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608535726267632355731307 15912803589401448533596961)
    ·
      refine ⟨11934602692051086400197721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15912803589401448533596961 11934602692051086400197721)
      ·
        refine ⟨8950952019038314800148291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11934602692051086400197721 8950952019038314800148291)
        ·
          refine ⟨13426428028557472200222437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8950952019038314800148291 13426428028557472200222437)
          ·
            refine ⟨2517455255354526037541707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13426428028557472200222437 2517455255354526037541707)
            ·
              refine ⟨3776182883031789056312561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517455255354526037541707 3776182883031789056312561)
              ·
                refine ⟨2832137162273841792234421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3776182883031789056312561 2832137162273841792234421)
                ·
                  refine ⟨265512858963172668021977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2832137162273841792234421 265512858963172668021977)
                  ·
                    rfl

theorem cell20_581720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_581720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581720 prefixEnd_581720 := by exact prefixLift 581720
  have htrace : WordTrace (prefixWord ++ tailWord_581720) baseStart_581720 baseEnd_581720 := by
    simpa [prefixWord, tailWord_581720, baseEnd_581720] using wordTrace_append hprefix tailTrace_581720
  have hstable : (prefixWord ++ tailWord_581720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581720).length < 2 ^ (prefixWord ++ tailWord_581720).sum := by decide
  have hdescent : baseEnd_581720 < baseStart_581720 := by decide
  rcases family_descends (prefixWord ++ tailWord_581720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581726 : List Nat := [4, 4, 1, 1, 2, 2, 6]
def baseStart_581726 : Nat := 118140960795 + 581726 * 2 ^ 59
def prefixEnd_581726 : Nat := 4983230072969 + 3 ^ 40 * 581726 * 2
def baseEnd_581726 : Nat := 29501733058518145980217

theorem tailTrace_581726 : CollatzResearch.WordTrace tailWord_581726 prefixEnd_581726 29501733058518145980217 := by
  unfold tailWord_581726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652161286314190967022629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14144860193675685157454021 2652161286314190967022629)
  ·
    refine ⟨497280241183910806316743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2652161286314190967022629 497280241183910806316743)
    ·
      refine ⟨745920361775866209475115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497280241183910806316743 745920361775866209475115)
      ·
        refine ⟨1118880542663799314212673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745920361775866209475115 1118880542663799314212673)
        ·
          refine ⟨839160406997849485659505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1118880542663799314212673 839160406997849485659505)
          ·
            refine ⟨629370305248387114244629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839160406997849485659505 629370305248387114244629)
            ·
              refine ⟨29501733058518145980217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 629370305248387114244629 29501733058518145980217)
              ·
                rfl

theorem cell20_581726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 6].length) (baseStart_581726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581726 prefixEnd_581726 := by exact prefixLift 581726
  have htrace : WordTrace (prefixWord ++ tailWord_581726) baseStart_581726 baseEnd_581726 := by
    simpa [prefixWord, tailWord_581726, baseEnd_581726] using wordTrace_append hprefix tailTrace_581726
  have hstable : (prefixWord ++ tailWord_581726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581726).length < 2 ^ (prefixWord ++ tailWord_581726).sum := by decide
  have hdescent : baseEnd_581726 < baseStart_581726 := by decide
  rcases family_descends (prefixWord ++ tailWord_581726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581740 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 2]
def baseStart_581740 : Nat := 118140960795 + 581740 * 2 ^ 59
def prefixEnd_581740 : Nat := 4983230072969 + 3 ^ 40 * 581740 * 2
def baseEnd_581740 : Nat := 265521987508141487355229

theorem tailTrace_581740 : CollatzResearch.WordTrace tailWord_581740 prefixEnd_581740 265521987508141487355229 := by
  unfold tailWord_581740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608900456231404063595337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14145200608308538751460449 10608900456231404063595337)
  ·
    refine ⟨7956675342173553047696503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10608900456231404063595337 7956675342173553047696503)
    ·
      refine ⟨11935013013260329571544755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7956675342173553047696503 11935013013260329571544755)
      ·
        refine ⟨17902519519890494357317133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935013013260329571544755 17902519519890494357317133)
        ·
          refine ⟨6713444819958935383993925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17902519519890494357317133 6713444819958935383993925)
          ·
            refine ⟨1258770903742300384498861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6713444819958935383993925 1258770903742300384498861)
            ·
              refine ⟨472039088903362644187073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1258770903742300384498861 472039088903362644187073)
              ·
                refine ⟨354029316677521983140305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472039088903362644187073 354029316677521983140305)
                ·
                  refine ⟨265521987508141487355229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354029316677521983140305 265521987508141487355229)
                  ·
                    rfl

theorem cell20_581740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_581740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581740 prefixEnd_581740 := by exact prefixLift 581740
  have htrace : WordTrace (prefixWord ++ tailWord_581740) baseStart_581740 baseEnd_581740 := by
    simpa [prefixWord, tailWord_581740, baseEnd_581740] using wordTrace_append hprefix tailTrace_581740
  have hstable : (prefixWord ++ tailWord_581740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581740).length < 2 ^ (prefixWord ++ tailWord_581740).sum := by decide
  have hdescent : baseEnd_581740 < baseStart_581740 := by decide
  rcases family_descends (prefixWord ++ tailWord_581740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581744 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_581744 : Nat := 118140960795 + 581744 * 2 ^ 59
def prefixEnd_581744 : Nat := 4983230072969 + 3 ^ 40 * 581744 * 2
def baseEnd_581744 : Nat := 265523813217135251221879

theorem tailTrace_581744 : CollatzResearch.WordTrace tailWord_581744 prefixEnd_581744 265523813217135251221879 := by
  unfold tailWord_581744
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608973402224158405168143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14145297869632211206890857 10608973402224158405168143)
  ·
    refine ⟨15913460103336237607752215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608973402224158405168143 15913460103336237607752215)
    ·
      refine ⟨23870190155004356411628323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15913460103336237607752215 23870190155004356411628323)
      ·
        refine ⟨35805285232506534617442485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23870190155004356411628323 35805285232506534617442485)
        ·
          refine ⟨3356745490547487620385233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35805285232506534617442485 3356745490547487620385233)
          ·
            refine ⟨2517559117910615715288925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356745490547487620385233 2517559117910615715288925)
            ·
              refine ⟨944084669216480893233347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517559117910615715288925 944084669216480893233347)
              ·
                refine ⟨1416127003824721339850021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944084669216480893233347 1416127003824721339850021)
                ·
                  refine ⟨265523813217135251221879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416127003824721339850021 265523813217135251221879)
                  ·
                    rfl

theorem cell20_581744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_581744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581744 prefixEnd_581744 := by exact prefixLift 581744
  have htrace : WordTrace (prefixWord ++ tailWord_581744) baseStart_581744 baseEnd_581744 := by
    simpa [prefixWord, tailWord_581744, baseEnd_581744] using wordTrace_append hprefix tailTrace_581744
  have hstable : (prefixWord ++ tailWord_581744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581744).length < 2 ^ (prefixWord ++ tailWord_581744).sum := by decide
  have hdescent : baseEnd_581744 < baseStart_581744 := by decide
  rcases family_descends (prefixWord ++ tailWord_581744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581751 : List Nat := [1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_581751 : Nat := 118140960795 + 581751 * 2 ^ 59
def prefixEnd_581751 : Nat := 4983230072969 + 3 ^ 40 * 581751 * 2
def baseEnd_581751 : Nat := 88509002735958112662839

theorem tailTrace_581751 : CollatzResearch.WordTrace tailWord_581751 prefixEnd_581751 88509002735958112662839 := by
  unfold tailWord_581751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21218202115422957005841107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14145468076948638003894071 21218202115422957005841107)
  ·
    refine ⟨31827303173134435508761661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21218202115422957005841107 31827303173134435508761661)
    ·
      refine ⟨11935238689925413315785623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31827303173134435508761661 11935238689925413315785623)
      ·
        refine ⟨17902858034888119973678435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935238689925413315785623 17902858034888119973678435)
        ·
          refine ⟨26854287052332179960517653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17902858034888119973678435 26854287052332179960517653)
          ·
            refine ⟨1258794705578070935649265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26854287052332179960517653 1258794705578070935649265)
            ·
              refine ⟨944096029183553201736949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258794705578070935649265 944096029183553201736949)
              ·
                refine ⟨88509002735958112662839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 944096029183553201736949 88509002735958112662839)
                ·
                  rfl

theorem cell20_581751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_581751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581751 prefixEnd_581751 := by exact prefixLift 581751
  have htrace : WordTrace (prefixWord ++ tailWord_581751) baseStart_581751 baseEnd_581751 := by
    simpa [prefixWord, tailWord_581751, baseEnd_581751] using wordTrace_append hprefix tailTrace_581751
  have hstable : (prefixWord ++ tailWord_581751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581751).length < 2 ^ (prefixWord ++ tailWord_581751).sum := by decide
  have hdescent : baseEnd_581751 < baseStart_581751 := by decide
  rcases family_descends (prefixWord ++ tailWord_581751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581802 : List Nat := [3, 1, 5, 1, 3, 1, 1, 5]
def baseStart_581802 : Nat := 118140960795 + 581802 * 2 ^ 59
def prefixEnd_581802 : Nat := 4983230072969 + 3 ^ 40 * 581802 * 2
def baseEnd_581802 : Nat := 88516761999181609096103

theorem tailTrace_581802 : CollatzResearch.WordTrace tailWord_581802 prefixEnd_581802 88516761999181609096103 := by
  unfold tailWord_581802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305015559559548178986915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14146708158825461810631773 5305015559559548178986915)
  ·
    refine ⟨7957523339339322268480373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5305015559559548178986915 7957523339339322268480373)
    ·
      refine ⟨746017813063061462670035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7957523339339322268480373 746017813063061462670035)
      ·
        refine ⟨1119026719594592194005053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746017813063061462670035 1119026719594592194005053)
        ·
          refine ⟨419635019847972072751895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1119026719594592194005053 419635019847972072751895)
          ·
            refine ⟨629452529771958109127843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419635019847972072751895 629452529771958109127843)
            ·
              refine ⟨944178794657937163691765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629452529771958109127843 944178794657937163691765)
              ·
                refine ⟨88516761999181609096103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 944178794657937163691765 88516761999181609096103)
                ·
                  rfl

theorem cell20_581802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_581802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581802 prefixEnd_581802 := by exact prefixLift 581802
  have htrace : WordTrace (prefixWord ++ tailWord_581802) baseStart_581802 baseEnd_581802 := by
    simpa [prefixWord, tailWord_581802, baseEnd_581802] using wordTrace_append hprefix tailTrace_581802
  have hstable : (prefixWord ++ tailWord_581802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581802).length < 2 ^ (prefixWord ++ tailWord_581802).sum := by decide
  have hdescent : baseEnd_581802 < baseStart_581802 := by decide
  rcases family_descends (prefixWord ++ tailWord_581802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581834 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_581834 : Nat := 118140960795 + 581834 * 2 ^ 59
def prefixEnd_581834 : Nat := 4983230072969 + 3 ^ 40 * 581834 * 2
def baseEnd_581834 : Nat := 265564891669494938221511

theorem tailTrace_581834 : CollatzResearch.WordTrace tailWord_581834 prefixEnd_581834 265564891669494938221511 := by
  unfold tailWord_581834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305307343530565545278139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14147486249414841454075037 5305307343530565545278139)
  ·
    refine ⟨7957961015295848317917209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5305307343530565545278139 7957961015295848317917209)
    ·
      refine ⟨5968470761471886238437907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7957961015295848317917209 5968470761471886238437907)
      ·
        refine ⟨8952706142207829357656861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968470761471886238437907 8952706142207829357656861)
        ·
          refine ⟨3357264803327936009121323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8952706142207829357656861 3357264803327936009121323)
          ·
            refine ⟨5035897204991904013681985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357264803327936009121323 5035897204991904013681985)
            ·
              refine ⟨3776922903743928010261489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5035897204991904013681985 3776922903743928010261489)
              ·
                refine ⟨2832692177807946007696117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3776922903743928010261489 2832692177807946007696117)
                ·
                  refine ⟨265564891669494938221511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2832692177807946007696117 265564891669494938221511)
                  ·
                    rfl

theorem cell20_581834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_581834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581834 prefixEnd_581834 := by exact prefixLift 581834
  have htrace : WordTrace (prefixWord ++ tailWord_581834) baseStart_581834 baseEnd_581834 := by
    simpa [prefixWord, tailWord_581834, baseEnd_581834] using wordTrace_append hprefix tailTrace_581834
  have hstable : (prefixWord ++ tailWord_581834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581834).length < 2 ^ (prefixWord ++ tailWord_581834).sum := by decide
  have hdescent : baseEnd_581834 < baseStart_581834 := by decide
  rcases family_descends (prefixWord ++ tailWord_581834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581872 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_581872 : Nat := 118140960795 + 581872 * 2 ^ 59
def prefixEnd_581872 : Nat := 4983230072969 + 3 ^ 40 * 581872 * 2
def baseEnd_581872 : Nat := 265582235904935694954689

theorem tailTrace_581872 : CollatzResearch.WordTrace tailWord_581872 prefixEnd_581872 265582235904935694954689 := by
  unfold tailWord_581872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611307673992297335497935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14148410231989729780663913 10611307673992297335497935)
  ·
    refine ⟨15916961510988446003246903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10611307673992297335497935 15916961510988446003246903)
    ·
      refine ⟨23875442266482669004870355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15916961510988446003246903 23875442266482669004870355)
      ·
        refine ⟨35813163399724003507305533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23875442266482669004870355 35813163399724003507305533)
        ·
          refine ⟨13429936274896501315239575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35813163399724003507305533 13429936274896501315239575)
          ·
            refine ⟨20144904412344751972859363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13429936274896501315239575 20144904412344751972859363)
            ·
              refine ⟨30217356618517127959289045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20144904412344751972859363 30217356618517127959289045)
              ·
                refine ⟨708219295746495186545837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30217356618517127959289045 708219295746495186545837)
                ·
                  refine ⟨265582235904935694954689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708219295746495186545837 265582235904935694954689)
                  ·
                    rfl

theorem cell20_581872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_581872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581872 prefixEnd_581872 := by exact prefixLift 581872
  have htrace : WordTrace (prefixWord ++ tailWord_581872) baseStart_581872 baseEnd_581872 := by
    simpa [prefixWord, tailWord_581872, baseEnd_581872] using wordTrace_append hprefix tailTrace_581872
  have hstable : (prefixWord ++ tailWord_581872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581872).length < 2 ^ (prefixWord ++ tailWord_581872).sum := by decide
  have hdescent : baseEnd_581872 < baseStart_581872 := by decide
  rcases family_descends (prefixWord ++ tailWord_581872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581882 : List Nat := [3, 1, 1, 1, 1, 7, 2, 4]
def baseStart_581882 : Nat := 118140960795 + 581882 * 2 ^ 59
def prefixEnd_581882 : Nat := 4983230072969 + 3 ^ 40 * 581882 * 2
def baseEnd_581882 : Nat := 88528933392473368207105

theorem tailTrace_581882 : CollatzResearch.WordTrace tailWord_581882 prefixEnd_581882 88528933392473368207105 := by
  unfold tailWord_581882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305745019487091594714975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14148653385298910919239933 5305745019487091594714975)
  ·
    refine ⟨7958617529230637392072463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5305745019487091594714975 7958617529230637392072463)
    ·
      refine ⟨11937926293845956088108695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7958617529230637392072463 11937926293845956088108695)
      ·
        refine ⟨17906889440768934132163043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11937926293845956088108695 17906889440768934132163043)
        ·
          refine ⟨26860334161153401198244565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17906889440768934132163043 26860334161153401198244565)
          ·
            refine ⟨629539081902032840583857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26860334161153401198244565 629539081902032840583857)
            ·
              refine ⟨472154311426524630437893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629539081902032840583857 472154311426524630437893)
              ·
                refine ⟨88528933392473368207105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472154311426524630437893 88528933392473368207105)
                ·
                  rfl

theorem cell20_581882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_581882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581882 prefixEnd_581882 := by exact prefixLift 581882
  have htrace : WordTrace (prefixWord ++ tailWord_581882) baseStart_581882 baseEnd_581882 := by
    simpa [prefixWord, tailWord_581882, baseEnd_581882] using wordTrace_append hprefix tailTrace_581882
  have hstable : (prefixWord ++ tailWord_581882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581882).length < 2 ^ (prefixWord ++ tailWord_581882).sum := by decide
  have hdescent : baseEnd_581882 < baseStart_581882 := by decide
  rcases family_descends (prefixWord ++ tailWord_581882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581968 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 2]
def baseStart_581968 : Nat := 118140960795 + 581968 * 2 ^ 59
def prefixEnd_581968 : Nat := 4983230072969 + 3 ^ 40 * 581968 * 2
def baseEnd_581968 : Nat := 265626052920786027754297

theorem tailTrace_581968 : CollatzResearch.WordTrace tailWord_581968 prefixEnd_581968 265626052920786027754297 := by
  unfold tailWord_581968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10613058377818401533245279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14150744503757868710993705 10613058377818401533245279)
  ·
    refine ⟨15919587566727602299867919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10613058377818401533245279 15919587566727602299867919)
    ·
      refine ⟨23879381350091403449801879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15919587566727602299867919 23879381350091403449801879)
      ·
        refine ⟨35819072025137105174702819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23879381350091403449801879 35819072025137105174702819)
        ·
          refine ⟨53728608037705657762054229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35819072025137105174702819 53728608037705657762054229)
          ·
            refine ⟨629632125441863176899073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 53728608037705657762054229 629632125441863176899073)
            ·
              refine ⟨472224094081397382674305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629632125441863176899073 472224094081397382674305)
              ·
                refine ⟨354168070561048037005729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472224094081397382674305 354168070561048037005729)
                ·
                  refine ⟨265626052920786027754297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354168070561048037005729 265626052920786027754297)
                  ·
                    rfl

theorem cell20_581968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_581968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581968 prefixEnd_581968 := by exact prefixLift 581968
  have htrace : WordTrace (prefixWord ++ tailWord_581968) baseStart_581968 baseEnd_581968 := by
    simpa [prefixWord, tailWord_581968, baseEnd_581968] using wordTrace_append hprefix tailTrace_581968
  have hstable : (prefixWord ++ tailWord_581968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581968).length < 2 ^ (prefixWord ++ tailWord_581968).sum := by decide
  have hdescent : baseEnd_581968 < baseStart_581968 := by decide
  rcases family_descends (prefixWord ++ tailWord_581968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581993 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_581993 : Nat := 118140960795 + 581993 * 2 ^ 59
def prefixEnd_581993 : Nat := 4983230072969 + 3 ^ 40 * 581993 * 2
def baseEnd_581993 : Nat := 265637463601997051920861

theorem tailTrace_581993 : CollatzResearch.WordTrace tailWord_581993 prefixEnd_581993 265637463601997051920861 := by
  unfold tailWord_581993
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227028580546232336150633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14151352387030821557433755 21227028580546232336150633)
  ·
    refine ⟨15920271435409674252112975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21227028580546232336150633 15920271435409674252112975)
    ·
      refine ⟨23880407153114511378169463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15920271435409674252112975 23880407153114511378169463)
      ·
        refine ⟨35820610729671767067254195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23880407153114511378169463 35820610729671767067254195)
        ·
          refine ⟨53730916094507650600881293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35820610729671767067254195 53730916094507650600881293)
          ·
            refine ⟨20149093535440368975330485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53730916094507650600881293 20149093535440368975330485)
            ·
              refine ⟨1888977518947534591437233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20149093535440368975330485 1888977518947534591437233)
              ·
                refine ⟨1416733139210650943577925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888977518947534591437233 1416733139210650943577925)
                ·
                  refine ⟨265637463601997051920861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416733139210650943577925 265637463601997051920861)
                  ·
                    rfl

theorem cell20_581993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_581993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581993 prefixEnd_581993 := by exact prefixLift 581993
  have htrace : WordTrace (prefixWord ++ tailWord_581993) baseStart_581993 baseEnd_581993 := by
    simpa [prefixWord, tailWord_581993, baseEnd_581993] using wordTrace_append hprefix tailTrace_581993
  have hstable : (prefixWord ++ tailWord_581993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581993).length < 2 ^ (prefixWord ++ tailWord_581993).sum := by decide
  have hdescent : baseEnd_581993 < baseStart_581993 := by decide
  rcases family_descends (prefixWord ++ tailWord_581993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581996 : List Nat := [2, 2, 1, 1, 6, 1, 3, 4]
def baseStart_581996 : Nat := 118140960795 + 581996 * 2 ^ 59
def prefixEnd_581996 : Nat := 4983230072969 + 3 ^ 40 * 581996 * 2
def baseEnd_581996 : Nat := 88546277627914124940283

theorem tailTrace_581996 : CollatzResearch.WordTrace tailWord_581996 prefixEnd_581996 88546277627914124940283 := by
  unfold tailWord_581996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10613568999767681924254921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14151425333023575899006561 10613568999767681924254921)
  ·
    refine ⟨7960176749825761443191191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10613568999767681924254921 7960176749825761443191191)
    ·
      refine ⟨11940265124738642164786787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7960176749825761443191191 11940265124738642164786787)
      ·
        refine ⟨17910397687107963247180181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940265124738642164786787 17910397687107963247180181)
        ·
          refine ⟨839549891583185777211571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17910397687107963247180181 839549891583185777211571)
          ·
            refine ⟨1259324837374778665817357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839549891583185777211571 1259324837374778665817357)
            ·
              refine ⟨472246814015541999681509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1259324837374778665817357 472246814015541999681509)
              ·
                refine ⟨88546277627914124940283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472246814015541999681509 88546277627914124940283)
                ·
                  rfl

theorem cell20_581996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_581996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_581996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_581996 prefixEnd_581996 := by exact prefixLift 581996
  have htrace : WordTrace (prefixWord ++ tailWord_581996) baseStart_581996 baseEnd_581996 := by
    simpa [prefixWord, tailWord_581996, baseEnd_581996] using wordTrace_append hprefix tailTrace_581996
  have hstable : (prefixWord ++ tailWord_581996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581996).length < 2 ^ (prefixWord ++ tailWord_581996).sum := by decide
  have hdescent : baseEnd_581996 < baseStart_581996 := by decide
  rcases family_descends (prefixWord ++ tailWord_581996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582017 : List Nat := [1, 2, 4, 3, 1, 2, 7]
def baseStart_582017 : Nat := 118140960795 + 582017 * 2 ^ 59
def prefixEnd_582017 : Nat := 4983230072969 + 3 ^ 40 * 582017 * 2
def baseEnd_582017 : Nat := 29516490872884403902307

theorem tailTrace_582017 : CollatzResearch.WordTrace tailWord_582017 prefixEnd_582017 29516490872884403902307 := by
  unfold tailWord_582017
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227903932459284435024305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14151935954972856290016203 21227903932459284435024305)
  ·
    refine ⟨15920927949344463326268229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21227903932459284435024305 15920927949344463326268229)
    ·
      refine ⟨2985173990502086873675293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15920927949344463326268229 2985173990502086873675293)
      ·
        refine ⟨1119440246438282577628235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2985173990502086873675293 1119440246438282577628235)
        ·
          refine ⟨1679160369657423866442353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119440246438282577628235 1679160369657423866442353)
          ·
            refine ⟨1259370277243067899831765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679160369657423866442353 1259370277243067899831765)
            ·
              refine ⟨29516490872884403902307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1259370277243067899831765 29516490872884403902307)
              ·
                rfl

theorem cell20_582017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_582017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582017 prefixEnd_582017 := by exact prefixLift 582017
  have htrace : WordTrace (prefixWord ++ tailWord_582017) baseStart_582017 baseEnd_582017 := by
    simpa [prefixWord, tailWord_582017, baseEnd_582017] using wordTrace_append hprefix tailTrace_582017
  have hstable : (prefixWord ++ tailWord_582017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582017).length < 2 ^ (prefixWord ++ tailWord_582017).sum := by decide
  have hdescent : baseEnd_582017 < baseStart_582017 := by decide
  rcases family_descends (prefixWord ++ tailWord_582017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582024 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_582024 : Nat := 118140960795 + 582024 * 2 ^ 59
def prefixEnd_582024 : Nat := 4983230072969 + 3 ^ 40 * 582024 * 2
def baseEnd_582024 : Nat := 265651612846698721887401

theorem tailTrace_582024 : CollatzResearch.WordTrace tailWord_582024 prefixEnd_582024 265651612846698721887401 := by
  unfold tailWord_582024
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614079621716962315264563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14152106162289283087019417 10614079621716962315264563)
  ·
    refine ⟨15921119432575443472896845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10614079621716962315264563 15921119432575443472896845)
    ·
      refine ⟨5970419787215791302336317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15921119432575443472896845 5970419787215791302336317)
      ·
        refine ⟨2238907420205921738376119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5970419787215791302336317 2238907420205921738376119)
        ·
          refine ⟨3358361130308882607564179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238907420205921738376119 3358361130308882607564179)
          ·
            refine ⟨5037541695463323911346269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358361130308882607564179 5037541695463323911346269)
            ·
              refine ⟨1889078135798746466754851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5037541695463323911346269 1889078135798746466754851)
              ·
                refine ⟨2833617203698119700132277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889078135798746466754851 2833617203698119700132277)
                ·
                  refine ⟨265651612846698721887401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2833617203698119700132277 265651612846698721887401)
                  ·
                    rfl

theorem cell20_582024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_582024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582024 prefixEnd_582024 := by exact prefixLift 582024
  have htrace : WordTrace (prefixWord ++ tailWord_582024) baseStart_582024 baseEnd_582024 := by
    simpa [prefixWord, tailWord_582024, baseEnd_582024] using wordTrace_append hprefix tailTrace_582024
  have hstable : (prefixWord ++ tailWord_582024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582024).length < 2 ^ (prefixWord ++ tailWord_582024).sum := by decide
  have hdescent : baseEnd_582024 < baseStart_582024 := by decide
  rcases family_descends (prefixWord ++ tailWord_582024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582041 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 3]
def baseStart_582041 : Nat := 118140960795 + 582041 * 2 ^ 59
def prefixEnd_582041 : Nat := 4983230072969 + 3 ^ 40 * 582041 * 2
def baseEnd_582041 : Nat := 265659372109922218320665

theorem tailTrace_582041 : CollatzResearch.WordTrace tailWord_582041 prefixEnd_582041 265659372109922218320665 := by
  unfold tailWord_582041
  simp only [CollatzResearch.WordTrace]
  refine ⟨21228779284372336533897977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14152519522914891022598651 21228779284372336533897977)
  ·
    refine ⟨15921584463279252400423483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21228779284372336533897977 15921584463279252400423483)
    ·
      refine ⟨23882376694918878600635225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15921584463279252400423483 23882376694918878600635225)
      ·
        refine ⟨17911782521189158950476419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23882376694918878600635225 17911782521189158950476419)
        ·
          refine ⟨26867673781783738425714629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17911782521189158950476419 26867673781783738425714629)
          ·
            refine ⟨5037688834084450954821493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26867673781783738425714629 5037688834084450954821493)
            ·
              refine ⟨472283328195417277014515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5037688834084450954821493 472283328195417277014515)
              ·
                refine ⟨708424992293125915521773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472283328195417277014515 708424992293125915521773)
                ·
                  refine ⟨265659372109922218320665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708424992293125915521773 265659372109922218320665)
                  ·
                    rfl

theorem cell20_582041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_582041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582041 prefixEnd_582041 := by exact prefixLift 582041
  have htrace : WordTrace (prefixWord ++ tailWord_582041) baseStart_582041 baseEnd_582041 := by
    simpa [prefixWord, tailWord_582041, baseEnd_582041] using wordTrace_append hprefix tailTrace_582041
  have hstable : (prefixWord ++ tailWord_582041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582041).length < 2 ^ (prefixWord ++ tailWord_582041).sum := by decide
  have hdescent : baseEnd_582041 < baseStart_582041 := by decide
  rcases family_descends (prefixWord ++ tailWord_582041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582055 : List Nat := [1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_582055 : Nat := 118140960795 + 582055 * 2 ^ 59
def prefixEnd_582055 : Nat := 4983230072969 + 3 ^ 40 * 582055 * 2
def baseEnd_582055 : Nat := 88555254030466797284647

theorem tailTrace_582055 : CollatzResearch.WordTrace tailWord_582055 prefixEnd_582055 88555254030466797284647 := by
  unfold tailWord_582055
  simp only [CollatzResearch.WordTrace]
  refine ⟨21229289906321616924907619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14152859937547744616605079 21229289906321616924907619)
  ·
    refine ⟨31843934859482425387361429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21229289906321616924907619 31843934859482425387361429)
    ·
      refine ⟨1492684446538238690032567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31843934859482425387361429 1492684446538238690032567)
      ·
        refine ⟨2239026669807358035048851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492684446538238690032567 2239026669807358035048851)
        ·
          refine ⟨3358540004711037052573277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239026669807358035048851 3358540004711037052573277)
          ·
            refine ⟨1259452501766638894714979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3358540004711037052573277 1259452501766638894714979)
            ·
              refine ⟨1889178752649958342072469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259452501766638894714979 1889178752649958342072469)
              ·
                refine ⟨88555254030466797284647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1889178752649958342072469 88555254030466797284647)
                ·
                  rfl

theorem cell20_582055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_582055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582055 prefixEnd_582055 := by exact prefixLift 582055
  have htrace : WordTrace (prefixWord ++ tailWord_582055) baseStart_582055 baseEnd_582055 := by
    simpa [prefixWord, tailWord_582055, baseEnd_582055] using wordTrace_append hprefix tailTrace_582055
  have hstable : (prefixWord ++ tailWord_582055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582055).length < 2 ^ (prefixWord ++ tailWord_582055).sum := by decide
  have hdescent : baseEnd_582055 < baseStart_582055 := by decide
  rcases family_descends (prefixWord ++ tailWord_582055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582061 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 2]
def baseStart_582061 : Nat := 118140960795 + 582061 * 2 ^ 59
def prefixEnd_582061 : Nat := 4983230072969 + 3 ^ 40 * 582061 * 2
def baseEnd_582061 : Nat := 265668500654891037653917

theorem tailTrace_582061 : CollatzResearch.WordTrace tailWord_582061 prefixEnd_582061 265668500654891037653917 := by
  unfold tailWord_582061
  simp only [CollatzResearch.WordTrace]
  refine ⟨21229508744299879949626037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14153005829533253299750691 21229508744299879949626037)
  ·
    refine ⟨1990266444778113745277441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21229508744299879949626037 1990266444778113745277441)
    ·
      refine ⟨1492699833583585308958081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1990266444778113745277441 1492699833583585308958081)
      ·
        refine ⟨1119524875187688981718561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1492699833583585308958081 1119524875187688981718561)
        ·
          refine ⟨839643656390766736288921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1119524875187688981718561 839643656390766736288921)
          ·
            refine ⟨629732742293075052216691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839643656390766736288921 629732742293075052216691)
            ·
              refine ⟨944599113439612578325037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629732742293075052216691 944599113439612578325037)
              ·
                refine ⟨354224667539854716871889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944599113439612578325037 354224667539854716871889)
                ·
                  refine ⟨265668500654891037653917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354224667539854716871889 265668500654891037653917)
                  ·
                    rfl

theorem cell20_582061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_582061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582061 prefixEnd_582061 := by exact prefixLift 582061
  have htrace : WordTrace (prefixWord ++ tailWord_582061) baseStart_582061 baseEnd_582061 := by
    simpa [prefixWord, tailWord_582061, baseEnd_582061] using wordTrace_append hprefix tailTrace_582061
  have hstable : (prefixWord ++ tailWord_582061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582061).length < 2 ^ (prefixWord ++ tailWord_582061).sum := by decide
  have hdescent : baseEnd_582061 < baseStart_582061 := by decide
  rcases family_descends (prefixWord ++ tailWord_582061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582065 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 2]
def baseStart_582065 : Nat := 118140960795 + 582065 * 2 ^ 59
def prefixEnd_582065 : Nat := 4983230072969 + 3 ^ 40 * 582065 * 2
def baseEnd_582065 : Nat := 265670326363884801520567

theorem tailTrace_582065 : CollatzResearch.WordTrace tailWord_582065 prefixEnd_582065 265670326363884801520567 := by
  unfold tailWord_582065
  simp only [CollatzResearch.WordTrace]
  refine ⟨21229654636285388632771649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14153103090856925755181099 21229654636285388632771649)
  ·
    refine ⟨15922240977214041474578737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21229654636285388632771649 15922240977214041474578737)
    ·
      refine ⟨11941680732910531105934053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15922240977214041474578737 11941680732910531105934053)
      ·
        refine ⟨2239065137420724582362635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11941680732910531105934053 2239065137420724582362635)
        ·
          refine ⟨3358597706131086873543953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239065137420724582362635 3358597706131086873543953)
          ·
            refine ⟨2518948279598315155157965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3358597706131086873543953 2518948279598315155157965)
            ·
              refine ⟨944605604849368183184237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2518948279598315155157965 944605604849368183184237)
              ·
                refine ⟨354227101818513068694089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944605604849368183184237 354227101818513068694089)
                ·
                  refine ⟨265670326363884801520567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354227101818513068694089 265670326363884801520567)
                  ·
                    rfl

theorem cell20_582065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_582065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582065 prefixEnd_582065 := by exact prefixLift 582065
  have htrace : WordTrace (prefixWord ++ tailWord_582065) baseStart_582065 baseEnd_582065 := by
    simpa [prefixWord, tailWord_582065, baseEnd_582065] using wordTrace_append hprefix tailTrace_582065
  have hstable : (prefixWord ++ tailWord_582065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582065).length < 2 ^ (prefixWord ++ tailWord_582065).sum := by decide
  have hdescent : baseEnd_582065 < baseStart_582065 := by decide
  rcases family_descends (prefixWord ++ tailWord_582065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582068 : List Nat := [2, 5, 2, 2, 2, 1, 6]
def baseStart_582068 : Nat := 118140960795 + 582068 * 2 ^ 59
def prefixEnd_582068 : Nat := 4983230072969 + 3 ^ 40 * 582068 * 2
def baseEnd_582068 : Nat := 29519077293958902713395

theorem tailTrace_582068 : CollatzResearch.WordTrace tailWord_582068 prefixEnd_582068 29519077293958902713395 := by
  unfold tailWord_582068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614882027637260072565429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14153176036849680096753905 10614882027637260072565429)
  ·
    refine ⟨995145190090993131803009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10614882027637260072565429 995145190090993131803009)
    ·
      refine ⟨746358892568244848852257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 995145190090993131803009 746358892568244848852257)
      ·
        refine ⟨559769169426183636639193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 746358892568244848852257 559769169426183636639193)
        ·
          refine ⟨419826877069637727479395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559769169426183636639193 419826877069637727479395)
          ·
            refine ⟨629740315604456591219093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419826877069637727479395 629740315604456591219093)
            ·
              refine ⟨29519077293958902713395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 629740315604456591219093 29519077293958902713395)
              ·
                rfl

theorem cell20_582068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 6].length) (baseStart_582068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582068 prefixEnd_582068 := by exact prefixLift 582068
  have htrace : WordTrace (prefixWord ++ tailWord_582068) baseStart_582068 baseEnd_582068 := by
    simpa [prefixWord, tailWord_582068, baseEnd_582068] using wordTrace_append hprefix tailTrace_582068
  have hstable : (prefixWord ++ tailWord_582068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582068).length < 2 ^ (prefixWord ++ tailWord_582068).sum := by decide
  have hdescent : baseEnd_582068 < baseStart_582068 := by decide
  rcases family_descends (prefixWord ++ tailWord_582068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582121 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_582121 : Nat := 118140960795 + 582121 * 2 ^ 59
def prefixEnd_582121 : Nat := 4983230072969 + 3 ^ 40 * 582121 * 2
def baseEnd_582121 : Nat := 265695886289797495653671

theorem tailTrace_582121 : CollatzResearch.WordTrace tailWord_582121 prefixEnd_582121 265695886289797495653671 := by
  unfold tailWord_582121
  simp only [CollatzResearch.WordTrace]
  refine ⟨21231697124082510196810217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14154464749388340131206811 21231697124082510196810217)
  ·
    refine ⟨15923772843061882647607663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21231697124082510196810217 15923772843061882647607663)
    ·
      refine ⟨23885659264592823971411495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15923772843061882647607663 23885659264592823971411495)
      ·
        refine ⟨35828488896889235957117243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23885659264592823971411495 35828488896889235957117243)
        ·
          refine ⟨53742733345333853935675865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35828488896889235957117243 53742733345333853935675865)
          ·
            refine ⟨40307050009000390451756899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53742733345333853935675865 40307050009000390451756899)
            ·
              refine ⟨60460575013500585677635349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40307050009000390451756899 60460575013500585677635349)
              ·
                refine ⟨2834089453757839953639157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60460575013500585677635349 2834089453757839953639157)
                ·
                  refine ⟨265695886289797495653671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2834089453757839953639157 265695886289797495653671)
                  ·
                    rfl

theorem cell20_582121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_582121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582121 prefixEnd_582121 := by exact prefixLift 582121
  have htrace : WordTrace (prefixWord ++ tailWord_582121) baseStart_582121 baseEnd_582121 := by
    simpa [prefixWord, tailWord_582121, baseEnd_582121] using wordTrace_append hprefix tailTrace_582121
  have hstable : (prefixWord ++ tailWord_582121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582121).length < 2 ^ (prefixWord ++ tailWord_582121).sum := by decide
  have hdescent : baseEnd_582121 < baseStart_582121 := by decide
  rcases family_descends (prefixWord ++ tailWord_582121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582124 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 2]
def baseStart_582124 : Nat := 118140960795 + 582124 * 2 ^ 59
def prefixEnd_582124 : Nat := 4983230072969 + 3 ^ 40 * 582124 * 2
def baseEnd_582124 : Nat := 265697255571542818553659

theorem tailTrace_582124 : CollatzResearch.WordTrace tailWord_582124 prefixEnd_582124 265697255571542818553659 := by
  unfold tailWord_582124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615903271535820854584713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14154537695381094472779617 10615903271535820854584713)
  ·
    refine ⟨7961927453651865640938535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10615903271535820854584713 7961927453651865640938535)
    ·
      refine ⟨11942891180477798461407803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7961927453651865640938535 11942891180477798461407803)
      ·
        refine ⟨17914336770716697692111705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11942891180477798461407803 17914336770716697692111705)
        ·
          refine ⟨13435752578037523269083779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17914336770716697692111705 13435752578037523269083779)
          ·
            refine ⟨20153628867056284903625669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13435752578037523269083779 20153628867056284903625669)
            ·
              refine ⟨3778805412573053419429813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20153628867056284903625669 3778805412573053419429813)
              ·
                refine ⟨354263007428723758071545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3778805412573053419429813 354263007428723758071545)
                ·
                  refine ⟨265697255571542818553659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354263007428723758071545 265697255571542818553659)
                  ·
                    rfl

theorem cell20_582124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_582124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582124 prefixEnd_582124 := by exact prefixLift 582124
  have htrace : WordTrace (prefixWord ++ tailWord_582124) baseStart_582124 baseEnd_582124 := by
    simpa [prefixWord, tailWord_582124, baseEnd_582124] using wordTrace_append hprefix tailTrace_582124
  have hstable : (prefixWord ++ tailWord_582124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582124).length < 2 ^ (prefixWord ++ tailWord_582124).sum := by decide
  have hdescent : baseEnd_582124 < baseStart_582124 := by decide
  rcases family_descends (prefixWord ++ tailWord_582124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582148 : List Nat := [2, 3, 2, 3, 1, 3, 1, 5]
def baseStart_582148 : Nat := 118140960795 + 582148 * 2 ^ 59
def prefixEnd_582148 : Nat := 4983230072969 + 3 ^ 40 * 582148 * 2
def baseEnd_582148 : Nat := 88569403275168467251187

theorem tailTrace_582148 : CollatzResearch.WordTrace tailWord_582148 prefixEnd_582148 88569403275168467251187 := by
  unfold tailWord_582148
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616340947492346904021549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14155121263323129205362065 10616340947492346904021549)
  ·
    refine ⟨3981127855309630089008081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10616340947492346904021549 3981127855309630089008081)
    ·
      refine ⟨2985845891482222566756061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981127855309630089008081 2985845891482222566756061)
      ·
        refine ⟨1119692209305833462533523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2985845891482222566756061 1119692209305833462533523)
        ·
          refine ⟨1679538313958750193800285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119692209305833462533523 1679538313958750193800285)
          ·
            refine ⟨629826867734531322675107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1679538313958750193800285 629826867734531322675107)
            ·
              refine ⟨944740301601796984012661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629826867734531322675107 944740301601796984012661)
              ·
                refine ⟨88569403275168467251187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 944740301601796984012661 88569403275168467251187)
                ·
                  rfl

theorem cell20_582148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_582148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582148 prefixEnd_582148 := by exact prefixLift 582148
  have htrace : WordTrace (prefixWord ++ tailWord_582148) baseStart_582148 baseEnd_582148 := by
    simpa [prefixWord, tailWord_582148, baseEnd_582148] using wordTrace_append hprefix tailTrace_582148
  have hstable : (prefixWord ++ tailWord_582148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582148).length < 2 ^ (prefixWord ++ tailWord_582148).sum := by decide
  have hdescent : baseEnd_582148 < baseStart_582148 := by decide
  rcases family_descends (prefixWord ++ tailWord_582148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582179 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 2]
def baseStart_582179 : Nat := 118140960795 + 582179 * 2 ^ 59
def prefixEnd_582179 : Nat := 4983230072969 + 3 ^ 40 * 582179 * 2
def baseEnd_582179 : Nat := 265722359070207071720101

theorem tailTrace_582179 : CollatzResearch.WordTrace tailWord_582179 prefixEnd_582179 265722359070207071720101 := by
  unfold tailWord_582179
  simp only [CollatzResearch.WordTrace]
  refine ⟨21233812557872386102421591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14155875038581590734947727 21233812557872386102421591)
  ·
    refine ⟨31850718836808579153632387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21233812557872386102421591 31850718836808579153632387)
    ·
      refine ⟨47776078255212868730448581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31850718836808579153632387 47776078255212868730448581)
      ·
        refine ⟨8958014672852412886959109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47776078255212868730448581 8958014672852412886959109)
        ·
          refine ⟨1679627751159827416304833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8958014672852412886959109 1679627751159827416304833)
          ·
            refine ⟨1259720813369870562228625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679627751159827416304833 1259720813369870562228625)
            ·
              refine ⟨944790610027402921671469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259720813369870562228625 944790610027402921671469)
              ·
                refine ⟨354296478760276095626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944790610027402921671469 354296478760276095626801)
                ·
                  refine ⟨265722359070207071720101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354296478760276095626801 265722359070207071720101)
                  ·
                    rfl

theorem cell20_582179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 2].length) (baseStart_582179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582179 prefixEnd_582179 := by exact prefixLift 582179
  have htrace : WordTrace (prefixWord ++ tailWord_582179) baseStart_582179 baseEnd_582179 := by
    simpa [prefixWord, tailWord_582179, baseEnd_582179] using wordTrace_append hprefix tailTrace_582179
  have hstable : (prefixWord ++ tailWord_582179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582179).length < 2 ^ (prefixWord ++ tailWord_582179).sum := by decide
  have hdescent : baseEnd_582179 < baseStart_582179 := by decide
  rcases family_descends (prefixWord ++ tailWord_582179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582189 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 5]
def baseStart_582189 : Nat := 118140960795 + 582189 * 2 ^ 59
def prefixEnd_582189 : Nat := 4983230072969 + 3 ^ 40 * 582189 * 2
def baseEnd_582189 : Nat := 265726923342691481386727

theorem tailTrace_582189 : CollatzResearch.WordTrace tailWord_582189 prefixEnd_582189 265726923342691481386727 := by
  unfold tailWord_582189
  simp only [CollatzResearch.WordTrace]
  refine ⟨21234177287836157810285621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14156118191890771873523747 21234177287836157810285621)
  ·
    refine ⟨1990704120734639794714277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21234177287836157810285621 1990704120734639794714277)
    ·
      refine ⟨373257022637744961508927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1990704120734639794714277 373257022637744961508927)
      ·
        refine ⟨559885533956617442263391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373257022637744961508927 559885533956617442263391)
        ·
          refine ⟨839828300934926163395087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559885533956617442263391 839828300934926163395087)
          ·
            refine ⟨1259742451402389245092631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839828300934926163395087 1259742451402389245092631)
            ·
              refine ⟨1889613677103583867638947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259742451402389245092631 1889613677103583867638947)
              ·
                refine ⟨2834420515655375801458421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889613677103583867638947 2834420515655375801458421)
                ·
                  refine ⟨265726923342691481386727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2834420515655375801458421 265726923342691481386727)
                  ·
                    rfl

theorem cell20_582189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_582189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582189 prefixEnd_582189 := by exact prefixLift 582189
  have htrace : WordTrace (prefixWord ++ tailWord_582189) baseStart_582189 baseEnd_582189 := by
    simpa [prefixWord, tailWord_582189, baseEnd_582189] using wordTrace_append hprefix tailTrace_582189
  have hstable : (prefixWord ++ tailWord_582189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582189).length < 2 ^ (prefixWord ++ tailWord_582189).sum := by decide
  have hdescent : baseEnd_582189 < baseStart_582189 := by decide
  rcases family_descends (prefixWord ++ tailWord_582189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582196 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_582196 : Nat := 118140960795 + 582196 * 2 ^ 59
def prefixEnd_582196 : Nat := 4983230072969 + 3 ^ 40 * 582196 * 2
def baseEnd_582196 : Nat := 265730118333430568153365

theorem tailTrace_582196 : CollatzResearch.WordTrace tailWord_582196 prefixEnd_582196 265730118333430568153365 := by
  unfold tailWord_582196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10617216299405399002895221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14156288399207198670526961 10617216299405399002895221)
  ·
    refine ⟨995364028069256156521427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10617216299405399002895221 995364028069256156521427)
    ·
      refine ⟨1493046042103884234782141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995364028069256156521427 1493046042103884234782141)
      ·
        refine ⟨559892265788956588043303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1493046042103884234782141 559892265788956588043303)
        ·
          refine ⟨839838398683434882064955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559892265788956588043303 839838398683434882064955)
          ·
            refine ⟨1259757598025152323097433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839838398683434882064955 1259757598025152323097433)
            ·
              refine ⟨944818198518864242323075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259757598025152323097433 944818198518864242323075)
              ·
                refine ⟨1417227297778296363484613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944818198518864242323075 1417227297778296363484613)
                ·
                  refine ⟨265730118333430568153365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417227297778296363484613 265730118333430568153365)
                  ·
                    rfl

theorem cell20_582196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_582196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582196 prefixEnd_582196 := by exact prefixLift 582196
  have htrace : WordTrace (prefixWord ++ tailWord_582196) baseStart_582196 baseEnd_582196 := by
    simpa [prefixWord, tailWord_582196, baseEnd_582196] using wordTrace_append hprefix tailTrace_582196
  have hstable : (prefixWord ++ tailWord_582196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582196).length < 2 ^ (prefixWord ++ tailWord_582196).sum := by decide
  have hdescent : baseEnd_582196 < baseStart_582196 := by decide
  rcases family_descends (prefixWord ++ tailWord_582196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582200 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 2]
def baseStart_582200 : Nat := 118140960795 + 582200 * 2 ^ 59
def prefixEnd_582200 : Nat := 4983230072969 + 3 ^ 40 * 582200 * 2
def baseEnd_582200 : Nat := 265731944042424332020015

theorem tailTrace_582200 : CollatzResearch.WordTrace tailWord_582200 prefixEnd_582200 265731944042424332020015 := by
  unfold tailWord_582200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10617289245398153344468027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14156385660530871125957369 10617289245398153344468027)
  ·
    refine ⟨15925933868097230016702041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10617289245398153344468027 15925933868097230016702041)
    ·
      refine ⟨11944450401072922512526531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15925933868097230016702041 11944450401072922512526531)
      ·
        refine ⟨17916675601609383768789797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11944450401072922512526531 17916675601609383768789797)
        ·
          refine ⟨3359376675301759456648087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17916675601609383768789797 3359376675301759456648087)
          ·
            refine ⟨5039065012952639184972131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359376675301759456648087 5039065012952639184972131)
            ·
              refine ⟨7558597519428958777458197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039065012952639184972131 7558597519428958777458197)
              ·
                refine ⟨354309258723232442693353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7558597519428958777458197 354309258723232442693353)
                ·
                  refine ⟨265731944042424332020015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354309258723232442693353 265731944042424332020015)
                  ·
                    rfl

theorem cell20_582200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_582200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582200 prefixEnd_582200 := by exact prefixLift 582200
  have htrace : WordTrace (prefixWord ++ tailWord_582200) baseStart_582200 baseEnd_582200 := by
    simpa [prefixWord, tailWord_582200, baseEnd_582200] using wordTrace_append hprefix tailTrace_582200
  have hstable : (prefixWord ++ tailWord_582200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582200).length < 2 ^ (prefixWord ++ tailWord_582200).sum := by decide
  have hdescent : baseEnd_582200 < baseStart_582200 := by decide
  rcases family_descends (prefixWord ++ tailWord_582200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582245 : List Nat := [1, 3, 1, 3, 4, 2, 6]
def baseStart_582245 : Nat := 118140960795 + 582245 * 2 ^ 59
def prefixEnd_582245 : Nat := 4983230072969 + 3 ^ 40 * 582245 * 2
def baseEnd_582245 : Nat := 29528053696511575057759

theorem tailTrace_582245 : CollatzResearch.WordTrace tailWord_582245 prefixEnd_582245 29528053696511575057759 := by
  unfold tailWord_582245
  simp only [CollatzResearch.WordTrace]
  refine ⟨21236219775633279374324189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14157479850422186249549459 21236219775633279374324189)
  ·
    refine ⟨7963582415862479765371571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21236219775633279374324189 7963582415862479765371571)
    ·
      refine ⟨11945373623793719648057357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7963582415862479765371571 11945373623793719648057357)
      ·
        refine ⟨4479515108922644868021509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11945373623793719648057357 4479515108922644868021509)
        ·
          refine ⟨839909082922995912754033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4479515108922644868021509 839909082922995912754033)
          ·
            refine ⟨629931812192246934565525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839909082922995912754033 629931812192246934565525)
            ·
              refine ⟨29528053696511575057759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 629931812192246934565525 29528053696511575057759)
              ·
                rfl

theorem cell20_582245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_582245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582245 prefixEnd_582245 := by exact prefixLift 582245
  have htrace : WordTrace (prefixWord ++ tailWord_582245) baseStart_582245 baseEnd_582245 := by
    simpa [prefixWord, tailWord_582245, baseEnd_582245] using wordTrace_append hprefix tailTrace_582245
  have hstable : (prefixWord ++ tailWord_582245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582245).length < 2 ^ (prefixWord ++ tailWord_582245).sum := by decide
  have hdescent : baseEnd_582245 < baseStart_582245 := by decide
  rcases family_descends (prefixWord ++ tailWord_582245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582262 : List Nat := [5, 1, 1, 2, 3, 1, 2, 5]
def baseStart_582262 : Nat := 118140960795 + 582262 * 2 ^ 59
def prefixEnd_582262 : Nat := 4983230072969 + 3 ^ 40 * 582262 * 2
def baseEnd_582262 : Nat := 88586747510609223984365

theorem tailTrace_582262 : CollatzResearch.WordTrace tailWord_582262 prefixEnd_582262 88586747510609223984365 := by
  unfold tailWord_582262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327302488535730704855815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14157893211047794185128693 1327302488535730704855815)
  ·
    refine ⟨1990953732803596057283723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1327302488535730704855815 1990953732803596057283723)
    ·
      refine ⟨2986430599205394085925585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990953732803596057283723 2986430599205394085925585)
      ·
        refine ⟨2239822949404045564444189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2986430599205394085925585 2239822949404045564444189)
        ·
          refine ⟨839933606026517086666571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2239822949404045564444189 839933606026517086666571)
          ·
            refine ⟨1259900409039775629999857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839933606026517086666571 1259900409039775629999857)
            ·
              refine ⟨944925306779831722499893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259900409039775629999857 944925306779831722499893)
              ·
                refine ⟨88586747510609223984365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 944925306779831722499893 88586747510609223984365)
                ·
                  rfl

theorem cell20_582262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_582262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582262 prefixEnd_582262 := by exact prefixLift 582262
  have htrace : WordTrace (prefixWord ++ tailWord_582262) baseStart_582262 baseEnd_582262 := by
    simpa [prefixWord, tailWord_582262, baseEnd_582262] using wordTrace_append hprefix tailTrace_582262
  have hstable : (prefixWord ++ tailWord_582262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582262).length < 2 ^ (prefixWord ++ tailWord_582262).sum := by decide
  have hdescent : baseEnd_582262 < baseStart_582262 := by decide
  rcases family_descends (prefixWord ++ tailWord_582262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582269 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_582269 : Nat := 118140960795 + 582269 * 2 ^ 59
def prefixEnd_582269 : Nat := 4983230072969 + 3 ^ 40 * 582269 * 2
def baseEnd_582269 : Nat := 265763437522566758719733

theorem tailTrace_582269 : CollatzResearch.WordTrace tailWord_582269 prefixEnd_582269 265763437522566758719733 := by
  unfold tailWord_582269
  simp only [CollatzResearch.WordTrace]
  refine ⟨21237095127546331473197861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14158063418364220982131907 21237095127546331473197861)
  ·
    refine ⟨3981955336414937151224599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21237095127546331473197861 3981955336414937151224599)
    ·
      refine ⟨5972933004622405726836899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3981955336414937151224599 5972933004622405726836899)
      ·
        refine ⟨8959399506933608590255349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5972933004622405726836899 8959399506933608590255349)
        ·
          refine ⟨839943703775025805336439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8959399506933608590255349 839943703775025805336439)
          ·
            refine ⟨1259915555662538708004659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839943703775025805336439 1259915555662538708004659)
            ·
              refine ⟨1889873333493808062006989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259915555662538708004659 1889873333493808062006989)
              ·
                refine ⟨708702500060178023252621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1889873333493808062006989 708702500060178023252621)
                ·
                  refine ⟨265763437522566758719733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708702500060178023252621 265763437522566758719733)
                  ·
                    rfl

theorem cell20_582269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_582269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582269 prefixEnd_582269 := by exact prefixLift 582269
  have htrace : WordTrace (prefixWord ++ tailWord_582269) baseStart_582269 baseEnd_582269 := by
    simpa [prefixWord, tailWord_582269, baseEnd_582269] using wordTrace_append hprefix tailTrace_582269
  have hstable : (prefixWord ++ tailWord_582269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582269).length < 2 ^ (prefixWord ++ tailWord_582269).sum := by decide
  have hdescent : baseEnd_582269 < baseStart_582269 := by decide
  rcases family_descends (prefixWord ++ tailWord_582269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582304 : List Nat := [2, 1, 1, 4, 4, 8]
def baseStart_582304 : Nat := 118140960795 + 582304 * 2 ^ 59
def prefixEnd_582304 : Nat := 4983230072969 + 3 ^ 40 * 582304 * 2
def baseEnd_582304 : Nat := 9843681943565266390849

theorem tailTrace_582304 : CollatzResearch.WordTrace tailWord_582304 prefixEnd_582304 9843681943565266390849 := by
  unfold tailWord_582304
  simp only [CollatzResearch.WordTrace]
  refine ⟨10619185841209766225360983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14158914454946354967147977 10619185841209766225360983)
  ·
    refine ⟨15928778761814649338041475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10619185841209766225360983 15928778761814649338041475)
    ·
      refine ⟨23893168142721974007062213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15928778761814649338041475 23893168142721974007062213)
      ·
        refine ⟨4479969026760370126324165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23893168142721974007062213 4479969026760370126324165)
        ·
          refine ⟨839994192517569398685781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4479969026760370126324165 839994192517569398685781)
          ·
            refine ⟨9843681943565266390849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 839994192517569398685781 9843681943565266390849)
            ·
              rfl

theorem cell20_582304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 8].length) (baseStart_582304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582304 prefixEnd_582304 := by exact prefixLift 582304
  have htrace : WordTrace (prefixWord ++ tailWord_582304) baseStart_582304 baseEnd_582304 := by
    simpa [prefixWord, tailWord_582304, baseEnd_582304] using wordTrace_append hprefix tailTrace_582304
  have hstable : (prefixWord ++ tailWord_582304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582304).length < 2 ^ (prefixWord ++ tailWord_582304).sum := by decide
  have hdescent : baseEnd_582304 < baseStart_582304 := by decide
  rcases family_descends (prefixWord ++ tailWord_582304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582335 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_582335 : Nat := 118140960795 + 582335 * 2 ^ 59
def prefixEnd_582335 : Nat := 4983230072969 + 3 ^ 40 * 582335 * 2
def baseEnd_582335 : Nat := 265793561720963862519463

theorem tailTrace_582335 : CollatzResearch.WordTrace tailWord_582335 prefixEnd_582335 265793561720963862519463 := by
  unfold tailWord_582335
  simp only [CollatzResearch.WordTrace]
  refine ⟨21239502345307224745100459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14159668230204816496733639 21239502345307224745100459)
  ·
    refine ⟨31859253517960837117650689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21239502345307224745100459 31859253517960837117650689)
    ·
      refine ⟨23894440138470627838238017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31859253517960837117650689 23894440138470627838238017)
      ·
        refine ⟨17920830103852970878678513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23894440138470627838238017 17920830103852970878678513)
        ·
          refine ⟨13440622577889728159008885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17920830103852970878678513 13440622577889728159008885)
          ·
            refine ⟨1260058366677162014907083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13440622577889728159008885 1260058366677162014907083)
            ·
              refine ⟨1890087550015743022360625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260058366677162014907083 1890087550015743022360625)
              ·
                refine ⟨1417565662511807266770469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890087550015743022360625 1417565662511807266770469)
                ·
                  refine ⟨265793561720963862519463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417565662511807266770469 265793561720963862519463)
                  ·
                    rfl

theorem cell20_582335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_582335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582335 prefixEnd_582335 := by exact prefixLift 582335
  have htrace : WordTrace (prefixWord ++ tailWord_582335) baseStart_582335 baseEnd_582335 := by
    simpa [prefixWord, tailWord_582335, baseEnd_582335] using wordTrace_append hprefix tailTrace_582335
  have hstable : (prefixWord ++ tailWord_582335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582335).length < 2 ^ (prefixWord ++ tailWord_582335).sum := by decide
  have hdescent : baseEnd_582335 < baseStart_582335 := by decide
  rcases family_descends (prefixWord ++ tailWord_582335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582373 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_582373 : Nat := 118140960795 + 582373 * 2 ^ 59
def prefixEnd_582373 : Nat := 4983230072969 + 3 ^ 40 * 582373 * 2
def baseEnd_582373 : Nat := 265810905956404619252641

theorem tailTrace_582373 : CollatzResearch.WordTrace tailWord_582373 prefixEnd_582373 265810905956404619252641 := by
  unfold tailWord_582373
  simp only [CollatzResearch.WordTrace]
  refine ⟨21240888319169557234983773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14160592212779704823322515 21240888319169557234983773)
  ·
    refine ⟨7965333119688583963118915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21240888319169557234983773 7965333119688583963118915)
    ·
      refine ⟨11947999679532875944678373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7965333119688583963118915 11947999679532875944678373)
      ·
        refine ⟨2240249939912414239627195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11947999679532875944678373 2240249939912414239627195)
        ·
          refine ⟨3360374909868621359440793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240249939912414239627195 3360374909868621359440793)
          ·
            refine ⟨2520281182401466019580595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3360374909868621359440793 2520281182401466019580595)
            ·
              refine ⟨3780421773602199029370893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520281182401466019580595 3780421773602199029370893)
              ·
                refine ⟨1417658165100824636014085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3780421773602199029370893 1417658165100824636014085)
                ·
                  refine ⟨265810905956404619252641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417658165100824636014085 265810905956404619252641)
                  ·
                    rfl

theorem cell20_582373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_582373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582373 prefixEnd_582373 := by exact prefixLift 582373
  have htrace : WordTrace (prefixWord ++ tailWord_582373) baseStart_582373 baseEnd_582373 := by
    simpa [prefixWord, tailWord_582373, baseEnd_582373] using wordTrace_append hprefix tailTrace_582373
  have hstable : (prefixWord ++ tailWord_582373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582373).length < 2 ^ (prefixWord ++ tailWord_582373).sum := by decide
  have hdescent : baseEnd_582373 < baseStart_582373 := by decide
  rcases family_descends (prefixWord ++ tailWord_582373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582383 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 3]
def baseStart_582383 : Nat := 118140960795 + 582383 * 2 ^ 59
def prefixEnd_582383 : Nat := 4983230072969 + 3 ^ 40 * 582383 * 2
def baseEnd_582383 : Nat := 265815470228889028919267

theorem tailTrace_582383 : CollatzResearch.WordTrace tailWord_582383 prefixEnd_582383 265815470228889028919267 := by
  unfold tailWord_582383
  simp only [CollatzResearch.WordTrace]
  refine ⟨21241253049133328942847803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14160835366088885961898535 21241253049133328942847803)
  ·
    refine ⟨31861879573699993414271705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21241253049133328942847803 31861879573699993414271705)
    ·
      refine ⟨23896409680274995060703779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31861879573699993414271705 23896409680274995060703779)
      ·
        refine ⟨35844614520412492591055669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23896409680274995060703779 35844614520412492591055669)
        ·
          refine ⟨3360432611288671180411469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35844614520412492591055669 3360432611288671180411469)
          ·
            refine ⟨1260162229233251692654301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3360432611288671180411469 1260162229233251692654301)
            ·
              refine ⟨472560835962469384745363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1260162229233251692654301 472560835962469384745363)
              ·
                refine ⟨708841253943704077118045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472560835962469384745363 708841253943704077118045)
                ·
                  refine ⟨265815470228889028919267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708841253943704077118045 265815470228889028919267)
                  ·
                    rfl

theorem cell20_582383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_582383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582383 prefixEnd_582383 := by exact prefixLift 582383
  have htrace : WordTrace (prefixWord ++ tailWord_582383) baseStart_582383 baseEnd_582383 := by
    simpa [prefixWord, tailWord_582383, baseEnd_582383] using wordTrace_append hprefix tailTrace_582383
  have hstable : (prefixWord ++ tailWord_582383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582383).length < 2 ^ (prefixWord ++ tailWord_582383).sum := by decide
  have hdescent : baseEnd_582383 < baseStart_582383 := by decide
  rcases family_descends (prefixWord ++ tailWord_582383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582389 : List Nat := [1, 3, 6, 1, 2, 1, 2, 4]
def baseStart_582389 : Nat := 118140960795 + 582389 * 2 ^ 59
def prefixEnd_582389 : Nat := 4983230072969 + 3 ^ 40 * 582389 * 2
def baseEnd_582389 : Nat := 88606069597459891573081

theorem tailTrace_582389 : CollatzResearch.WordTrace tailWord_582389 prefixEnd_582389 88606069597459891573081 := by
  unfold tailWord_582389
  simp only [CollatzResearch.WordTrace]
  refine ⟨21241471887111591967566221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14160981258074394645044147 21241471887111591967566221)
  ·
    refine ⟨7965551957666846987837333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21241471887111591967566221 7965551957666846987837333)
    ·
      refine ⟨373385248015633452554875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7965551957666846987837333 373385248015633452554875)
      ·
        refine ⟨560077872023450178832313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373385248015633452554875 560077872023450178832313)
        ·
          refine ⟨420058404017587634124235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560077872023450178832313 420058404017587634124235)
          ·
            refine ⟨630087606026381451186353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420058404017587634124235 630087606026381451186353)
            ·
              refine ⟨472565704519786088389765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630087606026381451186353 472565704519786088389765)
              ·
                refine ⟨88606069597459891573081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472565704519786088389765 88606069597459891573081)
                ·
                  rfl

theorem cell20_582389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].length) (baseStart_582389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582389 prefixEnd_582389 := by exact prefixLift 582389
  have htrace : WordTrace (prefixWord ++ tailWord_582389) baseStart_582389 baseEnd_582389 := by
    simpa [prefixWord, tailWord_582389, baseEnd_582389] using wordTrace_append hprefix tailTrace_582389
  have hstable : (prefixWord ++ tailWord_582389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582389).length < 2 ^ (prefixWord ++ tailWord_582389).sum := by decide
  have hdescent : baseEnd_582389 < baseStart_582389 := by decide
  rcases family_descends (prefixWord ++ tailWord_582389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582407 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 2]
def baseStart_582407 : Nat := 118140960795 + 582407 * 2 ^ 59
def prefixEnd_582407 : Nat := 4983230072969 + 3 ^ 40 * 582407 * 2
def baseEnd_582407 : Nat := 265826424482851612119169

theorem tailTrace_582407 : CollatzResearch.WordTrace tailWord_582407 prefixEnd_582407 265826424482851612119169 := by
  unfold tailWord_582407
  simp only [CollatzResearch.WordTrace]
  refine ⟨21242128401046381041721475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14161418934030920694480983 21242128401046381041721475)
  ·
    refine ⟨31863192601569571562582213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21242128401046381041721475 31863192601569571562582213)
    ·
      refine ⟨5974348612794294667984165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31863192601569571562582213 5974348612794294667984165)
      ·
        refine ⟨1120190364898930250247031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5974348612794294667984165 1120190364898930250247031)
        ·
          refine ⟨1680285547348395375370547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120190364898930250247031 1680285547348395375370547)
          ·
            refine ⟨2520428321022593063055821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680285547348395375370547 2520428321022593063055821)
            ·
              refine ⟨945160620383472398645933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520428321022593063055821 945160620383472398645933)
              ·
                refine ⟨354435232643802149492225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 945160620383472398645933 354435232643802149492225)
                ·
                  refine ⟨265826424482851612119169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354435232643802149492225 265826424482851612119169)
                  ·
                    rfl

theorem cell20_582407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 2].length) (baseStart_582407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582407 prefixEnd_582407 := by exact prefixLift 582407
  have htrace : WordTrace (prefixWord ++ tailWord_582407) baseStart_582407 baseEnd_582407 := by
    simpa [prefixWord, tailWord_582407, baseEnd_582407] using wordTrace_append hprefix tailTrace_582407
  have hstable : (prefixWord ++ tailWord_582407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582407).length < 2 ^ (prefixWord ++ tailWord_582407).sum := by decide
  have hdescent : baseEnd_582407 < baseStart_582407 := by decide
  rcases family_descends (prefixWord ++ tailWord_582407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582428 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_582428 : Nat := 118140960795 + 582428 * 2 ^ 59
def prefixEnd_582428 : Nat := 4983230072969 + 3 ^ 40 * 582428 * 2
def baseEnd_582428 : Nat := 265836009455068872419083

theorem tailTrace_582428 : CollatzResearch.WordTrace tailWord_582428 prefixEnd_582428 265836009455068872419083 := by
  unfold tailWord_582428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10621447166985150814117969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14161929555980201085490625 10621447166985150814117969)
  ·
    refine ⟨7966085375238863110588477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10621447166985150814117969 7966085375238863110588477)
    ·
      refine ⟨2987282015714573666470679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7966085375238863110588477 2987282015714573666470679)
      ·
        refine ⟨4480923023571860499706019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2987282015714573666470679 4480923023571860499706019)
        ·
          refine ⟨6721384535357790749559029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480923023571860499706019 6721384535357790749559029)
          ·
            refine ⟨630129800189792882771159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6721384535357790749559029 630129800189792882771159)
            ·
              refine ⟨945194700284689324156739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630129800189792882771159 945194700284689324156739)
              ·
                refine ⟨1417792050427033986235109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945194700284689324156739 1417792050427033986235109)
                ·
                  refine ⟨265836009455068872419083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417792050427033986235109 265836009455068872419083)
                  ·
                    rfl

theorem cell20_582428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_582428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582428 prefixEnd_582428 := by exact prefixLift 582428
  have htrace : WordTrace (prefixWord ++ tailWord_582428) baseStart_582428 baseEnd_582428 := by
    simpa [prefixWord, tailWord_582428, baseEnd_582428] using wordTrace_append hprefix tailTrace_582428
  have hstable : (prefixWord ++ tailWord_582428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582428).length < 2 ^ (prefixWord ++ tailWord_582428).sum := by decide
  have hdescent : baseEnd_582428 < baseStart_582428 := by decide
  rcases family_descends (prefixWord ++ tailWord_582428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582515 : List Nat := [1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_582515 : Nat := 118140960795 + 582515 * 2 ^ 59
def prefixEnd_582515 : Nat := 4983230072969 + 3 ^ 40 * 582515 * 2
def baseEnd_582515 : Nat := 88625239541894412172909

theorem tailTrace_582515 : CollatzResearch.WordTrace tailWord_582515 prefixEnd_582515 88625239541894412172909 := by
  unfold tailWord_582515
  simp only [CollatzResearch.WordTrace]
  refine ⟨21246067484655115486652999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14164044989770076991101999 21246067484655115486652999)
  ·
    refine ⟨31869101226982673229979499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21246067484655115486652999 31869101226982673229979499)
    ·
      refine ⟨47803651840474009844969249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31869101226982673229979499 47803651840474009844969249)
      ·
        refine ⟨35852738880355507383726937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47803651840474009844969249 35852738880355507383726937)
        ·
          refine ⟨26889554160266630537795203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35852738880355507383726937 26889554160266630537795203)
          ·
            refine ⟨40334331240399945806692805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26889554160266630537795203 40334331240399945806692805)
            ·
              refine ⟨7562687107574989838754901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40334331240399945806692805 7562687107574989838754901)
              ·
                refine ⟨88625239541894412172909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7562687107574989838754901 88625239541894412172909)
                ·
                  rfl

theorem cell20_582515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_582515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582515 prefixEnd_582515 := by exact prefixLift 582515
  have htrace : WordTrace (prefixWord ++ tailWord_582515) baseStart_582515 baseEnd_582515 := by
    simpa [prefixWord, tailWord_582515, baseEnd_582515] using wordTrace_append hprefix tailTrace_582515
  have hstable : (prefixWord ++ tailWord_582515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582515).length < 2 ^ (prefixWord ++ tailWord_582515).sum := by decide
  have hdescent : baseEnd_582515 < baseStart_582515 := by decide
  rcases family_descends (prefixWord ++ tailWord_582515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582535 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 3]
def baseStart_582535 : Nat := 118140960795 + 582535 * 2 ^ 59
def prefixEnd_582535 : Nat := 4983230072969 + 3 ^ 40 * 582535 * 2
def baseEnd_582535 : Nat := 265884847170652055851979

theorem tailTrace_582535 : CollatzResearch.WordTrace tailWord_582535 prefixEnd_582535 265884847170652055851979 := by
  unfold tailWord_582535
  simp only [CollatzResearch.WordTrace]
  refine ⟨21246796944582658902381059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14164531296388439268254039 21246796944582658902381059)
  ·
    refine ⟨31870195416873988353571589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21246796944582658902381059 31870195416873988353571589)
    ·
      refine ⟨5975661640663872816294673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31870195416873988353571589 5975661640663872816294673)
      ·
        refine ⟨4481746230497904612221005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5975661640663872816294673 4481746230497904612221005)
        ·
          refine ⟨1680654836436714229582877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4481746230497904612221005 1680654836436714229582877)
          ·
            refine ⟨630245563663767836093579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1680654836436714229582877 630245563663767836093579)
            ·
              refine ⟨945368345495651754140369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630245563663767836093579 945368345495651754140369)
              ·
                refine ⟨709026259121738815605277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945368345495651754140369 709026259121738815605277)
                ·
                  refine ⟨265884847170652055851979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709026259121738815605277 265884847170652055851979)
                  ·
                    rfl

theorem cell20_582535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_582535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582535 prefixEnd_582535 := by exact prefixLift 582535
  have htrace : WordTrace (prefixWord ++ tailWord_582535) baseStart_582535 baseEnd_582535 := by
    simpa [prefixWord, tailWord_582535, baseEnd_582535] using wordTrace_append hprefix tailTrace_582535
  have hstable : (prefixWord ++ tailWord_582535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582535).length < 2 ^ (prefixWord ++ tailWord_582535).sum := by decide
  have hdescent : baseEnd_582535 < baseStart_582535 := by decide
  rcases family_descends (prefixWord ++ tailWord_582535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582553 : List Nat := [1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_582553 : Nat := 118140960795 + 582553 * 2 ^ 59
def prefixEnd_582553 : Nat := 4983230072969 + 3 ^ 40 * 582553 * 2
def baseEnd_582553 : Nat := 88631020953707997750635

theorem tailTrace_582553 : CollatzResearch.WordTrace tailWord_582553 prefixEnd_582553 88631020953707997750635 := by
  unfold tailWord_582553
  simp only [CollatzResearch.WordTrace]
  refine ⟨21247453458517447976536313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14164968972344965317690875 21247453458517447976536313)
  ·
    refine ⟨15935590093888085982402235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21247453458517447976536313 15935590093888085982402235)
    ·
      refine ⟨23903385140832128973603353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15935590093888085982402235 23903385140832128973603353)
      ·
        refine ⟨17927538855624096730202515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23903385140832128973603353 17927538855624096730202515)
        ·
          refine ⟨26891308283436145095303773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17927538855624096730202515 26891308283436145095303773)
          ·
            refine ⟨10084240606288554410738915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26891308283436145095303773 10084240606288554410738915)
            ·
              refine ⟨15126360909432831616108373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10084240606288554410738915 15126360909432831616108373)
              ·
                refine ⟨88631020953707997750635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15126360909432831616108373 88631020953707997750635)
                ·
                  rfl

theorem cell20_582553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_582553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582553 prefixEnd_582553 := by exact prefixLift 582553
  have htrace : WordTrace (prefixWord ++ tailWord_582553) baseStart_582553 baseEnd_582553 := by
    simpa [prefixWord, tailWord_582553, baseEnd_582553] using wordTrace_append hprefix tailTrace_582553
  have hstable : (prefixWord ++ tailWord_582553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582553).length < 2 ^ (prefixWord ++ tailWord_582553).sum := by decide
  have hdescent : baseEnd_582553 < baseStart_582553 := by decide
  rcases family_descends (prefixWord ++ tailWord_582553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582644 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 2]
def baseStart_582644 : Nat := 118140960795 + 582644 * 2 ^ 59
def prefixEnd_582644 : Nat := 4983230072969 + 3 ^ 40 * 582644 * 2
def baseEnd_582644 : Nat := 265934597740732121218201

theorem tailTrace_582644 : CollatzResearch.WordTrace tailWord_582644 prefixEnd_582644 265934597740732121218201 := by
  unfold tailWord_582644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10625386250593885259049493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14167181667458513678732657 10625386250593885259049493)
  ·
    refine ⟨498064980496588371517945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10625386250593885259049493 498064980496588371517945)
    ·
      refine ⟨373548735372441278638459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498064980496588371517945 373548735372441278638459)
      ·
        refine ⟨560323103058661917957689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373548735372441278638459 560323103058661917957689)
        ·
          refine ⟨420242327293996438468267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560323103058661917957689 420242327293996438468267)
          ·
            refine ⟨630363490940994657702401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420242327293996438468267 630363490940994657702401)
            ·
              refine ⟨472772618205745993276801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630363490940994657702401 472772618205745993276801)
              ·
                refine ⟨354579463654309494957601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472772618205745993276801 354579463654309494957601)
                ·
                  refine ⟨265934597740732121218201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354579463654309494957601 265934597740732121218201)
                  ·
                    rfl

theorem cell20_582644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_582644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582644 prefixEnd_582644 := by exact prefixLift 582644
  have htrace : WordTrace (prefixWord ++ tailWord_582644) baseStart_582644 baseEnd_582644 := by
    simpa [prefixWord, tailWord_582644, baseEnd_582644] using wordTrace_append hprefix tailTrace_582644
  have hstable : (prefixWord ++ tailWord_582644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582644).length < 2 ^ (prefixWord ++ tailWord_582644).sum := by decide
  have hdescent : baseEnd_582644 < baseStart_582644 := by decide
  rcases family_descends (prefixWord ++ tailWord_582644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582646 : List Nat := [5, 1, 1, 1, 3, 9]
def baseStart_582646 : Nat := 118140960795 + 582646 * 2 ^ 59
def prefixEnd_582646 : Nat := 4983230072969 + 3 ^ 40 * 582646 * 2
def baseEnd_582646 : Nat := 9849463355378851968575

theorem tailTrace_582646 : CollatzResearch.WordTrace tailWord_582646 prefixEnd_582646 9849463355378851968575 := by
  unfold tailWord_582646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328177840448782803729487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14167230298120349906447861 1328177840448782803729487)
  ·
    refine ⟨1992266760673174205594231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1328177840448782803729487 1992266760673174205594231)
    ·
      refine ⟨2988400141009761308391347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1992266760673174205594231 2988400141009761308391347)
      ·
        refine ⟨4482600211514641962587021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988400141009761308391347 4482600211514641962587021)
        ·
          refine ⟨1680975079317990735970133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4482600211514641962587021 1680975079317990735970133)
          ·
            refine ⟨9849463355378851968575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1680975079317990735970133 9849463355378851968575)
            ·
              rfl

theorem cell20_582646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 9].length) (baseStart_582646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582646 prefixEnd_582646 := by exact prefixLift 582646
  have htrace : WordTrace (prefixWord ++ tailWord_582646) baseStart_582646 baseEnd_582646 := by
    simpa [prefixWord, tailWord_582646, baseEnd_582646] using wordTrace_append hprefix tailTrace_582646
  have hstable : (prefixWord ++ tailWord_582646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582646).length < 2 ^ (prefixWord ++ tailWord_582646).sum := by decide
  have hdescent : baseEnd_582646 < baseStart_582646 := by decide
  rcases family_descends (prefixWord ++ tailWord_582646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
