import V185TrunkScan22Chunk154

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1385218 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1385218 : Nat := 118140960795 + 1385218 * 2 ^ 59
def prefixEnd_1385218 : Nat := 4983230072969 + 3 ^ 40 * 1385218 * 2
def baseEnd_1385218 : Nat := 474188430173244374603003

theorem tailTrace_1385218 : CollatzResearch.WordTrace tailWord_1385218 prefixEnd_1385218 474188430173244374603003 := by
  unfold tailWord_1385218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12630762773899809311175077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33682034063732824829800205 12630762773899809311175077)
  ·
    refine ⟨2368268020106214245845327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12630762773899809311175077 2368268020106214245845327)
    ·
      refine ⟨3552402030159321368767991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368268020106214245845327 3552402030159321368767991)
      ·
        refine ⟨5328603045238982053151987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552402030159321368767991 5328603045238982053151987)
        ·
          refine ⟨7992904567858473079727981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328603045238982053151987 7992904567858473079727981)
          ·
            refine ⟨2997339212946927404897993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7992904567858473079727981 2997339212946927404897993)
            ·
              refine ⟨2248004409710195553673495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2997339212946927404897993 2248004409710195553673495)
              ·
                refine ⟨3372006614565293330510243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248004409710195553673495 3372006614565293330510243)
                ·
                  refine ⟨5058009921847939995765365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372006614565293330510243 5058009921847939995765365)
                  ·
                    refine ⟨474188430173244374603003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5058009921847939995765365 474188430173244374603003)
                    ·
                      rfl

theorem cell22_1385218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1385218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385218 prefixEnd_1385218 := by exact prefixLift 1385218
  have htrace : WordTrace (prefixWord ++ tailWord_1385218) baseStart_1385218 baseEnd_1385218 := by
    simpa [prefixWord, tailWord_1385218, baseEnd_1385218] using wordTrace_append hprefix tailTrace_1385218
  have hstable : (prefixWord ++ tailWord_1385218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385218).length < 2 ^ (prefixWord ++ tailWord_1385218).sum := by decide
  have hdescent : baseEnd_1385218 < baseStart_1385218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385252 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_1385252 : Nat := 118140960795 + 1385252 * 2 ^ 59
def prefixEnd_1385252 : Nat := 4983230072969 + 3 ^ 40 * 1385252 * 2
def baseEnd_1385252 : Nat := 474200069068079619252899

theorem tailTrace_1385252 : CollatzResearch.WordTrace tailWord_1385252 prefixEnd_1385252 474200069068079619252899 := by
  unfold tailWord_1385252
  simp only [CollatzResearch.WordTrace]
  refine ⟨25262145588738030525719005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33682860784984040700958673 25262145588738030525719005)
  ·
    refine ⟨9473304595776761447144627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25262145588738030525719005 9473304595776761447144627)
    ·
      refine ⟨14209956893665142170716941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9473304595776761447144627 14209956893665142170716941)
      ·
        refine ⟨5328733835124428314018853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14209956893665142170716941 5328733835124428314018853)
        ·
          refine ⟨999137594085830308878535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5328733835124428314018853 999137594085830308878535)
          ·
            refine ⟨1498706391128745463317803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999137594085830308878535 1498706391128745463317803)
            ·
              refine ⟨2248059586693118194976705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498706391128745463317803 2248059586693118194976705)
              ·
                refine ⟨1686044690019838646232529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248059586693118194976705 1686044690019838646232529)
                ·
                  refine ⟨1264533517514878984674397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686044690019838646232529 1264533517514878984674397)
                  ·
                    refine ⟨474200069068079619252899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264533517514878984674397 474200069068079619252899)
                    ·
                      rfl

theorem cell22_1385252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_1385252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385252 prefixEnd_1385252 := by exact prefixLift 1385252
  have htrace : WordTrace (prefixWord ++ tailWord_1385252) baseStart_1385252 baseEnd_1385252 := by
    simpa [prefixWord, tailWord_1385252, baseEnd_1385252] using wordTrace_append hprefix tailTrace_1385252
  have hstable : (prefixWord ++ tailWord_1385252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385252).length < 2 ^ (prefixWord ++ tailWord_1385252).sum := by decide
  have hdescent : baseEnd_1385252 < baseStart_1385252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385297 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 1, 3]
def baseStart_1385297 : Nat := 118140960795 + 1385297 * 2 ^ 59
def prefixEnd_1385297 : Nat := 4983230072969 + 3 ^ 40 * 1385297 * 2
def baseEnd_1385297 : Nat := 474215473487714501877761

theorem tailTrace_1385297 : CollatzResearch.WordTrace tailWord_1385297 prefixEnd_1385297 474215473487714501877761 := by
  unfold tailWord_1385297
  simp only [CollatzResearch.WordTrace]
  refine ⟨50525932462313033736826145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33683954974875355824550763 50525932462313033736826145)
  ·
    refine ⟨37894449346734775302619609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50525932462313033736826145 37894449346734775302619609)
    ·
      refine ⟨28420837010051081476964707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37894449346734775302619609 28420837010051081476964707)
      ·
        refine ⟨42631255515076622215447061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28420837010051081476964707 42631255515076622215447061)
        ·
          refine ⟨1998340102269216666349081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42631255515076622215447061 1998340102269216666349081)
          ·
            refine ⟨1498755076701912499761811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998340102269216666349081 1498755076701912499761811)
            ·
              refine ⟨2248132615052868749642717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498755076701912499761811 2248132615052868749642717)
              ·
                refine ⟨843049730644825781116019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2248132615052868749642717 843049730644825781116019)
                ·
                  refine ⟨1264574595967238671674029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843049730644825781116019 1264574595967238671674029)
                  ·
                    refine ⟨474215473487714501877761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264574595967238671674029 474215473487714501877761)
                    ·
                      rfl

theorem cell22_1385297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_1385297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385297 prefixEnd_1385297 := by exact prefixLift 1385297
  have htrace : WordTrace (prefixWord ++ tailWord_1385297) baseStart_1385297 baseEnd_1385297 := by
    simpa [prefixWord, tailWord_1385297, baseEnd_1385297] using wordTrace_append hprefix tailTrace_1385297
  have hstable : (prefixWord ++ tailWord_1385297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385297).length < 2 ^ (prefixWord ++ tailWord_1385297).sum := by decide
  have hdescent : baseEnd_1385297 < baseStart_1385297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385304 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_1385304 : Nat := 118140960795 + 1385304 * 2 ^ 59
def prefixEnd_1385304 : Nat := 4983230072969 + 3 ^ 40 * 1385304 * 2
def baseEnd_1385304 : Nat := 158072623243589605650913

theorem tailTrace_1385304 : CollatzResearch.WordTrace tailWord_1385304 prefixEnd_1385304 158072623243589605650913 := by
  unfold tailWord_1385304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25263093886643836966165483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33684125182191782621553977 25263093886643836966165483)
  ·
    refine ⟨37894640829965755449248225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25263093886643836966165483 37894640829965755449248225)
    ·
      refine ⟨28420980622474316586936169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37894640829965755449248225 28420980622474316586936169)
      ·
        refine ⟨21315735466855737440202127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28420980622474316586936169 21315735466855737440202127)
        ·
          refine ⟨31973603200283606160303191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21315735466855737440202127 31973603200283606160303191)
          ·
            refine ⟨47960404800425409240454787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31973603200283606160303191 47960404800425409240454787)
            ·
              refine ⟨71940607200638113860682181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47960404800425409240454787 71940607200638113860682181)
              ·
                refine ⟨13488863850119646348877909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71940607200638113860682181 13488863850119646348877909)
                ·
                  refine ⟨158072623243589605650913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13488863850119646348877909 158072623243589605650913)
                  ·
                    rfl

theorem cell22_1385304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_1385304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385304 prefixEnd_1385304 := by exact prefixLift 1385304
  have htrace : WordTrace (prefixWord ++ tailWord_1385304) baseStart_1385304 baseEnd_1385304 := by
    simpa [prefixWord, tailWord_1385304, baseEnd_1385304] using wordTrace_append hprefix tailTrace_1385304
  have hstable : (prefixWord ++ tailWord_1385304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385304).length < 2 ^ (prefixWord ++ tailWord_1385304).sum := by decide
  have hdescent : baseEnd_1385304 < baseStart_1385304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385314 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1385314 : Nat := 118140960795 + 1385314 * 2 ^ 59
def prefixEnd_1385314 : Nat := 4983230072969 + 3 ^ 40 * 1385314 * 2
def baseEnd_1385314 : Nat := 474221292935132124202709

theorem tailTrace_1385314 : CollatzResearch.WordTrace tailWord_1385314 prefixEnd_1385314 474221292935132124202709 := by
  unfold tailWord_1385314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12631638125812861410048749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33684368335500963760129997 12631638125812861410048749)
  ·
    refine ⟨4736864297179823028768281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12631638125812861410048749 4736864297179823028768281)
    ·
      refine ⟨3552648222884867271576211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4736864297179823028768281 3552648222884867271576211)
      ·
        refine ⟨5328972334327300907364317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552648222884867271576211 5328972334327300907364317)
        ·
          refine ⟨1998364625372737840261619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5328972334327300907364317 1998364625372737840261619)
          ·
            refine ⟨2997546938059106760392429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998364625372737840261619 2997546938059106760392429)
            ·
              refine ⟨1124080101772165035147161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2997546938059106760392429 1124080101772165035147161)
              ·
                refine ⟨843060076329123776360371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124080101772165035147161 843060076329123776360371)
                ·
                  refine ⟨1264590114493685664540557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843060076329123776360371 1264590114493685664540557)
                  ·
                    refine ⟨474221292935132124202709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264590114493685664540557 474221292935132124202709)
                    ·
                      rfl

theorem cell22_1385314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1385314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385314 prefixEnd_1385314 := by exact prefixLift 1385314
  have htrace : WordTrace (prefixWord ++ tailWord_1385314) baseStart_1385314 baseEnd_1385314 := by
    simpa [prefixWord, tailWord_1385314, baseEnd_1385314] using wordTrace_append hprefix tailTrace_1385314
  have hstable : (prefixWord ++ tailWord_1385314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385314).length < 2 ^ (prefixWord ++ tailWord_1385314).sum := by decide
  have hdescent : baseEnd_1385314 < baseStart_1385314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385336 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1385336 : Nat := 118140960795 + 1385336 * 2 ^ 59
def prefixEnd_1385336 : Nat := 4983230072969 + 3 ^ 40 * 1385336 * 2
def baseEnd_1385336 : Nat := 474228823984731400152641

theorem tailTrace_1385336 : CollatzResearch.WordTrace tailWord_1385336 prefixEnd_1385336 474228823984731400152641 := by
  unfold tailWord_1385336
  simp only [CollatzResearch.WordTrace]
  refine ⟨25263677454585871698747931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33684903272781162264997241 25263677454585871698747931)
  ·
    refine ⟨37895516181878807548121897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25263677454585871698747931 37895516181878807548121897)
    ·
      refine ⟨28421637136409105661091423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37895516181878807548121897 28421637136409105661091423)
      ·
        refine ⟨42632455704613658491637135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28421637136409105661091423 42632455704613658491637135)
        ·
          refine ⟨63948683556920487737455703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42632455704613658491637135 63948683556920487737455703)
          ·
            refine ⟨95923025335380731606183555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63948683556920487737455703 95923025335380731606183555)
            ·
              refine ⟨143884538003071097409275333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95923025335380731606183555 143884538003071097409275333)
              ·
                refine ⟨26978350875575830764239125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143884538003071097409275333 26978350875575830764239125)
                ·
                  refine ⟨1264610197292617067073709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26978350875575830764239125 1264610197292617067073709)
                  ·
                    refine ⟨474228823984731400152641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264610197292617067073709 474228823984731400152641)
                    ·
                      rfl

theorem cell22_1385336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1385336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385336 prefixEnd_1385336 := by exact prefixLift 1385336
  have htrace : WordTrace (prefixWord ++ tailWord_1385336) baseStart_1385336 baseEnd_1385336 := by
    simpa [prefixWord, tailWord_1385336, baseEnd_1385336] using wordTrace_append hprefix tailTrace_1385336
  have hstable : (prefixWord ++ tailWord_1385336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385336).length < 2 ^ (prefixWord ++ tailWord_1385336).sum := by decide
  have hdescent : baseEnd_1385336 < baseStart_1385336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385415 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 1, 3]
def baseStart_1385415 : Nat := 118140960795 + 1385415 * 2 ^ 59
def prefixEnd_1385415 : Nat := 4983230072969 + 3 ^ 40 * 1385415 * 2
def baseEnd_1385415 : Nat := 474255867299201527427399

theorem tailTrace_1385415 : CollatzResearch.WordTrace tailWord_1385415 prefixEnd_1385415 474255867299201527427399 := by
  unfold tailWord_1385415
  simp only [CollatzResearch.WordTrace]
  refine ⟨50530236275885539889621699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33686824183923693259747799 50530236275885539889621699)
  ·
    refine ⟨75795354413828309834432549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50530236275885539889621699 75795354413828309834432549)
    ·
      refine ⟨14211628952592808093956103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75795354413828309834432549 14211628952592808093956103)
      ·
        refine ⟨21317443428889212140934155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14211628952592808093956103 21317443428889212140934155)
        ·
          refine ⟨31976165143333818211401233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21317443428889212140934155 31976165143333818211401233)
          ·
            refine ⟨23982123857500363658550925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31976165143333818211401233 23982123857500363658550925)
            ·
              refine ⟨8993296446562636371956597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23982123857500363658550925 8993296446562636371956597)
              ·
                refine ⟨843121541865247159870931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8993296446562636371956597 843121541865247159870931)
                ·
                  refine ⟨1264682312797870739806397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843121541865247159870931 1264682312797870739806397)
                  ·
                    refine ⟨474255867299201527427399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264682312797870739806397 474255867299201527427399)
                    ·
                      rfl

theorem cell22_1385415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_1385415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385415 prefixEnd_1385415 := by exact prefixLift 1385415
  have htrace : WordTrace (prefixWord ++ tailWord_1385415) baseStart_1385415 baseEnd_1385415 := by
    simpa [prefixWord, tailWord_1385415, baseEnd_1385415] using wordTrace_append hprefix tailTrace_1385415
  have hstable : (prefixWord ++ tailWord_1385415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385415).length < 2 ^ (prefixWord ++ tailWord_1385415).sum := by decide
  have hdescent : baseEnd_1385415 < baseStart_1385415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385428 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1385428 : Nat := 118140960795 + 1385428 * 2 ^ 59
def prefixEnd_1385428 : Nat := 4983230072969 + 3 ^ 40 * 1385428 * 2
def baseEnd_1385428 : Nat := 158086772488291275617453

theorem tailTrace_1385428 : CollatzResearch.WordTrace tailWord_1385428 prefixEnd_1385428 158086772488291275617453 := by
  unfold tailWord_1385428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265355212419221554922469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33687140283225628739896625 25265355212419221554922469)
  ·
    refine ⟨4737254102328604041547963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25265355212419221554922469 4737254102328604041547963)
    ·
      refine ⟨7105881153492906062321945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4737254102328604041547963 7105881153492906062321945)
      ·
        refine ⟨5329410865119679546741459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7105881153492906062321945 5329410865119679546741459)
        ·
          refine ⟨7994116297679519320112189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329410865119679546741459 7994116297679519320112189)
          ·
            refine ⟨2997793611629819745042071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7994116297679519320112189 2997793611629819745042071)
            ·
              refine ⟨4496690417444729617563107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997793611629819745042071 4496690417444729617563107)
              ·
                refine ⟨6745035626167094426344661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496690417444729617563107 6745035626167094426344661)
                ·
                  refine ⟨158086772488291275617453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6745035626167094426344661 158086772488291275617453)
                  ·
                    rfl

theorem cell22_1385428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1385428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385428 prefixEnd_1385428 := by exact prefixLift 1385428
  have htrace : WordTrace (prefixWord ++ tailWord_1385428) baseStart_1385428 baseEnd_1385428 := by
    simpa [prefixWord, tailWord_1385428, baseEnd_1385428] using wordTrace_append hprefix tailTrace_1385428
  have hstable : (prefixWord ++ tailWord_1385428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385428).length < 2 ^ (prefixWord ++ tailWord_1385428).sum := by decide
  have hdescent : baseEnd_1385428 < baseStart_1385428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385518 : List Nat := [4, 1, 3, 1, 1, 1, 1, 10]
def baseStart_1385518 : Nat := 118140960795 + 1385518 * 2 ^ 59
def prefixEnd_1385518 : Nat := 4983230072969 + 3 ^ 40 * 1385518 * 2
def baseEnd_1385518 : Nat := 52699014033793732455787

theorem tailTrace_1385518 : CollatzResearch.WordTrace tailWord_1385518 prefixEnd_1385518 52699014033793732455787 := by
  unfold tailWord_1385518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316749124314048560077651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33689328663008258987080805 6316749124314048560077651)
  ·
    refine ⟨9475123686471072840116477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316749124314048560077651 9475123686471072840116477)
    ·
      refine ⟨3553171382426652315043679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9475123686471072840116477 3553171382426652315043679)
      ·
        refine ⟨5329757073639978472565519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553171382426652315043679 5329757073639978472565519)
        ·
          refine ⟨7994635610459967708848279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329757073639978472565519 7994635610459967708848279)
          ·
            refine ⟨11991953415689951563272419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7994635610459967708848279 11991953415689951563272419)
            ·
              refine ⟨17987930123534927344908629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11991953415689951563272419 17987930123534927344908629)
              ·
                refine ⟨52699014033793732455787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17987930123534927344908629 52699014033793732455787)
                ·
                  rfl

theorem cell22_1385518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_1385518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385518 prefixEnd_1385518 := by exact prefixLift 1385518
  have htrace : WordTrace (prefixWord ++ tailWord_1385518) baseStart_1385518 baseEnd_1385518 := by
    simpa [prefixWord, tailWord_1385518, baseEnd_1385518] using wordTrace_append hprefix tailTrace_1385518
  have hstable : (prefixWord ++ tailWord_1385518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385518).length < 2 ^ (prefixWord ++ tailWord_1385518).sum := by decide
  have hdescent : baseEnd_1385518 < baseStart_1385518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385531 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_1385531 : Nat := 118140960795 + 1385531 * 2 ^ 59
def prefixEnd_1385531 : Nat := 4983230072969 + 3 ^ 40 * 1385531 * 2
def baseEnd_1385531 : Nat := 474295576469815891527043

theorem tailTrace_1385531 : CollatzResearch.WordTrace tailWord_1385531 prefixEnd_1385531 474295576469815891527043 := by
  unfold tailWord_1385531
  simp only [CollatzResearch.WordTrace]
  refine ⟨50534467143465291700844447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33689644762310194467229631 50534467143465291700844447)
  ·
    refine ⟨75801700715197937551266671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50534467143465291700844447 75801700715197937551266671)
    ·
      refine ⟨113702551072796906326900007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75801700715197937551266671 113702551072796906326900007)
      ·
        refine ⟨170553826609195359490350011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113702551072796906326900007 170553826609195359490350011)
        ·
          refine ⟨255830739913793039235525017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170553826609195359490350011 255830739913793039235525017)
          ·
            refine ⟨191873054935344779426643763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255830739913793039235525017 191873054935344779426643763)
            ·
              refine ⟨287809582403017169139965645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191873054935344779426643763 287809582403017169139965645)
              ·
                refine ⟨107928593401131438427487117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287809582403017169139965645 107928593401131438427487117)
                ·
                  refine ⟨40473222525424289410307669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107928593401131438427487117 40473222525424289410307669)
                  ·
                    refine ⟨474295576469815891527043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40473222525424289410307669 474295576469815891527043)
                    ·
                      rfl

theorem cell22_1385531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_1385531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385531 prefixEnd_1385531 := by exact prefixLift 1385531
  have htrace : WordTrace (prefixWord ++ tailWord_1385531) baseStart_1385531 baseEnd_1385531 := by
    simpa [prefixWord, tailWord_1385531, baseEnd_1385531] using wordTrace_append hprefix tailTrace_1385531
  have hstable : (prefixWord ++ tailWord_1385531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385531).length < 2 ^ (prefixWord ++ tailWord_1385531).sum := by decide
  have hdescent : baseEnd_1385531 < baseStart_1385531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385550 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_1385550 : Nat := 118140960795 + 1385550 * 2 ^ 59
def prefixEnd_1385550 : Nat := 4983230072969 + 3 ^ 40 * 1385550 * 2
def baseEnd_1385550 : Nat := 474302080558106175301985

theorem tailTrace_1385550 : CollatzResearch.WordTrace tailWord_1385550 prefixEnd_1385550 474302080558106175301985 := by
  unfold tailWord_1385550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316895016299557243223263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33690106753597638630524069 6316895016299557243223263)
  ·
    refine ⟨9475342524449335864834895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316895016299557243223263 9475342524449335864834895)
    ·
      refine ⟨14213013786674003797252343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9475342524449335864834895 14213013786674003797252343)
      ·
        refine ⟨21319520680011005695878515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14213013786674003797252343 21319520680011005695878515)
        ·
          refine ⟨31979281020016508543817773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21319520680011005695878515 31979281020016508543817773)
          ·
            refine ⟨11992230382506190703931665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31979281020016508543817773 11992230382506190703931665)
            ·
              refine ⟨8994172786879643027948749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11992230382506190703931665 8994172786879643027948749)
              ·
                refine ⟨3372814795079866135480781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8994172786879643027948749 3372814795079866135480781)
                ·
                  refine ⟨1264805548154949800805293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3372814795079866135480781 1264805548154949800805293)
                  ·
                    refine ⟨474302080558106175301985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264805548154949800805293 474302080558106175301985)
                    ·
                      rfl

theorem cell22_1385550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_1385550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385550 prefixEnd_1385550 := by exact prefixLift 1385550
  have htrace : WordTrace (prefixWord ++ tailWord_1385550) baseStart_1385550 baseEnd_1385550 := by
    simpa [prefixWord, tailWord_1385550, baseEnd_1385550] using wordTrace_append hprefix tailTrace_1385550
  have hstable : (prefixWord ++ tailWord_1385550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385550).length < 2 ^ (prefixWord ++ tailWord_1385550).sum := by decide
  have hdescent : baseEnd_1385550 < baseStart_1385550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385655 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 2, 4]
def baseStart_1385655 : Nat := 118140960795 + 1385655 * 2 ^ 59
def prefixEnd_1385655 : Nat := 4983230072969 + 3 ^ 40 * 1385655 * 2
def baseEnd_1385655 : Nat := 474338024203920901426663

theorem tailTrace_1385655 : CollatzResearch.WordTrace tailWord_1385655 prefixEnd_1385655 474338024203920901426663 := by
  unfold tailWord_1385655
  simp only [CollatzResearch.WordTrace]
  refine ⟨50538989795016060878358419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33692659863344040585572279 50538989795016060878358419)
  ·
    refine ⟨75808484692524091317537629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50538989795016060878358419 75808484692524091317537629)
    ·
      refine ⟨28428181759696534244076611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75808484692524091317537629 28428181759696534244076611)
      ·
        refine ⟨42642272639544801366114917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28428181759696534244076611 42642272639544801366114917)
        ·
          refine ⟨7995426119914650256146547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42642272639544801366114917 7995426119914650256146547)
          ·
            refine ⟨11993139179871975384219821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995426119914650256146547 11993139179871975384219821)
            ·
              refine ⟨4497427192451990769082433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11993139179871975384219821 4497427192451990769082433)
              ·
                refine ⟨3373070394338993076811825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4497427192451990769082433 3373070394338993076811825)
                ·
                  refine ⟨2529802795754244807608869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3373070394338993076811825 2529802795754244807608869)
                  ·
                    refine ⟨474338024203920901426663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529802795754244807608869 474338024203920901426663)
                    ·
                      rfl

theorem cell22_1385655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_1385655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385655 prefixEnd_1385655 := by exact prefixLift 1385655
  have htrace : WordTrace (prefixWord ++ tailWord_1385655) baseStart_1385655 baseEnd_1385655 := by
    simpa [prefixWord, tailWord_1385655, baseEnd_1385655] using wordTrace_append hprefix tailTrace_1385655
  have hstable : (prefixWord ++ tailWord_1385655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385655).length < 2 ^ (prefixWord ++ tailWord_1385655).sum := by decide
  have hdescent : baseEnd_1385655 < baseStart_1385655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385674 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_1385674 : Nat := 118140960795 + 1385674 * 2 ^ 59
def prefixEnd_1385674 : Nat := 4983230072969 + 3 ^ 40 * 1385674 * 2
def baseEnd_1385674 : Nat := 474344528292211185201605

theorem tailTrace_1385674 : CollatzResearch.WordTrace tailWord_1385674 prefixEnd_1385674 474344528292211185201605 := by
  unfold tailWord_1385674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12634920695486806780825019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33693121854631484748866717 12634920695486806780825019)
  ·
    refine ⟨18952381043230210171237529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12634920695486806780825019 18952381043230210171237529)
    ·
      refine ⟨14214285782422657628428147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18952381043230210171237529 14214285782422657628428147)
      ·
        refine ⟨21321428673633986442642221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14214285782422657628428147 21321428673633986442642221)
        ·
          refine ⟨7995535752612744915990833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21321428673633986442642221 7995535752612744915990833)
          ·
            refine ⟨5996651814459558686993125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7995535752612744915990833 5996651814459558686993125)
            ·
              refine ⟨1124372215211167253811211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5996651814459558686993125 1124372215211167253811211)
              ·
                refine ⟨1686558322816750880716817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124372215211167253811211 1686558322816750880716817)
                ·
                  refine ⟨1264918742112563160537613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686558322816750880716817 1264918742112563160537613)
                  ·
                    refine ⟨474344528292211185201605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264918742112563160537613 474344528292211185201605)
                    ·
                      rfl

theorem cell22_1385674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_1385674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385674 prefixEnd_1385674 := by exact prefixLift 1385674
  have htrace : WordTrace (prefixWord ++ tailWord_1385674) baseStart_1385674 baseEnd_1385674 := by
    simpa [prefixWord, tailWord_1385674, baseEnd_1385674] using wordTrace_append hprefix tailTrace_1385674
  have hstable : (prefixWord ++ tailWord_1385674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385674).length < 2 ^ (prefixWord ++ tailWord_1385674).sum := by decide
  have hdescent : baseEnd_1385674 < baseStart_1385674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385683 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_1385683 : Nat := 118140960795 + 1385683 * 2 ^ 59
def prefixEnd_1385683 : Nat := 4983230072969 + 3 ^ 40 * 1385683 * 2
def baseEnd_1385683 : Nat := 474347609176138161726577

theorem tailTrace_1385683 : CollatzResearch.WordTrace tailWord_1385683 prefixEnd_1385683 474347609176138161726577 := by
  unfold tailWord_1385683
  simp only [CollatzResearch.WordTrace]
  refine ⟨50540011038914621660377703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33693340692609747773585135 50540011038914621660377703)
  ·
    refine ⟨75810016558371932490566555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50540011038914621660377703 75810016558371932490566555)
    ·
      refine ⟨113715024837557898735849833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75810016558371932490566555 113715024837557898735849833)
      ·
        refine ⟨85286268628168424051887375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113715024837557898735849833 85286268628168424051887375)
        ·
          refine ⟨127929402942252636077831063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85286268628168424051887375 127929402942252636077831063)
          ·
            refine ⟨191894104413378954116746595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127929402942252636077831063 191894104413378954116746595)
            ·
              refine ⟨287841156620068431175119893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191894104413378954116746595 287841156620068431175119893)
              ·
                refine ⟨13492554216565707711333745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 287841156620068431175119893 13492554216565707711333745)
                ·
                  refine ⟨10119415662424280783500309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13492554216565707711333745 10119415662424280783500309)
                  ·
                    refine ⟨474347609176138161726577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10119415662424280783500309 474347609176138161726577)
                    ·
                      rfl

theorem cell22_1385683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_1385683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385683 prefixEnd_1385683 := by exact prefixLift 1385683
  have htrace : WordTrace (prefixWord ++ tailWord_1385683) baseStart_1385683 baseEnd_1385683 := by
    simpa [prefixWord, tailWord_1385683, baseEnd_1385683] using wordTrace_append hprefix tailTrace_1385683
  have hstable : (prefixWord ++ tailWord_1385683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385683).length < 2 ^ (prefixWord ++ tailWord_1385683).sum := by decide
  have hdescent : baseEnd_1385683 < baseStart_1385683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385715 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 5]
def baseStart_1385715 : Nat := 118140960795 + 1385715 * 2 ^ 59
def prefixEnd_1385715 : Nat := 4983230072969 + 3 ^ 40 * 1385715 * 2
def baseEnd_1385715 : Nat := 158119521143366914975493

theorem tailTrace_1385715 : CollatzResearch.WordTrace tailWord_1385715 prefixEnd_1385715 158119521143366914975493 := by
  unfold tailWord_1385715
  simp only [CollatzResearch.WordTrace]
  refine ⟨50541178174798691125542599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33694118783199127417028399 50541178174798691125542599)
  ·
    refine ⟨75811767262198036688313899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50541178174798691125542599 75811767262198036688313899)
    ·
      refine ⟨113717650893297055032470849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75811767262198036688313899 113717650893297055032470849)
      ·
        refine ⟨85288238169972791274353137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113717650893297055032470849 85288238169972791274353137)
        ·
          refine ⟨63966178627479593455764853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85288238169972791274353137 63966178627479593455764853)
          ·
            refine ⟨5996829246326211886477955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63966178627479593455764853 5996829246326211886477955)
            ·
              refine ⟨8995243869489317829716933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996829246326211886477955 8995243869489317829716933)
              ·
                refine ⟨1686608225529247093071925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8995243869489317829716933 1686608225529247093071925)
                ·
                  refine ⟨158119521143366914975493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1686608225529247093071925 158119521143366914975493)
                  ·
                    rfl

theorem cell22_1385715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 5].length) (baseStart_1385715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385715 prefixEnd_1385715 := by exact prefixLift 1385715
  have htrace : WordTrace (prefixWord ++ tailWord_1385715) baseStart_1385715 baseEnd_1385715 := by
    simpa [prefixWord, tailWord_1385715, baseEnd_1385715] using wordTrace_append hprefix tailTrace_1385715
  have hstable : (prefixWord ++ tailWord_1385715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385715).length < 2 ^ (prefixWord ++ tailWord_1385715).sum := by decide
  have hdescent : baseEnd_1385715 < baseStart_1385715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385732 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1385732 : Nat := 118140960795 + 1385732 * 2 ^ 59
def prefixEnd_1385732 : Nat := 4983230072969 + 3 ^ 40 * 1385732 * 2
def baseEnd_1385732 : Nat := 158121460959172789083809

theorem tailTrace_1385732 : CollatzResearch.WordTrace tailWord_1385732 prefixEnd_1385732 158121460959172789083809 := by
  unfold tailWord_1385732
  simp only [CollatzResearch.WordTrace]
  refine ⟨25270899107868551514455725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33694532143824735352607633 25270899107868551514455725)
  ·
    refine ⟨9476587165450706817920897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25270899107868551514455725 9476587165450706817920897)
    ·
      refine ⟨7107440374088030113440673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9476587165450706817920897 7107440374088030113440673)
      ·
        refine ⟨5330580280566022585080505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7107440374088030113440673 5330580280566022585080505)
        ·
          refine ⟨3997935210424516938810379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5330580280566022585080505 3997935210424516938810379)
          ·
            refine ⟨5996902815636775408215569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997935210424516938810379 5996902815636775408215569)
            ·
              refine ⟨4497677111727581556161677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5996902815636775408215569 4497677111727581556161677)
              ·
                refine ⟨1686628916897843083560629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4497677111727581556161677 1686628916897843083560629)
                ·
                  refine ⟨158121460959172789083809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1686628916897843083560629 158121460959172789083809)
                  ·
                    rfl

theorem cell22_1385732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1385732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385732 prefixEnd_1385732 := by exact prefixLift 1385732
  have htrace : WordTrace (prefixWord ++ tailWord_1385732) baseStart_1385732 baseEnd_1385732 := by
    simpa [prefixWord, tailWord_1385732, baseEnd_1385732] using wordTrace_append hprefix tailTrace_1385732
  have hstable : (prefixWord ++ tailWord_1385732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385732).length < 2 ^ (prefixWord ++ tailWord_1385732).sum := by decide
  have hdescent : baseEnd_1385732 < baseStart_1385732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385745 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_1385745 : Nat := 118140960795 + 1385745 * 2 ^ 59
def prefixEnd_1385745 : Nat := 4983230072969 + 3 ^ 40 * 1385745 * 2
def baseEnd_1385745 : Nat := 474368833043190666676387

theorem tailTrace_1385745 : CollatzResearch.WordTrace tailWord_1385745 prefixEnd_1385745 474368833043190666676387 := by
  unfold tailWord_1385745
  simp only [CollatzResearch.WordTrace]
  refine ⟨50542272364690006249134689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33694848243126670832756459 50542272364690006249134689)
  ·
    refine ⟨37906704273517504686851017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50542272364690006249134689 37906704273517504686851017)
    ·
      refine ⟨28430028205138128515138263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37906704273517504686851017 28430028205138128515138263)
      ·
        refine ⟨42645042307707192772707395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28430028205138128515138263 42645042307707192772707395)
        ·
          refine ⟨63967563461560789159061093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42645042307707192772707395 63967563461560789159061093)
          ·
            refine ⟨11993918149042647967323955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63967563461560789159061093 11993918149042647967323955)
            ·
              refine ⟨17990877223563971950985933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11993918149042647967323955 17990877223563971950985933)
              ·
                refine ⟨6746578958836489481619725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17990877223563971950985933 6746578958836489481619725)
                ·
                  refine ⟨2529967109563683555607397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6746578958836489481619725 2529967109563683555607397)
                  ·
                    refine ⟨474368833043190666676387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529967109563683555607397 474368833043190666676387)
                    ·
                      rfl

theorem cell22_1385745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_1385745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385745 prefixEnd_1385745 := by exact prefixLift 1385745
  have htrace : WordTrace (prefixWord ++ tailWord_1385745) baseStart_1385745 baseEnd_1385745 := by
    simpa [prefixWord, tailWord_1385745, baseEnd_1385745] using wordTrace_append hprefix tailTrace_1385745
  have hstable : (prefixWord ++ tailWord_1385745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385745).length < 2 ^ (prefixWord ++ tailWord_1385745).sum := by decide
  have hdescent : baseEnd_1385745 < baseStart_1385745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385777 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 6]
def baseStart_1385777 : Nat := 118140960795 + 1385777 * 2 ^ 59
def prefixEnd_1385777 : Nat := 4983230072969 + 3 ^ 40 * 1385777 * 2
def baseEnd_1385777 : Nat := 158126595765717749958763

theorem tailTrace_1385777 : CollatzResearch.WordTrace tailWord_1385777 prefixEnd_1385777 158126595765717749958763 := by
  unfold tailWord_1385777
  simp only [CollatzResearch.WordTrace]
  refine ⟨50543439500574075714299585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33695626333716050476199723 50543439500574075714299585)
  ·
    refine ⟨37907579625430556785724689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50543439500574075714299585 37907579625430556785724689)
    ·
      refine ⟨28430684719072917589293517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37907579625430556785724689 28430684719072917589293517)
      ·
        refine ⟨10661506769652344095985069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28430684719072917589293517 10661506769652344095985069)
        ·
          refine ⟨3998065038619629035994401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10661506769652344095985069 3998065038619629035994401)
          ·
            refine ⟨2998548778964721776995801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998065038619629035994401 2998548778964721776995801)
            ·
              refine ⟨2248911584223541332746851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998548778964721776995801 2248911584223541332746851)
              ·
                refine ⟨3373367376335311999120277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248911584223541332746851 3373367376335311999120277)
                ·
                  refine ⟨158126595765717749958763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3373367376335311999120277 158126595765717749958763)
                  ·
                    rfl

theorem cell22_1385777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_1385777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385777 prefixEnd_1385777 := by exact prefixLift 1385777
  have htrace : WordTrace (prefixWord ++ tailWord_1385777) baseStart_1385777 baseEnd_1385777 := by
    simpa [prefixWord, tailWord_1385777, baseEnd_1385777] using wordTrace_append hprefix tailTrace_1385777
  have hstable : (prefixWord ++ tailWord_1385777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385777).length < 2 ^ (prefixWord ++ tailWord_1385777).sum := by decide
  have hdescent : baseEnd_1385777 < baseStart_1385777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385796 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1385796 : Nat := 118140960795 + 1385796 * 2 ^ 59
def prefixEnd_1385796 : Nat := 4983230072969 + 3 ^ 40 * 1385796 * 2
def baseEnd_1385796 : Nat := 474386291385443533651231

theorem tailTrace_1385796 : CollatzResearch.WordTrace tailWord_1385796 prefixEnd_1385796 474386291385443533651231 := by
  unfold tailWord_1385796
  simp only [CollatzResearch.WordTrace]
  refine ⟨25272066243752620979620621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33696088325003494639494161 25272066243752620979620621)
  ·
    refine ⟨9477024841407232867357733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25272066243752620979620621 9477024841407232867357733)
    ·
      refine ⟨1776942157763856162629575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9477024841407232867357733 1776942157763856162629575)
      ·
        refine ⟨2665413236645784243944363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776942157763856162629575 2665413236645784243944363)
        ·
          refine ⟨3998119854968676365916545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665413236645784243944363 3998119854968676365916545)
          ·
            refine ⟨2998589891226507274437409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998119854968676365916545 2998589891226507274437409)
            ·
              refine ⟨2248942418419880455828057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998589891226507274437409 2248942418419880455828057)
              ·
                refine ⟨1686706813814910341871043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248942418419880455828057 1686706813814910341871043)
                ·
                  refine ⟨2530060220722365512806565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686706813814910341871043 2530060220722365512806565)
                  ·
                    refine ⟨474386291385443533651231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2530060220722365512806565 474386291385443533651231)
                    ·
                      rfl

theorem cell22_1385796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1385796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385796 prefixEnd_1385796 := by exact prefixLift 1385796
  have htrace : WordTrace (prefixWord ++ tailWord_1385796) baseStart_1385796 baseEnd_1385796 := by
    simpa [prefixWord, tailWord_1385796, baseEnd_1385796] using wordTrace_append hprefix tailTrace_1385796
  have hstable : (prefixWord ++ tailWord_1385796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385796).length < 2 ^ (prefixWord ++ tailWord_1385796).sum := by decide
  have hdescent : baseEnd_1385796 < baseStart_1385796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385882 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_1385882 : Nat := 118140960795 + 1385882 * 2 ^ 59
def prefixEnd_1385882 : Nat := 4983230072969 + 3 ^ 40 * 1385882 * 2
def baseEnd_1385882 : Nat := 474415730942967976000967

theorem tailTrace_1385882 : CollatzResearch.WordTrace tailWord_1385882 prefixEnd_1385882 474415730942967976000967 := by
  unfold tailWord_1385882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12636817291298419661717975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33698179443462452431247933 12636817291298419661717975)
  ·
    refine ⟨18955225936947629492576963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12636817291298419661717975 18955225936947629492576963)
    ·
      refine ⟨28432838905421444238865445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18955225936947629492576963 28432838905421444238865445)
      ·
        refine ⟨5331157294766520794787271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28432838905421444238865445 5331157294766520794787271)
        ·
          refine ⟨7996735942149781192180907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331157294766520794787271 7996735942149781192180907)
          ·
            refine ⟨11995103913224671788271361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996735942149781192180907 11995103913224671788271361)
            ·
              refine ⟨8996327934918503841203521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11995103913224671788271361 8996327934918503841203521)
              ·
                refine ⟨6747245951188877880902641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8996327934918503841203521 6747245951188877880902641)
                ·
                  refine ⟨5060434463391658410676981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6747245951188877880902641 5060434463391658410676981)
                  ·
                    refine ⟨474415730942967976000967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5060434463391658410676981 474415730942967976000967)
                    ·
                      rfl

theorem cell22_1385882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_1385882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385882 prefixEnd_1385882 := by exact prefixLift 1385882
  have htrace : WordTrace (prefixWord ++ tailWord_1385882) baseStart_1385882 baseEnd_1385882 := by
    simpa [prefixWord, tailWord_1385882, baseEnd_1385882] using wordTrace_append hprefix tailTrace_1385882
  have hstable : (prefixWord ++ tailWord_1385882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385882).length < 2 ^ (prefixWord ++ tailWord_1385882).sum := by decide
  have hdescent : baseEnd_1385882 < baseStart_1385882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385927 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1385927 : Nat := 118140960795 + 1385927 * 2 ^ 59
def prefixEnd_1385927 : Nat := 4983230072969 + 3 ^ 40 * 1385927 * 2
def baseEnd_1385927 : Nat := 474431135362602858625829

theorem tailTrace_1385927 : CollatzResearch.WordTrace tailWord_1385927 prefixEnd_1385927 474431135362602858625829 := by
  unfold tailWord_1385927
  simp only [CollatzResearch.WordTrace]
  refine ⟨50548910450030651332260035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33699273633353767554840023 50548910450030651332260035)
  ·
    refine ⟨75823365675045976998390053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50548910450030651332260035 75823365675045976998390053)
    ·
      refine ⟨14216881064071120687198135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75823365675045976998390053 14216881064071120687198135)
      ·
        refine ⟨21325321596106681030797203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14216881064071120687198135 21325321596106681030797203)
        ·
          refine ⟨31987982394160021546195805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21325321596106681030797203 31987982394160021546195805)
          ·
            refine ⟨11995493397810008079823427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31987982394160021546195805 11995493397810008079823427)
            ·
              refine ⟨17993240096715012119735141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11995493397810008079823427 17993240096715012119735141)
              ·
                refine ⟨3373732518134064772450339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17993240096715012119735141 3373732518134064772450339)
                ·
                  refine ⟨5060598777201097158675509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373732518134064772450339 5060598777201097158675509)
                  ·
                    refine ⟨474431135362602858625829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5060598777201097158675509 474431135362602858625829)
                    ·
                      rfl

theorem cell22_1385927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1385927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385927 prefixEnd_1385927 := by exact prefixLift 1385927
  have htrace : WordTrace (prefixWord ++ tailWord_1385927) baseStart_1385927 baseEnd_1385927 := by
    simpa [prefixWord, tailWord_1385927, baseEnd_1385927] using wordTrace_append hprefix tailTrace_1385927
  have hstable : (prefixWord ++ tailWord_1385927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385927).length < 2 ^ (prefixWord ++ tailWord_1385927).sum := by decide
  have hdescent : baseEnd_1385927 < baseStart_1385927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385974 : List Nat := [5, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1385974 : Nat := 118140960795 + 1385974 * 2 ^ 59
def prefixEnd_1385974 : Nat := 4983230072969 + 3 ^ 40 * 1385974 * 2
def baseEnd_1385974 : Nat := 52716358269234489188965

theorem tailTrace_1385974 : CollatzResearch.WordTrace tailWord_1385974 prefixEnd_1385974 52716358269234489188965 := by
  unfold tailWord_1385974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159414042553773647451311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33700416453906918906147317 3159414042553773647451311)
  ·
    refine ⟨4739121063830660471176967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3159414042553773647451311 4739121063830660471176967)
    ·
      refine ⟨7108681595745990706765451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739121063830660471176967 7108681595745990706765451)
      ·
        refine ⟨10663022393618986060148177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108681595745990706765451 10663022393618986060148177)
        ·
          refine ⟨7997266795214239545111133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10663022393618986060148177 7997266795214239545111133)
          ·
            refine ⟨2998975048205339829416675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7997266795214239545111133 2998975048205339829416675)
            ·
              refine ⟨4498462572308009744125013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998975048205339829416675 4498462572308009744125013)
              ·
                refine ⟨52716358269234489188965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4498462572308009744125013 52716358269234489188965)
                ·
                  rfl

theorem cell22_1385974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1385974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385974 prefixEnd_1385974 := by exact prefixLift 1385974
  have htrace : WordTrace (prefixWord ++ tailWord_1385974) baseStart_1385974 baseEnd_1385974 := by
    simpa [prefixWord, tailWord_1385974, baseEnd_1385974] using wordTrace_append hprefix tailTrace_1385974
  have hstable : (prefixWord ++ tailWord_1385974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385974).length < 2 ^ (prefixWord ++ tailWord_1385974).sum := by decide
  have hdescent : baseEnd_1385974 < baseStart_1385974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385997 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1385997 : Nat := 118140960795 + 1385997 * 2 ^ 59
def prefixEnd_1385997 : Nat := 4983230072969 + 3 ^ 40 * 1385997 * 2
def baseEnd_1385997 : Nat := 158151699264382003125205

theorem tailTrace_1385997 : CollatzResearch.WordTrace tailWord_1385997 prefixEnd_1385997 158151699264382003125205 := by
  unfold tailWord_1385997
  simp only [CollatzResearch.WordTrace]
  refine ⟨50551463559777053287308245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33700975706518035524872163 50551463559777053287308245)
  ·
    refine ⟨1184799927182274686421287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50551463559777053287308245 1184799927182274686421287)
    ·
      refine ⟨1777199890773412029631931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184799927182274686421287 1777199890773412029631931)
      ·
        refine ⟨2665799836160118044447897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777199890773412029631931 2665799836160118044447897)
        ·
          refine ⟨1999349877120088533335923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665799836160118044447897 1999349877120088533335923)
          ·
            refine ⟨2999024815680132800003885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999349877120088533335923 2999024815680132800003885)
            ·
              refine ⟨1124634305880049800001457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2999024815680132800003885 1124634305880049800001457)
              ·
                refine ⟨843475729410037350001093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124634305880049800001457 843475729410037350001093)
                ·
                  refine ⟨158151699264382003125205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843475729410037350001093 158151699264382003125205)
                  ·
                    rfl

theorem cell22_1385997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1385997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385997 prefixEnd_1385997 := by exact prefixLift 1385997
  have htrace : WordTrace (prefixWord ++ tailWord_1385997) baseStart_1385997 baseEnd_1385997 := by
    simpa [prefixWord, tailWord_1385997, baseEnd_1385997] using wordTrace_append hprefix tailTrace_1385997
  have hstable : (prefixWord ++ tailWord_1385997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385997).length < 2 ^ (prefixWord ++ tailWord_1385997).sum := by decide
  have hdescent : baseEnd_1385997 < baseStart_1385997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386079 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 8, 3]
def baseStart_1386079 : Nat := 118140960795 + 1386079 * 2 ^ 59
def prefixEnd_1386079 : Nat := 4983230072969 + 3 ^ 40 * 1386079 * 2
def baseEnd_1386079 : Nat := 474483168068925128825363

theorem tailTrace_1386079 : CollatzResearch.WordTrace tailWord_1386079 prefixEnd_1386079 474483168068925128825363 := by
  unfold tailWord_1386079
  simp only [CollatzResearch.WordTrace]
  refine ⟨50554454345479981291793291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33702969563653320861195527 50554454345479981291793291)
  ·
    refine ⟨75831681518219971937689937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50554454345479981291793291 75831681518219971937689937)
    ·
      refine ⟨56873761138664978953267453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75831681518219971937689937 56873761138664978953267453)
      ·
        refine ⟨21327660426999367107475295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56873761138664978953267453 21327660426999367107475295)
        ·
          refine ⟨31991490640499050661212943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21327660426999367107475295 31991490640499050661212943)
          ·
            refine ⟨47987235960748575991819415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31991490640499050661212943 47987235960748575991819415)
            ·
              refine ⟨71980853941122863987729123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47987235960748575991819415 71980853941122863987729123)
              ·
                refine ⟨107971280911684295981593685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71980853941122863987729123 107971280911684295981593685)
                ·
                  refine ⟨1265288448183800343534301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 107971280911684295981593685 1265288448183800343534301)
                  ·
                    refine ⟨474483168068925128825363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265288448183800343534301 474483168068925128825363)
                    ·
                      rfl

theorem cell22_1386079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_1386079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386079 prefixEnd_1386079 := by exact prefixLift 1386079
  have htrace : WordTrace (prefixWord ++ tailWord_1386079) baseStart_1386079 baseEnd_1386079 := by
    simpa [prefixWord, tailWord_1386079, baseEnd_1386079] using wordTrace_append hprefix tailTrace_1386079
  have hstable : (prefixWord ++ tailWord_1386079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386079).length < 2 ^ (prefixWord ++ tailWord_1386079).sum := by decide
  have hdescent : baseEnd_1386079 < baseStart_1386079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386098 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1386098 : Nat := 118140960795 + 1386098 * 2 ^ 59
def prefixEnd_1386098 : Nat := 4983230072969 + 3 ^ 40 * 1386098 * 2
def baseEnd_1386098 : Nat := 158163224052405137533435

theorem tailTrace_1386098 : CollatzResearch.WordTrace tailWord_1386098 prefixEnd_1386098 158163224052405137533435 := by
  unfold tailWord_1386098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638786833102786884183737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33703431554940765024489965 12638786833102786884183737)
  ·
    refine ⟨9479090124827090163137803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12638786833102786884183737 9479090124827090163137803)
    ·
      refine ⟨14218635187240635244706705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9479090124827090163137803 14218635187240635244706705)
      ·
        refine ⟨10663976390430476433530029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14218635187240635244706705 10663976390430476433530029)
        ·
          refine ⟨3998991146411428662573761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10663976390430476433530029 3998991146411428662573761)
          ·
            refine ⟨2999243359808571496930321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998991146411428662573761 2999243359808571496930321)
            ·
              refine ⟨2249432519856428622697741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2999243359808571496930321 2249432519856428622697741)
              ·
                refine ⟨843537194946160733511653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2249432519856428622697741 843537194946160733511653)
                ·
                  refine ⟨158163224052405137533435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843537194946160733511653 158163224052405137533435)
                  ·
                    rfl

theorem cell22_1386098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1386098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386098 prefixEnd_1386098 := by exact prefixLift 1386098
  have htrace : WordTrace (prefixWord ++ tailWord_1386098) baseStart_1386098 baseEnd_1386098 := by
    simpa [prefixWord, tailWord_1386098, baseEnd_1386098] using wordTrace_append hprefix tailTrace_1386098
  have hstable : (prefixWord ++ tailWord_1386098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386098).length < 2 ^ (prefixWord ++ tailWord_1386098).sum := by decide
  have hdescent : baseEnd_1386098 < baseStart_1386098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386109 : List Nat := [1, 4, 1, 1, 4, 2, 9]
def baseStart_1386109 : Nat := 118140960795 + 1386109 * 2 ^ 59
def prefixEnd_1386109 : Nat := 4983230072969 + 3 ^ 40 * 1386109 * 2
def baseEnd_1386109 : Nat := 17573831025259816687973

theorem tailTrace_1386109 : CollatzResearch.WordTrace tailWord_1386109 prefixEnd_1386109 17573831025259816687973 := by
  unfold tailWord_1386109
  simp only [CollatzResearch.WordTrace]
  refine ⟨50555548535371296415385381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33703699023580864276923587 50555548535371296415385381)
  ·
    refine ⟨9479165350382118077884759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50555548535371296415385381 9479165350382118077884759)
    ·
      refine ⟨14218748025573177116827139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9479165350382118077884759 14218748025573177116827139)
      ·
        refine ⟨21328122038359765675240709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14218748025573177116827139 21328122038359765675240709)
        ·
          refine ⟨3999022882192456064107633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21328122038359765675240709 3999022882192456064107633)
          ·
            refine ⟨2999267161644342048080725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999022882192456064107633 2999267161644342048080725)
            ·
              refine ⟨17573831025259816687973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2999267161644342048080725 17573831025259816687973)
              ·
                rfl

theorem cell22_1386109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 9].length) (baseStart_1386109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386109 prefixEnd_1386109 := by exact prefixLift 1386109
  have htrace : WordTrace (prefixWord ++ tailWord_1386109) baseStart_1386109 baseEnd_1386109 := by
    simpa [prefixWord, tailWord_1386109, baseEnd_1386109] using wordTrace_append hprefix tailTrace_1386109
  have hstable : (prefixWord ++ tailWord_1386109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386109).length < 2 ^ (prefixWord ++ tailWord_1386109).sum := by decide
  have hdescent : baseEnd_1386109 < baseStart_1386109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386113 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1386113 : Nat := 118140960795 + 1386113 * 2 ^ 59
def prefixEnd_1386113 : Nat := 4983230072969 + 3 ^ 40 * 1386113 * 2
def baseEnd_1386113 : Nat := 474494806963760373475259

theorem tailTrace_1386113 : CollatzResearch.WordTrace tailWord_1386113 prefixEnd_1386113 474494806963760373475259 := by
  unfold tailWord_1386113
  simp only [CollatzResearch.WordTrace]
  refine ⟨50555694427356805098530993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33703796284904536732353995 50555694427356805098530993)
  ·
    refine ⟨37916770820517603823898245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50555694427356805098530993 37916770820517603823898245)
    ·
      refine ⟨7109394528847050716980921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37916770820517603823898245 7109394528847050716980921)
      ·
        refine ⟨5332045896635288037735691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7109394528847050716980921 5332045896635288037735691)
        ·
          refine ⟨7998068844952932056603537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332045896635288037735691 7998068844952932056603537)
          ·
            refine ⟨5998551633714699042452653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7998068844952932056603537 5998551633714699042452653)
            ·
              refine ⟨2249456862643012140919745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5998551633714699042452653 2249456862643012140919745)
              ·
                refine ⟨1687092646982259105689809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249456862643012140919745 1687092646982259105689809)
                ·
                  refine ⟨1265319485236694329267357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1687092646982259105689809 1265319485236694329267357)
                  ·
                    refine ⟨474494806963760373475259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265319485236694329267357 474494806963760373475259)
                    ·
                      rfl

theorem cell22_1386113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1386113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386113 prefixEnd_1386113 := by exact prefixLift 1386113
  have htrace : WordTrace (prefixWord ++ tailWord_1386113) baseStart_1386113 baseEnd_1386113 := by
    simpa [prefixWord, tailWord_1386113, baseEnd_1386113] using wordTrace_append hprefix tailTrace_1386113
  have hstable : (prefixWord ++ tailWord_1386113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386113).length < 2 ^ (prefixWord ++ tailWord_1386113).sum := by decide
  have hdescent : baseEnd_1386113 < baseStart_1386113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386130 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1386130 : Nat := 118140960795 + 1386130 * 2 ^ 59
def prefixEnd_1386130 : Nat := 4983230072969 + 3 ^ 40 * 1386130 * 2
def baseEnd_1386130 : Nat := 474500626411177995800207

theorem tailTrace_1386130 : CollatzResearch.WordTrace tailWord_1386130 prefixEnd_1386130 474500626411177995800207 := by
  unfold tailWord_1386130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639078617073804250474961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33704209645530144667933229 12639078617073804250474961)
  ·
    refine ⟨9479308962805353187856221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12639078617073804250474961 9479308962805353187856221)
    ·
      refine ⟨3554740861052007445446083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9479308962805353187856221 3554740861052007445446083)
      ·
        refine ⟨5332111291578011168169125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554740861052007445446083 5332111291578011168169125)
        ·
          refine ⟨999770867170877094031711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5332111291578011168169125 999770867170877094031711)
          ·
            refine ⟨1499656300756315641047567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999770867170877094031711 1499656300756315641047567)
            ·
              refine ⟨2249484451134473461571351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499656300756315641047567 2249484451134473461571351)
              ·
                refine ⟨3374226676701710192357027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249484451134473461571351 3374226676701710192357027)
                ·
                  refine ⟨5061340015052565288535541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374226676701710192357027 5061340015052565288535541)
                  ·
                    refine ⟨474500626411177995800207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5061340015052565288535541 474500626411177995800207)
                    ·
                      rfl

theorem cell22_1386130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1386130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386130 prefixEnd_1386130 := by exact prefixLift 1386130
  have htrace : WordTrace (prefixWord ++ tailWord_1386130) baseStart_1386130 baseEnd_1386130 := by
    simpa [prefixWord, tailWord_1386130, baseEnd_1386130] using wordTrace_append hprefix tailTrace_1386130
  have hstable : (prefixWord ++ tailWord_1386130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386130).length < 2 ^ (prefixWord ++ tailWord_1386130).sum := by decide
  have hdescent : baseEnd_1386130 < baseStart_1386130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386169 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_1386169 : Nat := 118140960795 + 1386169 * 2 ^ 59
def prefixEnd_1386169 : Nat := 4983230072969 + 3 ^ 40 * 1386169 * 2
def baseEnd_1386169 : Nat := 474513976908194894075087

theorem tailTrace_1386169 : CollatzResearch.WordTrace tailWord_1386169 prefixEnd_1386169 474513976908194894075087 := by
  unfold tailWord_1386169
  simp only [CollatzResearch.WordTrace]
  refine ⟨50557736915153926662569561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33705157943435951108379707 50557736915153926662569561)
  ·
    refine ⟨37918302686365444996927171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50557736915153926662569561 37918302686365444996927171)
    ·
      refine ⟨56877454029548167495390757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37918302686365444996927171 56877454029548167495390757)
      ·
        refine ⟨10664522630540281405385767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56877454029548167495390757 10664522630540281405385767)
        ·
          refine ⟨15996783945810422108078651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10664522630540281405385767 15996783945810422108078651)
          ·
            refine ⟨23995175918715633162117977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15996783945810422108078651 23995175918715633162117977)
            ·
              refine ⟨17996381939036724871588483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23995175918715633162117977 17996381939036724871588483)
              ·
                refine ⟨26994572908555087307382725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17996381939036724871588483 26994572908555087307382725)
                ·
                  refine ⟨5061482420354078870134261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26994572908555087307382725 5061482420354078870134261)
                  ·
                    refine ⟨474513976908194894075087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5061482420354078870134261 474513976908194894075087)
                    ·
                      rfl

theorem cell22_1386169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_1386169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386169 prefixEnd_1386169 := by exact prefixLift 1386169
  have htrace : WordTrace (prefixWord ++ tailWord_1386169) baseStart_1386169 baseEnd_1386169 := by
    simpa [prefixWord, tailWord_1386169, baseEnd_1386169] using wordTrace_append hprefix tailTrace_1386169
  have hstable : (prefixWord ++ tailWord_1386169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386169).length < 2 ^ (prefixWord ++ tailWord_1386169).sum := by decide
  have hdescent : baseEnd_1386169 < baseStart_1386169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386175 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 1, 3]
def baseStart_1386175 : Nat := 118140960795 + 1386175 * 2 ^ 59
def prefixEnd_1386175 : Nat := 4983230072969 + 3 ^ 40 * 1386175 * 2
def baseEnd_1386175 : Nat := 474516030830812878425069

theorem tailTrace_1386175 : CollatzResearch.WordTrace tailWord_1386175 prefixEnd_1386175 474516030830812878425069 := by
  unfold tailWord_1386175
  simp only [CollatzResearch.WordTrace]
  refine ⟨50557955753132189687287979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33705303835421459791525319 50557955753132189687287979)
  ·
    refine ⟨75836933629698284530931969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50557955753132189687287979 75836933629698284530931969)
    ·
      refine ⟨56877700222273713398198977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75836933629698284530931969 56877700222273713398198977)
      ·
        refine ⟨42658275166705285048649233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56877700222273713398198977 42658275166705285048649233)
        ·
          refine ⟨31993706375028963786486925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42658275166705285048649233 31993706375028963786486925)
          ·
            refine ⟨11997639890635861419932597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31993706375028963786486925 11997639890635861419932597)
            ·
              refine ⟨1124778739747112008118681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11997639890635861419932597 1124778739747112008118681)
              ·
                refine ⟨843584054810334006089011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124778739747112008118681 843584054810334006089011)
                ·
                  refine ⟨1265376082215501009133517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843584054810334006089011 1265376082215501009133517)
                  ·
                    refine ⟨474516030830812878425069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265376082215501009133517 474516030830812878425069)
                    ·
                      rfl

theorem cell22_1386175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_1386175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386175 prefixEnd_1386175 := by exact prefixLift 1386175
  have htrace : WordTrace (prefixWord ++ tailWord_1386175) baseStart_1386175 baseEnd_1386175 := by
    simpa [prefixWord, tailWord_1386175, baseEnd_1386175] using wordTrace_append hprefix tailTrace_1386175
  have hstable : (prefixWord ++ tailWord_1386175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386175).length < 2 ^ (prefixWord ++ tailWord_1386175).sum := by decide
  have hdescent : baseEnd_1386175 < baseStart_1386175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386188 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_1386188 : Nat := 118140960795 + 1386188 * 2 ^ 59
def prefixEnd_1386188 : Nat := 4983230072969 + 3 ^ 40 * 1386188 * 2
def baseEnd_1386188 : Nat := 158173493665495059283343

theorem tailTrace_1386188 : CollatzResearch.WordTrace tailWord_1386188 prefixEnd_1386188 158173493665495059283343 := by
  unfold tailWord_1386188
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279214951042546453755609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33705619934723395271674145 25279214951042546453755609)
  ·
    refine ⟨18959411213281909840316707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25279214951042546453755609 18959411213281909840316707)
    ·
      refine ⟨28439116819922864760475061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18959411213281909840316707 28439116819922864760475061)
      ·
        refine ⟨2666167201867768571294537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28439116819922864760475061 2666167201867768571294537)
        ·
          refine ⟨1999625401400826428470903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2666167201867768571294537 1999625401400826428470903)
          ·
            refine ⟨2999438102101239642706355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999625401400826428470903 2999438102101239642706355)
            ·
              refine ⟨4499157153151859464059533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999438102101239642706355 4499157153151859464059533)
              ·
                refine ⟨1687183932431947299022325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4499157153151859464059533 1687183932431947299022325)
                ·
                  refine ⟨158173493665495059283343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687183932431947299022325 158173493665495059283343)
                  ·
                    rfl

theorem cell22_1386188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_1386188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386188 prefixEnd_1386188 := by exact prefixLift 1386188
  have htrace : WordTrace (prefixWord ++ tailWord_1386188) baseStart_1386188 baseEnd_1386188 := by
    simpa [prefixWord, tailWord_1386188, baseEnd_1386188] using wordTrace_append hprefix tailTrace_1386188
  have hstable : (prefixWord ++ tailWord_1386188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386188).length < 2 ^ (prefixWord ++ tailWord_1386188).sum := by decide
  have hdescent : baseEnd_1386188 < baseStart_1386188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386199 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 8]
def baseStart_1386199 : Nat := 118140960795 + 1386199 * 2 ^ 59
def prefixEnd_1386199 : Nat := 4983230072969 + 3 ^ 40 * 1386199 * 2
def baseEnd_1386199 : Nat := 158174748840428271941665

theorem tailTrace_1386199 : CollatzResearch.WordTrace tailWord_1386199 prefixEnd_1386199 158174748840428271941665 := by
  unfold tailWord_1386199
  simp only [CollatzResearch.WordTrace]
  refine ⟨50558831105045241786161651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33705887403363494524107767 50558831105045241786161651)
  ·
    refine ⟨75838246657567862679242477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50558831105045241786161651 75838246657567862679242477)
    ·
      refine ⟨28439342496587948504715929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75838246657567862679242477 28439342496587948504715929)
      ·
        refine ⟨21329506872440961378536947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28439342496587948504715929 21329506872440961378536947)
        ·
          refine ⟨31994260308661442067805421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21329506872440961378536947 31994260308661442067805421)
          ·
            refine ⟨11997847615748040775427033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31994260308661442067805421 11997847615748040775427033)
            ·
              refine ⟨8998385711811030581570275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11997847615748040775427033 8998385711811030581570275)
              ·
                refine ⟨13497578567716545872355413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8998385711811030581570275 13497578567716545872355413)
                ·
                  refine ⟨158174748840428271941665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13497578567716545872355413 158174748840428271941665)
                  ·
                    rfl

theorem cell22_1386199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_1386199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386199 prefixEnd_1386199 := by exact prefixLift 1386199
  have htrace : WordTrace (prefixWord ++ tailWord_1386199) baseStart_1386199 baseEnd_1386199 := by
    simpa [prefixWord, tailWord_1386199, baseEnd_1386199] using wordTrace_append hprefix tailTrace_1386199
  have hstable : (prefixWord ++ tailWord_1386199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386199).length < 2 ^ (prefixWord ++ tailWord_1386199).sum := by decide
  have hdescent : baseEnd_1386199 < baseStart_1386199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386201 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_1386201 : Nat := 118140960795 + 1386201 * 2 ^ 59
def prefixEnd_1386201 : Nat := 4983230072969 + 3 ^ 40 * 1386201 * 2
def baseEnd_1386201 : Nat := 474524931162157477274989

theorem tailTrace_1386201 : CollatzResearch.WordTrace tailWord_1386201 prefixEnd_1386201 474524931162157477274989 := by
  unfold tailWord_1386201
  simp only [CollatzResearch.WordTrace]
  refine ⟨50558904051037996127734457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33705936034025330751822971 50558904051037996127734457)
  ·
    refine ⟨37919178038278497095800843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50558904051037996127734457 37919178038278497095800843)
    ·
      refine ⟨56878767057417745643701265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37919178038278497095800843 56878767057417745643701265)
      ·
        refine ⟨42659075293063309232775949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56878767057417745643701265 42659075293063309232775949)
        ·
          refine ⟨15997153234898740962290981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42659075293063309232775949 15997153234898740962290981)
          ·
            refine ⟨2999466231543513930429559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15997153234898740962290981 2999466231543513930429559)
            ·
              refine ⟨4499199347315270895644339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999466231543513930429559 4499199347315270895644339)
              ·
                refine ⟨6748799020972906343466509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499199347315270895644339 6748799020972906343466509)
                ·
                  refine ⟨2530799632864839878799941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6748799020972906343466509 2530799632864839878799941)
                  ·
                    refine ⟨474524931162157477274989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2530799632864839878799941 474524931162157477274989)
                    ·
                      rfl

theorem cell22_1386201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_1386201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386201 prefixEnd_1386201 := by exact prefixLift 1386201
  have htrace : WordTrace (prefixWord ++ tailWord_1386201) baseStart_1386201 baseEnd_1386201 := by
    simpa [prefixWord, tailWord_1386201, baseEnd_1386201] using wordTrace_append hprefix tailTrace_1386201
  have hstable : (prefixWord ++ tailWord_1386201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386201).length < 2 ^ (prefixWord ++ tailWord_1386201).sum := by decide
  have hdescent : baseEnd_1386201 < baseStart_1386201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386231 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 4, 3]
def baseStart_1386231 : Nat := 118140960795 + 1386231 * 2 ^ 59
def prefixEnd_1386231 : Nat := 4983230072969 + 3 ^ 40 * 1386231 * 2
def baseEnd_1386231 : Nat := 474535200775247399024897

theorem tailTrace_1386231 : CollatzResearch.WordTrace tailWord_1386231 prefixEnd_1386231 474535200775247399024897 := by
  unfold tailWord_1386231
  simp only [CollatzResearch.WordTrace]
  refine ⟨50559998240929311251326547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33706665493952874167551031 50559998240929311251326547)
  ·
    refine ⟨75839997361393966876989821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50559998240929311251326547 75839997361393966876989821)
    ·
      refine ⟨28439999010522737578871183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75839997361393966876989821 28439999010522737578871183)
      ·
        refine ⟨42659998515784106368306775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28439999010522737578871183 42659998515784106368306775)
        ·
          refine ⟨63989997773676159552460163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42659998515784106368306775 63989997773676159552460163)
          ·
            refine ⟨95984996660514239328690245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63989997773676159552460163 95984996660514239328690245)
            ·
              refine ⟨17997186873846419874129421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95984996660514239328690245 17997186873846419874129421)
              ·
                refine ⟨6748945077692407452798533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17997186873846419874129421 6748945077692407452798533)
                ·
                  refine ⟨1265427202067326397399725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6748945077692407452798533 1265427202067326397399725)
                  ·
                    refine ⟨474535200775247399024897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265427202067326397399725 474535200775247399024897)
                    ·
                      rfl

theorem cell22_1386231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_1386231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386231 prefixEnd_1386231 := by exact prefixLift 1386231
  have htrace : WordTrace (prefixWord ++ tailWord_1386231) baseStart_1386231 baseEnd_1386231 := by
    simpa [prefixWord, tailWord_1386231, baseEnd_1386231] using wordTrace_append hprefix tailTrace_1386231
  have hstable : (prefixWord ++ tailWord_1386231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386231).length < 2 ^ (prefixWord ++ tailWord_1386231).sum := by decide
  have hdescent : baseEnd_1386231 < baseStart_1386231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386248 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1386248 : Nat := 118140960795 + 1386248 * 2 ^ 59
def prefixEnd_1386248 : Nat := 4983230072969 + 3 ^ 40 * 1386248 * 2
def baseEnd_1386248 : Nat := 474541020222665021349845

theorem tailTrace_1386248 : CollatzResearch.WordTrace tailWord_1386248 prefixEnd_1386248 474541020222665021349845 := by
  unfold tailWord_1386248
  simp only [CollatzResearch.WordTrace]
  refine ⟨25280309140933861577347699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33707078854578482103130265 25280309140933861577347699)
  ·
    refine ⟨37920463711400792366021549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25280309140933861577347699 37920463711400792366021549)
    ·
      refine ⟨14220173891775297137258081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37920463711400792366021549 14220173891775297137258081)
      ·
        refine ⟨10665130418831472852943561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14220173891775297137258081 10665130418831472852943561)
        ·
          refine ⟨7998847814123604639707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10665130418831472852943561 7998847814123604639707671)
          ·
            refine ⟨11998271721185406959561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998847814123604639707671 11998271721185406959561507)
            ·
              refine ⟨17997407581778110439342261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11998271721185406959561507 17997407581778110439342261)
              ·
                refine ⟨1687256960791697853688337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17997407581778110439342261 1687256960791697853688337)
                ·
                  refine ⟨1265442720593773390266253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1687256960791697853688337 1265442720593773390266253)
                  ·
                    refine ⟨474541020222665021349845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265442720593773390266253 474541020222665021349845)
                    ·
                      rfl

theorem cell22_1386248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1386248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386248 prefixEnd_1386248 := by exact prefixLift 1386248
  have htrace : WordTrace (prefixWord ++ tailWord_1386248) baseStart_1386248 baseEnd_1386248 := by
    simpa [prefixWord, tailWord_1386248, baseEnd_1386248] using wordTrace_append hprefix tailTrace_1386248
  have hstable : (prefixWord ++ tailWord_1386248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386248).length < 2 ^ (prefixWord ++ tailWord_1386248).sum := by decide
  have hdescent : baseEnd_1386248 < baseStart_1386248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386259 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_1386259 : Nat := 118140960795 + 1386259 * 2 ^ 59
def prefixEnd_1386259 : Nat := 4983230072969 + 3 ^ 40 * 1386259 * 2
def baseEnd_1386259 : Nat := 474544785747464659324811

theorem tailTrace_1386259 : CollatzResearch.WordTrace tailWord_1386259 prefixEnd_1386259 474544785747464659324811 := by
  unfold tailWord_1386259
  simp only [CollatzResearch.WordTrace]
  refine ⟨50561019484827872033345831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33707346323218581355563887 50561019484827872033345831)
  ·
    refine ⟨75841529227241808050018747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50561019484827872033345831 75841529227241808050018747)
    ·
      refine ⟨113762293840862712075028121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75841529227241808050018747 113762293840862712075028121)
      ·
        refine ⟨85321720380647034056271091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113762293840862712075028121 85321720380647034056271091)
        ·
          refine ⟨127982580570970551084406637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85321720380647034056271091 127982580570970551084406637)
          ·
            refine ⟨47993467714113956656652489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127982580570970551084406637 47993467714113956656652489)
            ·
              refine ⟨35995100785585467492489367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47993467714113956656652489 35995100785585467492489367)
              ·
                refine ⟨53992651178378201238734051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35995100785585467492489367 53992651178378201238734051)
                ·
                  refine ⟨80988976767567301858101077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53992651178378201238734051 80988976767567301858101077)
                  ·
                    refine ⟨474544785747464659324811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 80988976767567301858101077 474544785747464659324811)
                    ·
                      rfl

theorem cell22_1386259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_1386259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386259 prefixEnd_1386259 := by exact prefixLift 1386259
  have htrace : WordTrace (prefixWord ++ tailWord_1386259) baseStart_1386259 baseEnd_1386259 := by
    simpa [prefixWord, tailWord_1386259, baseEnd_1386259] using wordTrace_append hprefix tailTrace_1386259
  have hstable : (prefixWord ++ tailWord_1386259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386259).length < 2 ^ (prefixWord ++ tailWord_1386259).sum := by decide
  have hdescent : baseEnd_1386259 < baseStart_1386259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386263 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 2, 4]
def baseStart_1386263 : Nat := 118140960795 + 1386263 * 2 ^ 59
def prefixEnd_1386263 : Nat := 4983230072969 + 3 ^ 40 * 1386263 * 2
def baseEnd_1386263 : Nat := 474546155029209982224799

theorem tailTrace_1386263 : CollatzResearch.WordTrace tailWord_1386263 prefixEnd_1386263 474546155029209982224799 := by
  unfold tailWord_1386263
  simp only [CollatzResearch.WordTrace]
  refine ⟨50561165376813380716491443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33707443584542253810994295 50561165376813380716491443)
  ·
    refine ⟨75841748065220071074737165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50561165376813380716491443 75841748065220071074737165)
    ·
      refine ⟨28440655524457526653026437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75841748065220071074737165 28440655524457526653026437)
      ·
        refine ⟨5332622910835786247442457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28440655524457526653026437 5332622910835786247442457)
        ·
          refine ⟨3999467183126839685581843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5332622910835786247442457 3999467183126839685581843)
          ·
            refine ⟨5999200774690259528372765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999467183126839685581843 5999200774690259528372765)
            ·
              refine ⟨2249700290508847323139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5999200774690259528372765 2249700290508847323139787)
              ·
                refine ⟨3374550435763270984709681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249700290508847323139787 3374550435763270984709681)
                ·
                  refine ⟨2530912826822453238532261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374550435763270984709681 2530912826822453238532261)
                  ·
                    refine ⟨474546155029209982224799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2530912826822453238532261 474546155029209982224799)
                    ·
                      rfl

theorem cell22_1386263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_1386263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386263 prefixEnd_1386263 := by exact prefixLift 1386263
  have htrace : WordTrace (prefixWord ++ tailWord_1386263) baseStart_1386263 baseEnd_1386263 := by
    simpa [prefixWord, tailWord_1386263, baseEnd_1386263] using wordTrace_append hprefix tailTrace_1386263
  have hstable : (prefixWord ++ tailWord_1386263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386263).length < 2 ^ (prefixWord ++ tailWord_1386263).sum := by decide
  have hdescent : baseEnd_1386263 < baseStart_1386263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386402 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1386402 : Nat := 118140960795 + 1386402 * 2 ^ 59
def prefixEnd_1386402 : Nat := 4983230072969 + 3 ^ 40 * 1386402 * 2
def baseEnd_1386402 : Nat := 158197912523286650999791

theorem tailTrace_1386402 : CollatzResearch.WordTrace tailWord_1386402 prefixEnd_1386402 158197912523286650999791 := by
  unfold tailWord_1386402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641558780827451863950365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33710823415539871637200973 12641558780827451863950365)
  ·
    refine ⟨4740584542810294448981387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12641558780827451863950365 4740584542810294448981387)
    ·
      refine ⟨7110876814215441673472081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740584542810294448981387 7110876814215441673472081)
      ·
        refine ⟨5333157610661581255104061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7110876814215441673472081 5333157610661581255104061)
        ·
          refine ⟨1999934103998092970664023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5333157610661581255104061 1999934103998092970664023)
          ·
            refine ⟨2999901155997139455996035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999934103998092970664023 2999901155997139455996035)
            ·
              refine ⟨4499851733995709183994053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999901155997139455996035 4499851733995709183994053)
              ·
                refine ⟨843722200124195471998885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4499851733995709183994053 843722200124195471998885)
                ·
                  refine ⟨158197912523286650999791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843722200124195471998885 158197912523286650999791)
                  ·
                    rfl

theorem cell22_1386402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1386402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386402 prefixEnd_1386402 := by exact prefixLift 1386402
  have htrace : WordTrace (prefixWord ++ tailWord_1386402) baseStart_1386402 baseEnd_1386402 := by
    simpa [prefixWord, tailWord_1386402, baseEnd_1386402] using wordTrace_append hprefix tailTrace_1386402
  have hstable : (prefixWord ++ tailWord_1386402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386402).length < 2 ^ (prefixWord ++ tailWord_1386402).sum := by decide
  have hdescent : baseEnd_1386402 < baseStart_1386402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386430 : List Nat := [4, 2, 1, 1, 1, 4, 3, 6]
def baseStart_1386430 : Nat := 118140960795 + 1386430 * 2 ^ 59
def prefixEnd_1386430 : Nat := 4983230072969 + 3 ^ 40 * 1386430 * 2
def baseEnd_1386430 : Nat := 52733702504675245922143

theorem tailTrace_1386430 : CollatzResearch.WordTrace tailWord_1386430 prefixEnd_1386430 52733702504675245922143 := by
  unfold tailWord_1386430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320907045901046029727593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33711504244805578825213829 6320907045901046029727593)
  ·
    refine ⟨4740680284425784522295695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6320907045901046029727593 4740680284425784522295695)
    ·
      refine ⟨7111020426638676783443543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740680284425784522295695 7111020426638676783443543)
      ·
        refine ⟨10666530639958015175165315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7111020426638676783443543 10666530639958015175165315)
        ·
          refine ⟨15999795959937022762747973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10666530639958015175165315 15999795959937022762747973)
          ·
            refine ⟨2999961742488191768015245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15999795959937022762747973 2999961742488191768015245)
            ·
              refine ⟨1124985653433071913005717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2999961742488191768015245 1124985653433071913005717)
              ·
                refine ⟨52733702504675245922143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1124985653433071913005717 52733702504675245922143)
                ·
                  rfl

theorem cell22_1386430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_1386430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386430 prefixEnd_1386430 := by exact prefixLift 1386430
  have htrace : WordTrace (prefixWord ++ tailWord_1386430) baseStart_1386430 baseEnd_1386430 := by
    simpa [prefixWord, tailWord_1386430, baseEnd_1386430] using wordTrace_append hprefix tailTrace_1386430
  have hstable : (prefixWord ++ tailWord_1386430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386430).length < 2 ^ (prefixWord ++ tailWord_1386430).sum := by decide
  have hdescent : baseEnd_1386430 < baseStart_1386430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386441 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 9]
def baseStart_1386441 : Nat := 118140960795 + 1386441 * 2 ^ 59
def prefixEnd_1386441 : Nat := 4983230072969 + 3 ^ 40 * 1386441 * 2
def baseEnd_1386441 : Nat := 158202362688958950424751

theorem tailTrace_1386441 : CollatzResearch.WordTrace tailWord_1386441 prefixEnd_1386441 158202362688958950424751 := by
  unfold tailWord_1386441
  simp only [CollatzResearch.WordTrace]
  refine ⟨50567657570168517116471177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33711771713445678077647451 50567657570168517116471177)
  ·
    refine ⟨37925743177626387837353383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50567657570168517116471177 37925743177626387837353383)
    ·
      refine ⟨56888614766439581756030075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37925743177626387837353383 56888614766439581756030075)
      ·
        refine ⟨85332922149659372634045113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56888614766439581756030075 85332922149659372634045113)
        ·
          refine ⟨63999691612244529475533835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85332922149659372634045113 63999691612244529475533835)
          ·
            refine ⟨95999537418366794213300753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63999691612244529475533835 95999537418366794213300753)
            ·
              refine ⟨71999653063775095659975565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95999537418366794213300753 71999653063775095659975565)
              ·
                refine ⟨26999869898915660872490837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71999653063775095659975565 26999869898915660872490837)
                ·
                  refine ⟨158202362688958950424751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26999869898915660872490837 158202362688958950424751)
                  ·
                    rfl

theorem cell22_1386441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_1386441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386441 prefixEnd_1386441 := by exact prefixLift 1386441
  have htrace : WordTrace (prefixWord ++ tailWord_1386441) baseStart_1386441 baseEnd_1386441 := by
    simpa [prefixWord, tailWord_1386441, baseEnd_1386441] using wordTrace_append hprefix tailTrace_1386441
  have hstable : (prefixWord ++ tailWord_1386441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386441).length < 2 ^ (prefixWord ++ tailWord_1386441).sum := by decide
  have hdescent : baseEnd_1386441 < baseStart_1386441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386488 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1386488 : Nat := 118140960795 + 1386488 * 2 ^ 59
def prefixEnd_1386488 : Nat := 4983230072969 + 3 ^ 40 * 1386488 * 2
def baseEnd_1386488 : Nat := 474623177127384395349109

theorem tailTrace_1386488 : CollatzResearch.WordTrace tailWord_1386488 prefixEnd_1386488 474623177127384395349109 := by
  unfold tailWord_1386488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25284685900499122071716059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33712914533998829428954745 25284685900499122071716059)
  ·
    refine ⟨37927028850748683107574089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25284685900499122071716059 37927028850748683107574089)
    ·
      refine ⟨28445271638061512330680567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37927028850748683107574089 28445271638061512330680567)
      ·
        refine ⟨42667907457092268496020851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28445271638061512330680567 42667907457092268496020851)
        ·
          refine ⟨64001861185638402744031277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42667907457092268496020851 64001861185638402744031277)
          ·
            refine ⟨24000697944614401029011729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64001861185638402744031277 24000697944614401029011729)
            ·
              refine ⟨18000523458460800771758797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24000697944614401029011729 18000523458460800771758797)
              ·
                refine ⟨6750196296922800289409549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18000523458460800771758797 6750196296922800289409549)
                ·
                  refine ⟨2531323611346050108528581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6750196296922800289409549 2531323611346050108528581)
                  ·
                    refine ⟨474623177127384395349109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531323611346050108528581 474623177127384395349109)
                    ·
                      rfl

theorem cell22_1386488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1386488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386488 prefixEnd_1386488 := by exact prefixLift 1386488
  have htrace : WordTrace (prefixWord ++ tailWord_1386488) baseStart_1386488 baseEnd_1386488 := by
    simpa [prefixWord, tailWord_1386488, baseEnd_1386488] using wordTrace_append hprefix tailTrace_1386488
  have hstable : (prefixWord ++ tailWord_1386488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386488).length < 2 ^ (prefixWord ++ tailWord_1386488).sum := by decide
  have hdescent : baseEnd_1386488 < baseStart_1386488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386593 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 9]
def baseStart_1386593 : Nat := 118140960795 + 1386593 * 2 ^ 59
def prefixEnd_1386593 : Nat := 4983230072969 + 3 ^ 40 * 1386593 * 2
def baseEnd_1386593 : Nat := 158219706924399707157929

theorem tailTrace_1386593 : CollatzResearch.WordTrace tailWord_1386593 prefixEnd_1386593 158219706924399707157929 := by
  unfold tailWord_1386593
  simp only [CollatzResearch.WordTrace]
  refine ⟨50573201465617847076004433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33715467643745231384002955 50573201465617847076004433)
  ·
    refine ⟨37929901099213385307003325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50573201465617847076004433 37929901099213385307003325)
    ·
      refine ⟨14223712912205019490126247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37929901099213385307003325 14223712912205019490126247)
      ·
        refine ⟨21335569368307529235189371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14223712912205019490126247 21335569368307529235189371)
        ·
          refine ⟨32003354052461293852784057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21335569368307529235189371 32003354052461293852784057)
          ·
            refine ⟨24002515539345970389588043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32003354052461293852784057 24002515539345970389588043)
            ·
              refine ⟨36003773309018955584382065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24002515539345970389588043 36003773309018955584382065)
              ·
                refine ⟨27002829981764216688286549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36003773309018955584382065 27002829981764216688286549)
                ·
                  refine ⟨158219706924399707157929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27002829981764216688286549 158219706924399707157929)
                  ·
                    rfl

theorem cell22_1386593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_1386593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386593 prefixEnd_1386593 := by exact prefixLift 1386593
  have htrace : WordTrace (prefixWord ++ tailWord_1386593) baseStart_1386593 baseEnd_1386593 := by
    simpa [prefixWord, tailWord_1386593, baseEnd_1386593] using wordTrace_append hprefix tailTrace_1386593
  have hstable : (prefixWord ++ tailWord_1386593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386593).length < 2 ^ (prefixWord ++ tailWord_1386593).sum := by decide
  have hdescent : baseEnd_1386593 < baseStart_1386593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386597 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_1386597 : Nat := 118140960795 + 1386597 * 2 ^ 59
def prefixEnd_1386597 : Nat := 4983230072969 + 3 ^ 40 * 1386597 * 2
def baseEnd_1386597 : Nat := 474660490054944444373775

theorem tailTrace_1386597 : CollatzResearch.WordTrace tailWord_1386597 prefixEnd_1386597 474660490054944444373775 := by
  unfold tailWord_1386597
  simp only [CollatzResearch.WordTrace]
  refine ⟨50573347357603355759150045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33715564905068903839433363 50573347357603355759150045)
  ·
    refine ⟨18965005259101258409681267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50573347357603355759150045 18965005259101258409681267)
    ·
      refine ⟨28447507888651887614521901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18965005259101258409681267 28447507888651887614521901)
      ·
        refine ⟨10667815458244457855445713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28447507888651887614521901 10667815458244457855445713)
        ·
          refine ⟨8000861593683343391584285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10667815458244457855445713 8000861593683343391584285)
          ·
            refine ⟨3000323097631253771844107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8000861593683343391584285 3000323097631253771844107)
            ·
              refine ⟨4500484646446880657766161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000323097631253771844107 4500484646446880657766161)
              ·
                refine ⟨3375363484835160493324621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500484646446880657766161 3375363484835160493324621)
                ·
                  refine ⟨1265761306813185184996733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3375363484835160493324621 1265761306813185184996733)
                  ·
                    refine ⟨474660490054944444373775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265761306813185184996733 474660490054944444373775)
                    ·
                      rfl

theorem cell22_1386597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_1386597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386597 prefixEnd_1386597 := by exact prefixLift 1386597
  have htrace : WordTrace (prefixWord ++ tailWord_1386597) baseStart_1386597 baseEnd_1386597 := by
    simpa [prefixWord, tailWord_1386597, baseEnd_1386597] using wordTrace_append hprefix tailTrace_1386597
  have hstable : (prefixWord ++ tailWord_1386597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386597).length < 2 ^ (prefixWord ++ tailWord_1386597).sum := by decide
  have hdescent : baseEnd_1386597 < baseStart_1386597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386627 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 5]
def baseStart_1386627 : Nat := 118140960795 + 1386627 * 2 ^ 59
def prefixEnd_1386627 : Nat := 4983230072969 + 3 ^ 40 * 1386627 * 2
def baseEnd_1386627 : Nat := 158223586556011455374561

theorem tailTrace_1386627 : CollatzResearch.WordTrace tailWord_1386627 prefixEnd_1386627 158223586556011455374561 := by
  unfold tailWord_1386627
  simp only [CollatzResearch.WordTrace]
  refine ⟨50574441547494670882742135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33716294364996447255161423 50574441547494670882742135)
  ·
    refine ⟨75861662321242006324113203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50574441547494670882742135 75861662321242006324113203)
    ·
      refine ⟨113792493481863009486169805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75861662321242006324113203 113792493481863009486169805)
      ·
        refine ⟨42672185055698628557313677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113792493481863009486169805 42672185055698628557313677)
        ·
          refine ⟨16002069395886985708992629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42672185055698628557313677 16002069395886985708992629)
          ·
            refine ⟨1500194005864404910218059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16002069395886985708992629 1500194005864404910218059)
            ·
              refine ⟨2250291008796607365327089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500194005864404910218059 2250291008796607365327089)
              ·
                refine ⟨1687718256597455523995317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250291008796607365327089 1687718256597455523995317)
                ·
                  refine ⟨158223586556011455374561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687718256597455523995317 158223586556011455374561)
                  ·
                    rfl

theorem cell22_1386627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 5].length) (baseStart_1386627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386627 prefixEnd_1386627 := by exact prefixLift 1386627
  have htrace : WordTrace (prefixWord ++ tailWord_1386627) baseStart_1386627 baseEnd_1386627 := by
    simpa [prefixWord, tailWord_1386627, baseEnd_1386627] using wordTrace_append hprefix tailTrace_1386627
  have hstable : (prefixWord ++ tailWord_1386627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386627).length < 2 ^ (prefixWord ++ tailWord_1386627).sum := by decide
  have hdescent : baseEnd_1386627 < baseStart_1386627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386657 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1386657 : Nat := 118140960795 + 1386657 * 2 ^ 59
def prefixEnd_1386657 : Nat := 4983230072969 + 3 ^ 40 * 1386657 * 2
def baseEnd_1386657 : Nat := 474681029281124287873591

theorem tailTrace_1386657 : CollatzResearch.WordTrace tailWord_1386657 prefixEnd_1386657 474681029281124287873591 := by
  unfold tailWord_1386657
  simp only [CollatzResearch.WordTrace]
  refine ⟨50575535737385986006334225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33717023824923990670889483 50575535737385986006334225)
  ·
    refine ⟨37931651803039489504750669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50575535737385986006334225 37931651803039489504750669)
    ·
      refine ⟨14224369426139808564281501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37931651803039489504750669 14224369426139808564281501)
      ·
        refine ⟨5334138534802428211605563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14224369426139808564281501 5334138534802428211605563)
        ·
          refine ⟨8001207802203642317408345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334138534802428211605563 8001207802203642317408345)
          ·
            refine ⟨6000905851652731738056259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8001207802203642317408345 6000905851652731738056259)
            ·
              refine ⟨9001358777479097607084389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000905851652731738056259 9001358777479097607084389)
              ·
                refine ⟨1687754770777330801328323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9001358777479097607084389 1687754770777330801328323)
                ·
                  refine ⟨2531632156165996201992485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687754770777330801328323 2531632156165996201992485)
                  ·
                    refine ⟨474681029281124287873591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531632156165996201992485 474681029281124287873591)
                    ·
                      rfl

theorem cell22_1386657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1386657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386657 prefixEnd_1386657 := by exact prefixLift 1386657
  have htrace : WordTrace (prefixWord ++ tailWord_1386657) baseStart_1386657 baseEnd_1386657 := by
    simpa [prefixWord, tailWord_1386657, baseEnd_1386657] using wordTrace_append hprefix tailTrace_1386657
  have hstable : (prefixWord ++ tailWord_1386657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386657).length < 2 ^ (prefixWord ++ tailWord_1386657).sum := by decide
  have hdescent : baseEnd_1386657 < baseStart_1386657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386687 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 2, 3]
def baseStart_1386687 : Nat := 118140960795 + 1386687 * 2 ^ 59
def prefixEnd_1386687 : Nat := 4983230072969 + 3 ^ 40 * 1386687 * 2
def baseEnd_1386687 : Nat := 474691298894214209623499

theorem tailTrace_1386687 : CollatzResearch.WordTrace tailWord_1386687 prefixEnd_1386687 474691298894214209623499 := by
  unfold tailWord_1386687
  simp only [CollatzResearch.WordTrace]
  refine ⟨50576629927277301129926315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33717753284851534086617543 50576629927277301129926315)
  ·
    refine ⟨75864944890915951694889473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50576629927277301129926315 75864944890915951694889473)
    ·
      refine ⟨56898708668186963771167105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75864944890915951694889473 56898708668186963771167105)
      ·
        refine ⟨42674031501140222828375329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56898708668186963771167105 42674031501140222828375329)
        ·
          refine ⟨32005523625855167121281497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42674031501140222828375329 32005523625855167121281497)
          ·
            refine ⟨24004142719391375340961123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32005523625855167121281497 24004142719391375340961123)
            ·
              refine ⟨36006214079087063011441685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24004142719391375340961123 36006214079087063011441685)
              ·
                refine ⟨1687791284957206078661329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36006214079087063011441685 1687791284957206078661329)
                ·
                  refine ⟨1265843463717904558995997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1687791284957206078661329 1265843463717904558995997)
                  ·
                    refine ⟨474691298894214209623499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265843463717904558995997 474691298894214209623499)
                    ·
                      rfl

theorem cell22_1386687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_1386687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386687 prefixEnd_1386687 := by exact prefixLift 1386687
  have htrace : WordTrace (prefixWord ++ tailWord_1386687) baseStart_1386687 baseEnd_1386687 := by
    simpa [prefixWord, tailWord_1386687, baseEnd_1386687] using wordTrace_append hprefix tailTrace_1386687
  have hstable : (prefixWord ++ tailWord_1386687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386687).length < 2 ^ (prefixWord ++ tailWord_1386687).sum := by decide
  have hdescent : baseEnd_1386687 < baseStart_1386687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386717 : List Nat := [1, 4, 3, 2, 1, 1, 2, 8]
def baseStart_1386717 : Nat := 118140960795 + 1386717 * 2 ^ 59
def prefixEnd_1386717 : Nat := 4983230072969 + 3 ^ 40 * 1386717 * 2
def baseEnd_1386717 : Nat := 52744618723033792374823

theorem tailTrace_1386717 : CollatzResearch.WordTrace tailWord_1386717 prefixEnd_1386717 52744618723033792374823 := by
  unfold tailWord_1386717
  simp only [CollatzResearch.WordTrace]
  refine ⟨50577724117168616253518405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33718482744779077502345603 50577724117168616253518405)
  ·
    refine ⟨9483323271969115547534701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50577724117168616253518405 9483323271969115547534701)
    ·
      refine ⟨3556246226988418330325513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9483323271969115547534701 3556246226988418330325513)
      ·
        refine ⟨2667184670241313747744135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3556246226988418330325513 2667184670241313747744135)
        ·
          refine ⟨4000777005361970621616203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667184670241313747744135 4000777005361970621616203)
          ·
            refine ⟨6001165508042955932424305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000777005361970621616203 6001165508042955932424305)
            ·
              refine ⟨4500874131032216949318229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001165508042955932424305 4500874131032216949318229)
              ·
                refine ⟨52744618723033792374823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4500874131032216949318229 52744618723033792374823)
                ·
                  rfl

theorem cell22_1386717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 8].length) (baseStart_1386717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386717 prefixEnd_1386717 := by exact prefixLift 1386717
  have htrace : WordTrace (prefixWord ++ tailWord_1386717) baseStart_1386717 baseEnd_1386717 := by
    simpa [prefixWord, tailWord_1386717, baseEnd_1386717] using wordTrace_append hprefix tailTrace_1386717
  have hstable : (prefixWord ++ tailWord_1386717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386717).length < 2 ^ (prefixWord ++ tailWord_1386717).sum := by decide
  have hdescent : baseEnd_1386717 < baseStart_1386717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386762 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_1386762 : Nat := 118140960795 + 1386762 * 2 ^ 59
def prefixEnd_1386762 : Nat := 4983230072969 + 3 ^ 40 * 1386762 * 2
def baseEnd_1386762 : Nat := 158238990975646337999423

theorem tailTrace_1386762 : CollatzResearch.WordTrace tailWord_1386762 prefixEnd_1386762 158238990975646337999423 := by
  unfold tailWord_1386762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12644841350501397234726635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33719576934670392625937693 12644841350501397234726635)
  ·
    refine ⟨18967262025752095852089953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12644841350501397234726635 18967262025752095852089953)
    ·
      refine ⟨14225446519314071889067465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18967262025752095852089953 14225446519314071889067465)
      ·
        refine ⟨10669084889485553916800599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14225446519314071889067465 10669084889485553916800599)
        ·
          refine ⟨16003627334228330875200899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10669084889485553916800599 16003627334228330875200899)
          ·
            refine ⟨24005441001342496312801349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16003627334228330875200899 24005441001342496312801349)
            ·
              refine ⟨4501020187751718058650253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24005441001342496312801349 4501020187751718058650253)
              ·
                refine ⟨1687882570406894271993845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4501020187751718058650253 1687882570406894271993845)
                ·
                  refine ⟨158238990975646337999423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687882570406894271993845 158238990975646337999423)
                  ·
                    rfl

theorem cell22_1386762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_1386762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386762 prefixEnd_1386762 := by exact prefixLift 1386762
  have htrace : WordTrace (prefixWord ++ tailWord_1386762) baseStart_1386762 baseEnd_1386762 := by
    simpa [prefixWord, tailWord_1386762, baseEnd_1386762] using wordTrace_append hprefix tailTrace_1386762
  have hstable : (prefixWord ++ tailWord_1386762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386762).length < 2 ^ (prefixWord ++ tailWord_1386762).sum := by decide
  have hdescent : baseEnd_1386762 < baseStart_1386762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386858 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_1386858 : Nat := 118140960795 + 1386858 * 2 ^ 59
def prefixEnd_1386858 : Nat := 4983230072969 + 3 ^ 40 * 1386858 * 2
def baseEnd_1386858 : Nat := 158249945229608921199325

theorem tailTrace_1386858 : CollatzResearch.WordTrace tailWord_1386858 prefixEnd_1386858 158249945229608921199325 := by
  unfold tailWord_1386858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12645716702414449333600307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33721911206438531556267485 12645716702414449333600307)
  ·
    refine ⟨18968575053621674000400461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12645716702414449333600307 18968575053621674000400461)
    ·
      refine ⟨7113215645108127750150173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18968575053621674000400461 7113215645108127750150173)
      ·
        refine ⟨2667455866915547906306315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7113215645108127750150173 2667455866915547906306315)
        ·
          refine ⟨4001183800373321859459473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667455866915547906306315 4001183800373321859459473)
          ·
            refine ⟨3000887850279991394594605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001183800373321859459473 3000887850279991394594605)
            ·
              refine ⟨1125332943854996772972977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3000887850279991394594605 1125332943854996772972977)
              ·
                refine ⟨843999707891247579729733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1125332943854996772972977 843999707891247579729733)
                ·
                  refine ⟨158249945229608921199325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843999707891247579729733 158249945229608921199325)
                  ·
                    rfl

theorem cell22_1386858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_1386858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386858 prefixEnd_1386858 := by exact prefixLift 1386858
  have htrace : WordTrace (prefixWord ++ tailWord_1386858) baseStart_1386858 baseEnd_1386858 := by
    simpa [prefixWord, tailWord_1386858, baseEnd_1386858] using wordTrace_append hprefix tailTrace_1386858
  have hstable : (prefixWord ++ tailWord_1386858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386858).length < 2 ^ (prefixWord ++ tailWord_1386858).sum := by decide
  have hdescent : baseEnd_1386858 < baseStart_1386858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386869 : List Nat := [1, 3, 4, 1, 2, 2, 2, 7]
def baseStart_1386869 : Nat := 118140960795 + 1386869 * 2 ^ 59
def prefixEnd_1386869 : Nat := 4983230072969 + 3 ^ 40 * 1386869 * 2
def baseEnd_1386869 : Nat := 52750400134847377952549

theorem tailTrace_1386869 : CollatzResearch.WordTrace tailWord_1386869 prefixEnd_1386869 52750400134847377952549 := by
  unfold tailWord_1386869
  simp only [CollatzResearch.WordTrace]
  refine ⟨50583268012617946213051661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33722178675078630808701107 50583268012617946213051661)
  ·
    refine ⟨18968725504731729829894373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50583268012617946213051661 18968725504731729829894373)
    ·
      refine ⟨3556636032137199343105195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18968725504731729829894373 3556636032137199343105195)
      ·
        refine ⟨5334954048205799014657793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556636032137199343105195 5334954048205799014657793)
        ·
          refine ⟨4001215536154349260993345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5334954048205799014657793 4001215536154349260993345)
          ·
            refine ⟨3000911652115761945745009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001215536154349260993345 3000911652115761945745009)
            ·
              refine ⟨2250683739086821459308757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000911652115761945745009 2250683739086821459308757)
              ·
                refine ⟨52750400134847377952549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2250683739086821459308757 52750400134847377952549)
                ·
                  rfl

theorem cell22_1386869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 7].length) (baseStart_1386869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386869 prefixEnd_1386869 := by exact prefixLift 1386869
  have htrace : WordTrace (prefixWord ++ tailWord_1386869) baseStart_1386869 baseEnd_1386869 := by
    simpa [prefixWord, tailWord_1386869, baseEnd_1386869] using wordTrace_append hprefix tailTrace_1386869
  have hstable : (prefixWord ++ tailWord_1386869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386869).length < 2 ^ (prefixWord ++ tailWord_1386869).sum := by decide
  have hdescent : baseEnd_1386869 < baseStart_1386869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386884 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1386884 : Nat := 118140960795 + 1386884 * 2 ^ 59
def prefixEnd_1386884 : Nat := 4983230072969 + 3 ^ 40 * 1386884 * 2
def baseEnd_1386884 : Nat := 474758736020171362447895

theorem tailTrace_1386884 : CollatzResearch.WordTrace tailWord_1386884 prefixEnd_1386884 474758736020171362447895 := by
  unfold tailWord_1386884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25291907553781801887423853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33722543405042402516565137 25291907553781801887423853)
  ·
    refine ⟨9484465332668175707783945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25291907553781801887423853 9484465332668175707783945)
    ·
      refine ⟨7113348999501131780837959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9484465332668175707783945 7113348999501131780837959)
      ·
        refine ⟨10670023499251697671256939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113348999501131780837959 10670023499251697671256939)
        ·
          refine ⟨16005035248877546506885409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670023499251697671256939 16005035248877546506885409)
          ·
            refine ⟨12003776436658159880164057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16005035248877546506885409 12003776436658159880164057)
            ·
              refine ⟨9002832327493619910123043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12003776436658159880164057 9002832327493619910123043)
              ·
                refine ⟨13504248491240429865184565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9002832327493619910123043 13504248491240429865184565)
                ·
                  refine ⟨1266023296053790299861053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13504248491240429865184565 1266023296053790299861053)
                  ·
                    refine ⟨474758736020171362447895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266023296053790299861053 474758736020171362447895)
                    ·
                      rfl

theorem cell22_1386884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1386884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386884 prefixEnd_1386884 := by exact prefixLift 1386884
  have htrace : WordTrace (prefixWord ++ tailWord_1386884) baseStart_1386884 baseEnd_1386884 := by
    simpa [prefixWord, tailWord_1386884, baseEnd_1386884] using wordTrace_append hprefix tailTrace_1386884
  have hstable : (prefixWord ++ tailWord_1386884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386884).length < 2 ^ (prefixWord ++ tailWord_1386884).sum := by decide
  have hdescent : baseEnd_1386884 < baseStart_1386884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386901 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1386901 : Nat := 118140960795 + 1386901 * 2 ^ 59
def prefixEnd_1386901 : Nat := 4983230072969 + 3 ^ 40 * 1386901 * 2
def baseEnd_1386901 : Nat := 474764555467588984772843

theorem tailTrace_1386901 : CollatzResearch.WordTrace tailWord_1386901 prefixEnd_1386901 474764555467588984772843 := by
  unfold tailWord_1386901
  simp only [CollatzResearch.WordTrace]
  refine ⟨50584435148502015678216557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33722956765668010452144371 50584435148502015678216557)
  ·
    refine ⟨18969163180688255879331209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50584435148502015678216557 18969163180688255879331209)
    ·
      refine ⟨14226872385516191909498407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18969163180688255879331209 14226872385516191909498407)
      ·
        refine ⟨21340308578274287864247611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14226872385516191909498407 21340308578274287864247611)
        ·
          refine ⟨32010462867411431796371417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21340308578274287864247611 32010462867411431796371417)
          ·
            refine ⟨24007847150558573847278563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32010462867411431796371417 24007847150558573847278563)
            ·
              refine ⟨36011770725837860770917845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24007847150558573847278563 36011770725837860770917845)
              ·
                refine ⟨844025876386824861818387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36011770725837860770917845 844025876386824861818387)
                ·
                  refine ⟨1266038814580237292727581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844025876386824861818387 1266038814580237292727581)
                  ·
                    refine ⟨474764555467588984772843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266038814580237292727581 474764555467588984772843)
                    ·
                      rfl

theorem cell22_1386901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1386901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386901 prefixEnd_1386901 := by exact prefixLift 1386901
  have htrace : WordTrace (prefixWord ++ tailWord_1386901) baseStart_1386901 baseEnd_1386901 := by
    simpa [prefixWord, tailWord_1386901, baseEnd_1386901] using wordTrace_append hprefix tailTrace_1386901
  have hstable : (prefixWord ++ tailWord_1386901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386901).length < 2 ^ (prefixWord ++ tailWord_1386901).sum := by decide
  have hdescent : baseEnd_1386901 < baseStart_1386901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386929 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_1386929 : Nat := 118140960795 + 1386929 * 2 ^ 59
def prefixEnd_1386929 : Nat := 4983230072969 + 3 ^ 40 * 1386929 * 2
def baseEnd_1386929 : Nat := 474774140439806245072757

theorem tailTrace_1386929 : CollatzResearch.WordTrace tailWord_1386929 prefixEnd_1386929 474774140439806245072757 := by
  unfold tailWord_1386929
  simp only [CollatzResearch.WordTrace]
  refine ⟨50585456392400576460235841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33723637594933717640157227 50585456392400576460235841)
  ·
    refine ⟨37939092294300432345176881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50585456392400576460235841 37939092294300432345176881)
    ·
      refine ⟨28454319220725324258882661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37939092294300432345176881 28454319220725324258882661)
      ·
        refine ⟨5335184853885998298540499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28454319220725324258882661 5335184853885998298540499)
        ·
          refine ⟨8002777280828997447810749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335184853885998298540499 8002777280828997447810749)
          ·
            refine ⟨3001041480310874042929031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8002777280828997447810749 3001041480310874042929031)
            ·
              refine ⟨4501562220466311064393547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001041480310874042929031 4501562220466311064393547)
              ·
                refine ⟨6752343330699466596590321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501562220466311064393547 6752343330699466596590321)
                ·
                  refine ⟨5064257498024599947442741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752343330699466596590321 5064257498024599947442741)
                  ·
                    refine ⟨474774140439806245072757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5064257498024599947442741 474774140439806245072757)
                    ·
                      rfl

theorem cell22_1386929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_1386929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386929 prefixEnd_1386929 := by exact prefixLift 1386929
  have htrace : WordTrace (prefixWord ++ tailWord_1386929) baseStart_1386929 baseEnd_1386929 := by
    simpa [prefixWord, tailWord_1386929, baseEnd_1386929] using wordTrace_append hprefix tailTrace_1386929
  have hstable : (prefixWord ++ tailWord_1386929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386929).length < 2 ^ (prefixWord ++ tailWord_1386929).sum := by decide
  have hdescent : baseEnd_1386929 < baseStart_1386929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386944 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_1386944 : Nat := 118140960795 + 1386944 * 2 ^ 59
def prefixEnd_1386944 : Nat := 4983230072969 + 3 ^ 40 * 1386944 * 2
def baseEnd_1386944 : Nat := 474779275246351205947711

theorem tailTrace_1386944 : CollatzResearch.WordTrace tailWord_1386944 prefixEnd_1386944 474779275246351205947711 := by
  unfold tailWord_1386944
  simp only [CollatzResearch.WordTrace]
  refine ⟨25293001743673117011015943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33724002324897489348021257 25293001743673117011015943)
  ·
    refine ⟨37939502615509675516523915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25293001743673117011015943 37939502615509675516523915)
    ·
      refine ⟨56909253923264513274785873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37939502615509675516523915 56909253923264513274785873)
      ·
        refine ⟨42681940442448384956089405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56909253923264513274785873 42681940442448384956089405)
        ·
          refine ⟨16005727665918144358533527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42681940442448384956089405 16005727665918144358533527)
          ·
            refine ⟨24008591498877216537800291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16005727665918144358533527 24008591498877216537800291)
            ·
              refine ⟨36012887248315824806700437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24008591498877216537800291 36012887248315824806700437)
              ·
                refine ⟨1688104089764804287814083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36012887248315824806700437 1688104089764804287814083)
                ·
                  refine ⟨2532156134647206431721125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688104089764804287814083 2532156134647206431721125)
                  ·
                    refine ⟨474779275246351205947711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2532156134647206431721125 474779275246351205947711)
                    ·
                      rfl

theorem cell22_1386944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_1386944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386944 prefixEnd_1386944 := by exact prefixLift 1386944
  have htrace : WordTrace (prefixWord ++ tailWord_1386944) baseStart_1386944 baseEnd_1386944 := by
    simpa [prefixWord, tailWord_1386944, baseEnd_1386944] using wordTrace_append hprefix tailTrace_1386944
  have hstable : (prefixWord ++ tailWord_1386944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386944).length < 2 ^ (prefixWord ++ tailWord_1386944).sum := by decide
  have hdescent : baseEnd_1386944 < baseStart_1386944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386987 : List Nat := [1, 1, 1, 1, 2, 3, 4, 9]
def baseStart_1386987 : Nat := 118140960795 + 1386987 * 2 ^ 59
def prefixEnd_1386987 : Nat := 4983230072969 + 3 ^ 40 * 1386987 * 2
def baseEnd_1386987 : Nat := 52754888336123714124731

theorem tailTrace_1386987 : CollatzResearch.WordTrace tailWord_1386987 prefixEnd_1386987 52754888336123714124731 := by
  unfold tailWord_1386987
  simp only [CollatzResearch.WordTrace]
  refine ⟨50587571826190452365847215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33725047884126968243898143 50587571826190452365847215)
  ·
    refine ⟨75881357739285678548770823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50587571826190452365847215 75881357739285678548770823)
    ·
      refine ⟨113822036608928517823156235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75881357739285678548770823 113822036608928517823156235)
      ·
        refine ⟨170733054913392776734734353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113822036608928517823156235 170733054913392776734734353)
        ·
          refine ⟨128049791185044582551050765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170733054913392776734734353 128049791185044582551050765)
          ·
            refine ⟨48018671694391718456644037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128049791185044582551050765 48018671694391718456644037)
            ·
              refine ⟨9003500942698447210620757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48018671694391718456644037 9003500942698447210620757)
              ·
                refine ⟨52754888336123714124731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9003500942698447210620757 52754888336123714124731)
                ·
                  rfl

theorem cell22_1386987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 9].length) (baseStart_1386987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386987 prefixEnd_1386987 := by exact prefixLift 1386987
  have htrace : WordTrace (prefixWord ++ tailWord_1386987) baseStart_1386987 baseEnd_1386987 := by
    simpa [prefixWord, tailWord_1386987, baseEnd_1386987] using wordTrace_append hprefix tailTrace_1386987
  have hstable : (prefixWord ++ tailWord_1386987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386987).length < 2 ^ (prefixWord ++ tailWord_1386987).sum := by decide
  have hdescent : baseEnd_1386987 < baseStart_1386987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387160 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 2, 3]
def baseStart_1387160 : Nat := 118140960795 + 1387160 * 2 ^ 59
def prefixEnd_1387160 : Nat := 4983230072969 + 3 ^ 40 * 1387160 * 2
def baseEnd_1387160 : Nat := 474853216460598642547049

theorem tailTrace_1387160 : CollatzResearch.WordTrace tailWord_1387160 prefixEnd_1387160 474853216460598642547049 := by
  unfold tailWord_1387160
  simp only [CollatzResearch.WordTrace]
  refine ⟨25296940827281851455947467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33729254436375801941263289 25296940827281851455947467)
  ·
    refine ⟨37945411240922777183921201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25296940827281851455947467 37945411240922777183921201)
    ·
      refine ⟨28459058430692082887940901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37945411240922777183921201 28459058430692082887940901)
      ·
        refine ⟨5336073455754765541488919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28459058430692082887940901 5336073455754765541488919)
        ·
          refine ⟨8004110183632148312233379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336073455754765541488919 8004110183632148312233379)
          ·
            refine ⟨12006165275448222468350069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8004110183632148312233379 12006165275448222468350069)
            ·
              refine ⟨1125577994573270856407819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12006165275448222468350069 1125577994573270856407819)
              ·
                refine ⟨1688366991859906284611729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125577994573270856407819 1688366991859906284611729)
                ·
                  refine ⟨1266275243894929713458797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1688366991859906284611729 1266275243894929713458797)
                  ·
                    refine ⟨474853216460598642547049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266275243894929713458797 474853216460598642547049)
                    ·
                      rfl

theorem cell22_1387160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_1387160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387160 prefixEnd_1387160 := by exact prefixLift 1387160
  have htrace : WordTrace (prefixWord ++ tailWord_1387160) baseStart_1387160 baseEnd_1387160 := by
    simpa [prefixWord, tailWord_1387160, baseEnd_1387160] using wordTrace_append hprefix tailTrace_1387160
  have hstable : (prefixWord ++ tailWord_1387160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387160).length < 2 ^ (prefixWord ++ tailWord_1387160).sum := by decide
  have hdescent : baseEnd_1387160 < baseStart_1387160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387171 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 5, 3]
def baseStart_1387171 : Nat := 118140960795 + 1387171 * 2 ^ 59
def prefixEnd_1387171 : Nat := 4983230072969 + 3 ^ 40 * 1387171 * 2
def baseEnd_1387171 : Nat := 474856981985398280522015

theorem tailTrace_1387171 : CollatzResearch.WordTrace tailWord_1387171 prefixEnd_1387171 474856981985398280522015 := by
  unfold tailWord_1387171
  simp only [CollatzResearch.WordTrace]
  refine ⟨50594282857523851790545367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33729521905015901193696911 50594282857523851790545367)
  ·
    refine ⟨75891424286285777685818051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50594282857523851790545367 75891424286285777685818051)
    ·
      refine ⟨113837136429428666528727077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75891424286285777685818051 113837136429428666528727077)
      ·
        refine ⟨21344463080517874974136327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113837136429428666528727077 21344463080517874974136327)
        ·
          refine ⟨32016694620776812461204491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21344463080517874974136327 32016694620776812461204491)
          ·
            refine ⟨48025041931165218691806737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32016694620776812461204491 48025041931165218691806737)
            ·
              refine ⟨36018781448373914018855053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48025041931165218691806737 36018781448373914018855053)
              ·
                refine ⟨13507043043140217757070645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36018781448373914018855053 13507043043140217757070645)
                ·
                  refine ⟨1266285285294395414725373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13507043043140217757070645 1266285285294395414725373)
                  ·
                    refine ⟨474856981985398280522015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266285285294395414725373 474856981985398280522015)
                    ·
                      rfl

theorem cell22_1387171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 3].length) (baseStart_1387171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387171 prefixEnd_1387171 := by exact prefixLift 1387171
  have htrace : WordTrace (prefixWord ++ tailWord_1387171) baseStart_1387171 baseEnd_1387171 := by
    simpa [prefixWord, tailWord_1387171, baseEnd_1387171] using wordTrace_append hprefix tailTrace_1387171
  have hstable : (prefixWord ++ tailWord_1387171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387171).length < 2 ^ (prefixWord ++ tailWord_1387171).sum := by decide
  have hdescent : baseEnd_1387171 < baseStart_1387171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387190 : List Nat := [5, 1, 3, 1, 2, 2, 8]
def baseStart_1387190 : Nat := 118140960795 + 1387190 * 2 ^ 59
def prefixEnd_1387190 : Nat := 4983230072969 + 3 ^ 40 * 1387190 * 2
def baseEnd_1387190 : Nat := 17587536521247724603591

theorem tailTrace_1387190 : CollatzResearch.WordTrace tailWord_1387190 prefixEnd_1387190 17587536521247724603591 := by
  unfold tailWord_1387190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162185990278438627217939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33729983896303345356991349 3162185990278438627217939)
  ·
    refine ⟨4743278985417657940826909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162185990278438627217939 4743278985417657940826909)
    ·
      refine ⟨1778729619531621727810091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4743278985417657940826909 1778729619531621727810091)
      ·
        refine ⟨2668094429297432591715137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778729619531621727810091 2668094429297432591715137)
        ·
          refine ⟨2001070821973074443786353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2668094429297432591715137 2001070821973074443786353)
          ·
            refine ⟨1500803116479805832839765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2001070821973074443786353 1500803116479805832839765)
            ·
              refine ⟨17587536521247724603591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1500803116479805832839765 17587536521247724603591)
              ·
                rfl

theorem cell22_1387190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 8].length) (baseStart_1387190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387190 prefixEnd_1387190 := by exact prefixLift 1387190
  have htrace : WordTrace (prefixWord ++ tailWord_1387190) baseStart_1387190 baseEnd_1387190 := by
    simpa [prefixWord, tailWord_1387190, baseEnd_1387190] using wordTrace_append hprefix tailTrace_1387190
  have hstable : (prefixWord ++ tailWord_1387190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387190).length < 2 ^ (prefixWord ++ tailWord_1387190).sum := by decide
  have hdescent : baseEnd_1387190 < baseStart_1387190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387261 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1387261 : Nat := 118140960795 + 1387261 * 2 ^ 59
def prefixEnd_1387261 : Nat := 4983230072969 + 3 ^ 40 * 1387261 * 2
def baseEnd_1387261 : Nat := 474887790824668045771739

theorem tailTrace_1387261 : CollatzResearch.WordTrace tailWord_1387261 prefixEnd_1387261 474887790824668045771739 := by
  unfold tailWord_1387261
  simp only [CollatzResearch.WordTrace]
  refine ⟨50597565427197797161321637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33731710284798531440881091 50597565427197797161321637)
  ·
    refine ⟨9487043517599586967747807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50597565427197797161321637 9487043517599586967747807)
    ·
      refine ⟨14230565276399380451621711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9487043517599586967747807 14230565276399380451621711)
      ·
        refine ⟨21345847914599070677432567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14230565276399380451621711 21345847914599070677432567)
        ·
          refine ⟨32018771871898606016148851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21345847914599070677432567 32018771871898606016148851)
          ·
            refine ⟨48028157807847909024223277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32018771871898606016148851 48028157807847909024223277)
            ·
              refine ⟨18010559177942965884083729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48028157807847909024223277 18010559177942965884083729)
              ·
                refine ⟨13507919383457224413062797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18010559177942965884083729 13507919383457224413062797)
                ·
                  refine ⟨5065469768796459154898549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13507919383457224413062797 5065469768796459154898549)
                  ·
                    refine ⟨474887790824668045771739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5065469768796459154898549 474887790824668045771739)
                    ·
                      rfl

theorem cell22_1387261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1387261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387261 prefixEnd_1387261 := by exact prefixLift 1387261
  have htrace : WordTrace (prefixWord ++ tailWord_1387261) baseStart_1387261 baseEnd_1387261 := by
    simpa [prefixWord, tailWord_1387261, baseEnd_1387261] using wordTrace_append hprefix tailTrace_1387261
  have hstable : (prefixWord ++ tailWord_1387261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387261).length < 2 ^ (prefixWord ++ tailWord_1387261).sum := by decide
  have hdescent : baseEnd_1387261 < baseStart_1387261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387276 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1387276 : Nat := 118140960795 + 1387276 * 2 ^ 59
def prefixEnd_1387276 : Nat := 4983230072969 + 3 ^ 40 * 1387276 * 2
def baseEnd_1387276 : Nat := 474892925631213006646693

theorem tailTrace_1387276 : CollatzResearch.WordTrace tailWord_1387276 prefixEnd_1387276 474892925631213006646693 := by
  unfold tailWord_1387276
  simp only [CollatzResearch.WordTrace]
  refine ⟨25299056261071727361558841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33732075014762303148745121 25299056261071727361558841)
  ·
    refine ⟨18974292195803795521169131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25299056261071727361558841 18974292195803795521169131)
    ·
      refine ⟨28461438293705693281753697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18974292195803795521169131 28461438293705693281753697)
      ·
        refine ⟨21346078720279269961315273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28461438293705693281753697 21346078720279269961315273)
        ·
          refine ⟨16009559040209452470986455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21346078720279269961315273 16009559040209452470986455)
          ·
            refine ⟨24014338560314178706479683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16009559040209452470986455 24014338560314178706479683)
            ·
              refine ⟨36021507840471268059719525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24014338560314178706479683 36021507840471268059719525)
              ·
                refine ⟨6754032720088362761197411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36021507840471268059719525 6754032720088362761197411)
                ·
                  refine ⟨10131049080132544141796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754032720088362761197411 10131049080132544141796117)
                  ·
                    refine ⟨474892925631213006646693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10131049080132544141796117 474892925631213006646693)
                    ·
                      rfl

theorem cell22_1387276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1387276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387276 prefixEnd_1387276 := by exact prefixLift 1387276
  have htrace : WordTrace (prefixWord ++ tailWord_1387276) baseStart_1387276 baseEnd_1387276 := by
    simpa [prefixWord, tailWord_1387276, baseEnd_1387276] using wordTrace_append hprefix tailTrace_1387276
  have hstable : (prefixWord ++ tailWord_1387276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387276).length < 2 ^ (prefixWord ++ tailWord_1387276).sum := by decide
  have hdescent : baseEnd_1387276 < baseStart_1387276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387278 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_1387278 : Nat := 118140960795 + 1387278 * 2 ^ 59
def prefixEnd_1387278 : Nat := 4983230072969 + 3 ^ 40 * 1387278 * 2
def baseEnd_1387278 : Nat := 474893610272085668096687

theorem tailTrace_1387278 : CollatzResearch.WordTrace tailWord_1387278 prefixEnd_1387278 474893610272085668096687 := by
  unfold tailWord_1387278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324773183517026133086311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33732123645424139376460325 6324773183517026133086311)
  ·
    refine ⟨9487159775275539199629467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6324773183517026133086311 9487159775275539199629467)
    ·
      refine ⟨14230739662913308799444201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9487159775275539199629467 14230739662913308799444201)
      ·
        refine ⟨10673054747184981599583151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14230739662913308799444201 10673054747184981599583151)
        ·
          refine ⟨16009582120777472399374727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10673054747184981599583151 16009582120777472399374727)
          ·
            refine ⟨24014373181166208599062091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16009582120777472399374727 24014373181166208599062091)
            ·
              refine ⟨36021559771749312898593137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24014373181166208599062091 36021559771749312898593137)
              ·
                refine ⟨27016169828811984673944853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36021559771749312898593137 27016169828811984673944853)
                ·
                  refine ⟨1266382960725561781591165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27016169828811984673944853 1266382960725561781591165)
                  ·
                    refine ⟨474893610272085668096687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266382960725561781591165 474893610272085668096687)
                    ·
                      rfl

theorem cell22_1387278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1387278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387278 prefixEnd_1387278 := by exact prefixLift 1387278
  have htrace : WordTrace (prefixWord ++ tailWord_1387278) baseStart_1387278 baseEnd_1387278 := by
    simpa [prefixWord, tailWord_1387278, baseEnd_1387278] using wordTrace_append hprefix tailTrace_1387278
  have hstable : (prefixWord ++ tailWord_1387278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387278).length < 2 ^ (prefixWord ++ tailWord_1387278).sum := by decide
  have hdescent : baseEnd_1387278 < baseStart_1387278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387329 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1387329 : Nat := 118140960795 + 1387329 * 2 ^ 59
def prefixEnd_1387329 : Nat := 4983230072969 + 3 ^ 40 * 1387329 * 2
def baseEnd_1387329 : Nat := 474911068614338535071531

theorem tailTrace_1387329 : CollatzResearch.WordTrace tailWord_1387329 prefixEnd_1387329 474911068614338535071531 := by
  unfold tailWord_1387329
  simp only [CollatzResearch.WordTrace]
  refine ⟨50600045590951444774797041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33733363727300963183198027 50600045590951444774797041)
  ·
    refine ⟨37950034193213583581097781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50600045590951444774797041 37950034193213583581097781)
    ·
      refine ⟨3557815705613773460727917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37950034193213583581097781 3557815705613773460727917)
      ·
        refine ⟨1334180889605165047772969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3557815705613773460727917 1334180889605165047772969)
        ·
          refine ⟨1000635667203873785829727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1334180889605165047772969 1000635667203873785829727)
          ·
            refine ⟨1500953500805810678744591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000635667203873785829727 1500953500805810678744591)
            ·
              refine ⟨2251430251208716018116887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500953500805810678744591 2251430251208716018116887)
              ·
                refine ⟨3377145376813074027175331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251430251208716018116887 3377145376813074027175331)
                ·
                  refine ⟨5065718065219611040762997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377145376813074027175331 5065718065219611040762997)
                  ·
                    refine ⟨474911068614338535071531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5065718065219611040762997 474911068614338535071531)
                    ·
                      rfl

theorem cell22_1387329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1387329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387329 prefixEnd_1387329 := by exact prefixLift 1387329
  have htrace : WordTrace (prefixWord ++ tailWord_1387329) baseStart_1387329 baseEnd_1387329 := by
    simpa [prefixWord, tailWord_1387329, baseEnd_1387329] using wordTrace_append hprefix tailTrace_1387329
  have hstable : (prefixWord ++ tailWord_1387329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387329).length < 2 ^ (prefixWord ++ tailWord_1387329).sum := by decide
  have hdescent : baseEnd_1387329 < baseStart_1387329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387340 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_1387340 : Nat := 118140960795 + 1387340 * 2 ^ 59
def prefixEnd_1387340 : Nat := 4983230072969 + 3 ^ 40 * 1387340 * 2
def baseEnd_1387340 : Nat := 474914834139138173046497

theorem tailTrace_1387340 : CollatzResearch.WordTrace tailWord_1387340 prefixEnd_1387340 474914834139138173046497 := by
  unfold tailWord_1387340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25300223396955796826723737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33733631195941062435631649 25300223396955796826723737)
  ·
    refine ⟨18975167547716847620042803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25300223396955796826723737 18975167547716847620042803)
    ·
      refine ⟨28462751321575271430064205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18975167547716847620042803 28462751321575271430064205)
      ·
        refine ⟨10673531745590726786274077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28462751321575271430064205 10673531745590726786274077)
        ·
          refine ⟨4002574404596522544852779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10673531745590726786274077 4002574404596522544852779)
          ·
            refine ⟨6003861606894783817279169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002574404596522544852779 6003861606894783817279169)
            ·
              refine ⟨4502896205171087862959377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6003861606894783817279169 4502896205171087862959377)
              ·
                refine ⟨3377172153878315897219533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502896205171087862959377 3377172153878315897219533)
                ·
                  refine ⟨1266439557704368461457325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3377172153878315897219533 1266439557704368461457325)
                  ·
                    refine ⟨474914834139138173046497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266439557704368461457325 474914834139138173046497)
                    ·
                      rfl

theorem cell22_1387340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_1387340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387340 prefixEnd_1387340 := by exact prefixLift 1387340
  have htrace : WordTrace (prefixWord ++ tailWord_1387340) baseStart_1387340 baseEnd_1387340 := by
    simpa [prefixWord, tailWord_1387340, baseEnd_1387340] using wordTrace_append hprefix tailTrace_1387340
  have hstable : (prefixWord ++ tailWord_1387340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387340).length < 2 ^ (prefixWord ++ tailWord_1387340).sum := by decide
  have hdescent : baseEnd_1387340 < baseStart_1387340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387374 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1387374 : Nat := 118140960795 + 1387374 * 2 ^ 59
def prefixEnd_1387374 : Nat := 4983230072969 + 3 ^ 40 * 1387374 * 2
def baseEnd_1387374 : Nat := 474926473033973417696393

theorem tailTrace_1387374 : CollatzResearch.WordTrace tailWord_1387374 prefixEnd_1387374 474926473033973417696393 := by
  unfold tailWord_1387374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325210859473552182523147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33734457917192278306790117 6325210859473552182523147)
  ·
    refine ⟨9487816289210328273784721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6325210859473552182523147 9487816289210328273784721)
    ·
      refine ⟨7115862216907746205338541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9487816289210328273784721 7115862216907746205338541)
      ·
        refine ⟨2668448331340404827001953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7115862216907746205338541 2668448331340404827001953)
        ·
          refine ⟨2001336248505303620251465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2668448331340404827001953 2001336248505303620251465)
          ·
            refine ⟨1501002186378977715188599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2001336248505303620251465 1501002186378977715188599)
            ·
              refine ⟨2251503279568466572782899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501002186378977715188599 2251503279568466572782899)
              ·
                refine ⟨3377254919352699859174349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251503279568466572782899 3377254919352699859174349)
                ·
                  refine ⟨1266470594757262447190381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3377254919352699859174349 1266470594757262447190381)
                  ·
                    refine ⟨474926473033973417696393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266470594757262447190381 474926473033973417696393)
                    ·
                      rfl

theorem cell22_1387374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1387374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387374 prefixEnd_1387374 := by exact prefixLift 1387374
  have htrace : WordTrace (prefixWord ++ tailWord_1387374) baseStart_1387374 baseEnd_1387374 := by
    simpa [prefixWord, tailWord_1387374, baseEnd_1387374] using wordTrace_append hprefix tailTrace_1387374
  have hstable : (prefixWord ++ tailWord_1387374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387374).length < 2 ^ (prefixWord ++ tailWord_1387374).sum := by decide
  have hdescent : baseEnd_1387374 < baseStart_1387374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387400 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1387400 : Nat := 118140960795 + 1387400 * 2 ^ 59
def prefixEnd_1387400 : Nat := 4983230072969 + 3 ^ 40 * 1387400 * 2
def baseEnd_1387400 : Nat := 474935373365318016546313

theorem tailTrace_1387400 : CollatzResearch.WordTrace tailWord_1387400 prefixEnd_1387400 474935373365318016546313 := by
  unfold tailWord_1387400
  simp only [CollatzResearch.WordTrace]
  refine ⟨25301317586847111950315827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33735090115796149267087769 25301317586847111950315827)
  ·
    refine ⟨37951976380270667925473741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25301317586847111950315827 37951976380270667925473741)
    ·
      refine ⟨14231991142601500472052653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37951976380270667925473741 14231991142601500472052653)
      ·
        refine ⟨5336996678475562677019745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14231991142601500472052653 5336996678475562677019745)
        ·
          refine ⟨4002747508856672007764809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5336996678475562677019745 4002747508856672007764809)
          ·
            refine ⟨3002060631642504005823607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002747508856672007764809 3002060631642504005823607)
            ·
              refine ⟨4503090947463756008735411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002060631642504005823607 4503090947463756008735411)
              ·
                refine ⟨6754636421195634013103117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503090947463756008735411 6754636421195634013103117)
                ·
                  refine ⟨2532988657948362754913669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6754636421195634013103117 2532988657948362754913669)
                  ·
                    refine ⟨474935373365318016546313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2532988657948362754913669 474935373365318016546313)
                    ·
                      rfl

theorem cell22_1387400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1387400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387400 prefixEnd_1387400 := by exact prefixLift 1387400
  have htrace : WordTrace (prefixWord ++ tailWord_1387400) baseStart_1387400 baseEnd_1387400 := by
    simpa [prefixWord, tailWord_1387400, baseEnd_1387400] using wordTrace_append hprefix tailTrace_1387400
  have hstable : (prefixWord ++ tailWord_1387400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387400).length < 2 ^ (prefixWord ++ tailWord_1387400).sum := by decide
  have hdescent : baseEnd_1387400 < baseStart_1387400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387413 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1387413 : Nat := 118140960795 + 1387413 * 2 ^ 59
def prefixEnd_1387413 : Nat := 4983230072969 + 3 ^ 40 * 1387413 * 2
def baseEnd_1387413 : Nat := 474939823530990315971273

theorem tailTrace_1387413 : CollatzResearch.WordTrace tailWord_1387413 prefixEnd_1387413 474939823530990315971273 := by
  unfold tailWord_1387413
  simp only [CollatzResearch.WordTrace]
  refine ⟨50603109322647127120854893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33735406215098084747236595 50603109322647127120854893)
  ·
    refine ⟨18976165995992672670320585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50603109322647127120854893 18976165995992672670320585)
    ·
      refine ⟨14232124496994504502740439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18976165995992672670320585 14232124496994504502740439)
      ·
        refine ⟨21348186745491756754110659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14232124496994504502740439 21348186745491756754110659)
        ·
          refine ⟨32022280118237635131165989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21348186745491756754110659 32022280118237635131165989)
          ·
            refine ⟨6004177522169556587093623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32022280118237635131165989 6004177522169556587093623)
            ·
              refine ⟨9006266283254334880640435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004177522169556587093623 9006266283254334880640435)
              ·
                refine ⟨13509399424881502320960653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9006266283254334880640435 13509399424881502320960653)
                ·
                  refine ⟨5066024784330563370360245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13509399424881502320960653 5066024784330563370360245)
                  ·
                    refine ⟨474939823530990315971273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5066024784330563370360245 474939823530990315971273)
                    ·
                      rfl

theorem cell22_1387413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1387413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387413 prefixEnd_1387413 := by exact prefixLift 1387413
  have htrace : WordTrace (prefixWord ++ tailWord_1387413) baseStart_1387413 baseEnd_1387413 := by
    simpa [prefixWord, tailWord_1387413, baseEnd_1387413] using wordTrace_append hprefix tailTrace_1387413
  have hstable : (prefixWord ++ tailWord_1387413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387413).length < 2 ^ (prefixWord ++ tailWord_1387413).sum := by decide
  have hdescent : baseEnd_1387413 < baseStart_1387413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387415 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 4]
def baseStart_1387415 : Nat := 118140960795 + 1387415 * 2 ^ 59
def prefixEnd_1387415 : Nat := 4983230072969 + 3 ^ 40 * 1387415 * 2
def baseEnd_1387415 : Nat := 158313502723954325807089

theorem tailTrace_1387415 : CollatzResearch.WordTrace tailWord_1387415 prefixEnd_1387415 158313502723954325807089 := by
  unfold tailWord_1387415
  simp only [CollatzResearch.WordTrace]
  refine ⟨50603182268639881462427699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33735454845759920974951799 50603182268639881462427699)
  ·
    refine ⟨75904773402959822193641549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50603182268639881462427699 75904773402959822193641549)
    ·
      refine ⟨28464290026109933322615581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75904773402959822193641549 28464290026109933322615581)
      ·
        refine ⟨10674108759791224995980843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28464290026109933322615581 10674108759791224995980843)
        ·
          refine ⟨16011163139686837493971265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10674108759791224995980843 16011163139686837493971265)
          ·
            refine ⟨12008372354765128120478449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16011163139686837493971265 12008372354765128120478449)
            ·
              refine ⟨9006279266073846090358837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12008372354765128120478449 9006279266073846090358837)
              ·
                refine ⟨844338681194423070971141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9006279266073846090358837 844338681194423070971141)
                ·
                  refine ⟨158313502723954325807089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 844338681194423070971141 158313502723954325807089)
                  ·
                    rfl

theorem cell22_1387415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 4].length) (baseStart_1387415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387415 prefixEnd_1387415 := by exact prefixLift 1387415
  have htrace : WordTrace (prefixWord ++ tailWord_1387415) baseStart_1387415 baseEnd_1387415 := by
    simpa [prefixWord, tailWord_1387415, baseEnd_1387415] using wordTrace_append hprefix tailTrace_1387415
  have hstable : (prefixWord ++ tailWord_1387415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387415).length < 2 ^ (prefixWord ++ tailWord_1387415).sum := by decide
  have hdescent : baseEnd_1387415 < baseStart_1387415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387582 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1387582 : Nat := 118140960795 + 1387582 * 2 ^ 59
def prefixEnd_1387582 : Nat := 4983230072969 + 3 ^ 40 * 1387582 * 2
def baseEnd_1387582 : Nat := 474997675684730208495755

theorem tailTrace_1387582 : CollatzResearch.WordTrace tailWord_1387582 prefixEnd_1387582 474997675684730208495755 := by
  unfold tailWord_1387582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326159157379358622969625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33739515506023245989171333 6326159157379358622969625)
  ·
    refine ⟨4744619368034518967227219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6326159157379358622969625 4744619368034518967227219)
    ·
      refine ⟨7116929052051778450840829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4744619368034518967227219 7116929052051778450840829)
      ·
        refine ⟨2668848394519416919065311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7116929052051778450840829 2668848394519416919065311)
        ·
          refine ⟨4003272591779125378597967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668848394519416919065311 4003272591779125378597967)
          ·
            refine ⟨6004908887668688067896951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003272591779125378597967 6004908887668688067896951)
            ·
              refine ⟨9007363331503032101845427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004908887668688067896951 9007363331503032101845427)
              ·
                refine ⟨13511044997254548152768141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007363331503032101845427 13511044997254548152768141)
                ·
                  refine ⟨5066641873970455557288053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13511044997254548152768141 5066641873970455557288053)
                  ·
                    refine ⟨474997675684730208495755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5066641873970455557288053 474997675684730208495755)
                    ·
                      rfl

theorem cell22_1387582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1387582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387582 prefixEnd_1387582 := by exact prefixLift 1387582
  have htrace : WordTrace (prefixWord ++ tailWord_1387582) baseStart_1387582 baseEnd_1387582 := by
    simpa [prefixWord, tailWord_1387582, baseEnd_1387582] using wordTrace_append hprefix tailTrace_1387582
  have hstable : (prefixWord ++ tailWord_1387582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387582).length < 2 ^ (prefixWord ++ tailWord_1387582).sum := by decide
  have hdescent : baseEnd_1387582 < baseStart_1387582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387646 : List Nat := [4, 2, 4, 1, 1, 1, 9]
def baseStart_1387646 : Nat := 118140960795 + 1387646 * 2 ^ 59
def prefixEnd_1387646 : Nat := 4983230072969 + 3 ^ 40 * 1387646 * 2
def baseEnd_1387646 : Nat := 17593317933061310181317

theorem tailTrace_1387646 : CollatzResearch.WordTrace tailWord_1387646 prefixEnd_1387646 17593317933061310181317 := by
  unfold tailWord_1387646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326450941350375989260849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33741071687202005276057861 6326450941350375989260849)
  ·
    refine ⟨4744838206012781991945637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6326450941350375989260849 4744838206012781991945637)
    ·
      refine ⟨889657163627396623489807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4744838206012781991945637 889657163627396623489807)
      ·
        refine ⟨1334485745441094935234711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889657163627396623489807 1334485745441094935234711)
        ·
          refine ⟨2001728618161642402852067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334485745441094935234711 2001728618161642402852067)
          ·
            refine ⟨3002592927242463604278101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001728618161642402852067 3002592927242463604278101)
            ·
              refine ⟨17593317933061310181317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3002592927242463604278101 17593317933061310181317)
              ·
                rfl

theorem cell22_1387646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 9].length) (baseStart_1387646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387646 prefixEnd_1387646 := by exact prefixLift 1387646
  have htrace : WordTrace (prefixWord ++ tailWord_1387646) baseStart_1387646 baseEnd_1387646 := by
    simpa [prefixWord, tailWord_1387646, baseEnd_1387646] using wordTrace_append hprefix tailTrace_1387646
  have hstable : (prefixWord ++ tailWord_1387646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387646).length < 2 ^ (prefixWord ++ tailWord_1387646).sum := by decide
  have hdescent : baseEnd_1387646 < baseStart_1387646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387657 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 5]
def baseStart_1387657 : Nat := 118140960795 + 1387657 * 2 ^ 59
def prefixEnd_1387657 : Nat := 4983230072969 + 3 ^ 40 * 1387657 * 2
def baseEnd_1387657 : Nat := 158341116572485004290175

theorem tailTrace_1387657 : CollatzResearch.WordTrace tailWord_1387657 prefixEnd_1387657 158341116572485004290175 := by
  unfold tailWord_1387657
  simp only [CollatzResearch.WordTrace]
  refine ⟨50612008733763156792737225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33741339155842104528491483 50612008733763156792737225)
  ·
    refine ⟨37959006550322367594552919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50612008733763156792737225 37959006550322367594552919)
    ·
      refine ⟨56938509825483551391829379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37959006550322367594552919 56938509825483551391829379)
      ·
        refine ⟨85407764738225327087744069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56938509825483551391829379 85407764738225327087744069)
        ·
          refine ⟨16013955888417248828952013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85407764738225327087744069 16013955888417248828952013)
          ·
            refine ⟨6005233458156468310857005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16013955888417248828952013 6005233458156468310857005)
            ·
              refine ⟨2251962546808675616571377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6005233458156468310857005 2251962546808675616571377)
              ·
                refine ⟨1688971910106506712428533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251962546808675616571377 1688971910106506712428533)
                ·
                  refine ⟨158341116572485004290175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1688971910106506712428533 158341116572485004290175)
                  ·
                    rfl

theorem cell22_1387657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_1387657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387657 prefixEnd_1387657 := by exact prefixLift 1387657
  have htrace : WordTrace (prefixWord ++ tailWord_1387657) baseStart_1387657 baseEnd_1387657 := by
    simpa [prefixWord, tailWord_1387657, baseEnd_1387657] using wordTrace_append hprefix tailTrace_1387657
  have hstable : (prefixWord ++ tailWord_1387657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387657).length < 2 ^ (prefixWord ++ tailWord_1387657).sum := by decide
  have hdescent : baseEnd_1387657 < baseStart_1387657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387672 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_1387672 : Nat := 118140960795 + 1387672 * 2 ^ 59
def prefixEnd_1387672 : Nat := 4983230072969 + 3 ^ 40 * 1387672 * 2
def baseEnd_1387672 : Nat := 475028484523999973745479

theorem tailTrace_1387672 : CollatzResearch.WordTrace tailWord_1387672 prefixEnd_1387672 475028484523999973745479 := by
  unfold tailWord_1387672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25306277914354407177266635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33741703885805876236355513 25306277914354407177266635)
  ·
    refine ⟨37959416871531610765899953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25306277914354407177266635 37959416871531610765899953)
    ·
      refine ⟨28469562653648708074424965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37959416871531610765899953 28469562653648708074424965)
      ·
        refine ⟨5338042997559132763954681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28469562653648708074424965 5338042997559132763954681)
        ·
          refine ⟨4003532248169349572966011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5338042997559132763954681 4003532248169349572966011)
          ·
            refine ⟨6005298372254024359449017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003532248169349572966011 6005298372254024359449017)
            ·
              refine ⟨4503973779190518269586763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6005298372254024359449017 4503973779190518269586763)
              ·
                refine ⟨6755960668785777404380145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503973779190518269586763 6755960668785777404380145)
                ·
                  refine ⟨5066970501589333053285109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6755960668785777404380145 5066970501589333053285109)
                  ·
                    refine ⟨475028484523999973745479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5066970501589333053285109 475028484523999973745479)
                    ·
                      rfl

theorem cell22_1387672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_1387672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387672 prefixEnd_1387672 := by exact prefixLift 1387672
  have htrace : WordTrace (prefixWord ++ tailWord_1387672) baseStart_1387672 baseEnd_1387672 := by
    simpa [prefixWord, tailWord_1387672, baseEnd_1387672] using wordTrace_append hprefix tailTrace_1387672
  have hstable : (prefixWord ++ tailWord_1387672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387672).length < 2 ^ (prefixWord ++ tailWord_1387672).sum := by decide
  have hdescent : baseEnd_1387672 < baseStart_1387672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387715 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_1387715 : Nat := 118140960795 + 1387715 * 2 ^ 59
def prefixEnd_1387715 : Nat := 4983230072969 + 3 ^ 40 * 1387715 * 2
def baseEnd_1387715 : Nat := 475043204302762194920347

theorem tailTrace_1387715 : CollatzResearch.WordTrace tailWord_1387715 prefixEnd_1387715 475043204302762194920347 := by
  unfold tailWord_1387715
  simp only [CollatzResearch.WordTrace]
  refine ⟨50614124167553032698348599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33742749445035355132232399 50614124167553032698348599)
  ·
    refine ⟨75921186251329549047522899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50614124167553032698348599 75921186251329549047522899)
    ·
      refine ⟨113881779376994323571284349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75921186251329549047522899 113881779376994323571284349)
      ·
        refine ⟨42705667266372871339231631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113881779376994323571284349 42705667266372871339231631)
        ·
          refine ⟨64058500899559307008847447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42705667266372871339231631 64058500899559307008847447)
          ·
            refine ⟨96087751349338960513271171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64058500899559307008847447 96087751349338960513271171)
            ·
              refine ⟨144131627024008440769906757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96087751349338960513271171 144131627024008440769906757)
              ·
                refine ⟨27024680067001582644357517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144131627024008440769906757 27024680067001582644357517)
                ·
                  refine ⟨10134255025125593491634069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27024680067001582644357517 10134255025125593491634069)
                  ·
                    refine ⟨475043204302762194920347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10134255025125593491634069 475043204302762194920347)
                    ·
                      rfl

theorem cell22_1387715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_1387715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387715 prefixEnd_1387715 := by exact prefixLift 1387715
  have htrace : WordTrace (prefixWord ++ tailWord_1387715) baseStart_1387715 baseEnd_1387715 := by
    simpa [prefixWord, tailWord_1387715, baseEnd_1387715] using wordTrace_append hprefix tailTrace_1387715
  have hstable : (prefixWord ++ tailWord_1387715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387715).length < 2 ^ (prefixWord ++ tailWord_1387715).sum := by decide
  have hdescent : baseEnd_1387715 < baseStart_1387715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387725 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1387725 : Nat := 118140960795 + 1387725 * 2 ^ 59
def prefixEnd_1387725 : Nat := 4983230072969 + 3 ^ 40 * 1387725 * 2
def baseEnd_1387725 : Nat := 158348875835708500723439

theorem tailTrace_1387725 : CollatzResearch.WordTrace tailWord_1387725 prefixEnd_1387725 158348875835708500723439 := by
  unfold tailWord_1387725
  simp only [CollatzResearch.WordTrace]
  refine ⟨50614488897516804406212629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33742992598344536270808419 50614488897516804406212629)
  ·
    refine ⟨2372554167071100206541217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50614488897516804406212629 2372554167071100206541217)
    ·
      refine ⟨1779415625303325154905913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2372554167071100206541217 1779415625303325154905913)
      ·
        refine ⟨1334561718977493866179435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1779415625303325154905913 1334561718977493866179435)
        ·
          refine ⟨2001842578466240799269153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334561718977493866179435 2001842578466240799269153)
          ·
            refine ⟨1501381933849680599451865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2001842578466240799269153 1501381933849680599451865)
            ·
              refine ⟨1126036450387260449588899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1501381933849680599451865 1126036450387260449588899)
              ·
                refine ⟨1689054675580890674383349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126036450387260449588899 1689054675580890674383349)
                ·
                  refine ⟨158348875835708500723439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1689054675580890674383349 158348875835708500723439)
                  ·
                    rfl

theorem cell22_1387725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1387725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387725 prefixEnd_1387725 := by exact prefixLift 1387725
  have htrace : WordTrace (prefixWord ++ tailWord_1387725) baseStart_1387725 baseEnd_1387725 := by
    simpa [prefixWord, tailWord_1387725, baseEnd_1387725] using wordTrace_append hprefix tailTrace_1387725
  have hstable : (prefixWord ++ tailWord_1387725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387725).length < 2 ^ (prefixWord ++ tailWord_1387725).sum := by decide
  have hdescent : baseEnd_1387725 < baseStart_1387725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387777 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1387777 : Nat := 118140960795 + 1387777 * 2 ^ 59
def prefixEnd_1387777 : Nat := 4983230072969 + 3 ^ 40 * 1387777 * 2
def baseEnd_1387777 : Nat := 475064428169814699870157

theorem tailTrace_1387777 : CollatzResearch.WordTrace tailWord_1387777 prefixEnd_1387777 475064428169814699870157 := by
  unfold tailWord_1387777
  simp only [CollatzResearch.WordTrace]
  refine ⟨50616385493328417287105585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33744256995552278191403723 50616385493328417287105585)
  ·
    refine ⟨37962289119996312965329189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50616385493328417287105585 37962289119996312965329189)
    ·
      refine ⟨7117929209999308680999223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37962289119996312965329189 7117929209999308680999223)
      ·
        refine ⟨10676893814998963021498835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7117929209999308680999223 10676893814998963021498835)
        ·
          refine ⟨16015340722498444532248253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10676893814998963021498835 16015340722498444532248253)
          ·
            refine ⟨6005752770936916699593095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16015340722498444532248253 6005752770936916699593095)
            ·
              refine ⟨9008629156405375049389643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005752770936916699593095 9008629156405375049389643)
              ·
                refine ⟨13512943734608062574084465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9008629156405375049389643 13512943734608062574084465)
                ·
                  refine ⟨10134707800956046930563349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13512943734608062574084465 10134707800956046930563349)
                  ·
                    refine ⟨475064428169814699870157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10134707800956046930563349 475064428169814699870157)
                    ·
                      rfl

theorem cell22_1387777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1387777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387777 prefixEnd_1387777 := by exact prefixLift 1387777
  have htrace : WordTrace (prefixWord ++ tailWord_1387777) baseStart_1387777 baseEnd_1387777 := by
    simpa [prefixWord, tailWord_1387777, baseEnd_1387777] using wordTrace_append hprefix tailTrace_1387777
  have hstable : (prefixWord ++ tailWord_1387777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387777).length < 2 ^ (prefixWord ++ tailWord_1387777).sum := by decide
  have hdescent : baseEnd_1387777 < baseStart_1387777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387813 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_1387813 : Nat := 118140960795 + 1387813 * 2 ^ 59
def prefixEnd_1387813 : Nat := 4983230072969 + 3 ^ 40 * 1387813 * 2
def baseEnd_1387813 : Nat := 475076751705522605970047

theorem tailTrace_1387813 : CollatzResearch.WordTrace tailWord_1387813 prefixEnd_1387813 475076751705522605970047 := by
  unfold tailWord_1387813
  simp only [CollatzResearch.WordTrace]
  refine ⟨50617698521197995435416093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33745132347465330290277395 50617698521197995435416093)
  ·
    refine ⟨18981636945449248288281035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50617698521197995435416093 18981636945449248288281035)
    ·
      refine ⟨28472455418173872432421553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18981636945449248288281035 28472455418173872432421553)
      ·
        refine ⟨21354341563630404324316165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28472455418173872432421553 21354341563630404324316165)
        ·
          refine ⟨4003939043180700810809281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21354341563630404324316165 4003939043180700810809281)
          ·
            refine ⟨3002954282385525608106961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4003939043180700810809281 3002954282385525608106961)
            ·
              refine ⟨2252215711789144206080221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002954282385525608106961 2252215711789144206080221)
              ·
                refine ⟨844580891920929077280083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2252215711789144206080221 844580891920929077280083)
                ·
                  refine ⟨1266871337881393615920125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844580891920929077280083 1266871337881393615920125)
                  ·
                    refine ⟨475076751705522605970047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266871337881393615920125 475076751705522605970047)
                    ·
                      rfl

theorem cell22_1387813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_1387813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387813 prefixEnd_1387813 := by exact prefixLift 1387813
  have htrace : WordTrace (prefixWord ++ tailWord_1387813) baseStart_1387813 baseEnd_1387813 := by
    simpa [prefixWord, tailWord_1387813, baseEnd_1387813] using wordTrace_append hprefix tailTrace_1387813
  have hstable : (prefixWord ++ tailWord_1387813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387813).length < 2 ^ (prefixWord ++ tailWord_1387813).sum := by decide
  have hdescent : baseEnd_1387813 < baseStart_1387813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387826 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1387826 : Nat := 118140960795 + 1387826 * 2 ^ 59
def prefixEnd_1387826 : Nat := 4983230072969 + 3 ^ 40 * 1387826 * 2
def baseEnd_1387826 : Nat := 158360400623731635131669

theorem tailTrace_1387826 : CollatzResearch.WordTrace tailWord_1387826 prefixEnd_1387826 158360400623731635131669 := by
  unfold tailWord_1387826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654543167537724663909833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33745448446767265770426221 12654543167537724663909833)
  ·
    refine ⟨9490907375653293497932375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12654543167537724663909833 9490907375653293497932375)
    ·
      refine ⟨14236361063479940246898563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9490907375653293497932375 14236361063479940246898563)
      ·
        refine ⟨21354541595219910370347845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14236361063479940246898563 21354541595219910370347845)
        ·
          refine ⟨4003976549103733194440221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21354541595219910370347845 4003976549103733194440221)
          ·
            refine ⟨1501491205913899947915083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4003976549103733194440221 1501491205913899947915083)
            ·
              refine ⟨2252236808870849921872625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501491205913899947915083 2252236808870849921872625)
              ·
                refine ⟨1689177606653137441404469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252236808870849921872625 1689177606653137441404469)
                ·
                  refine ⟨158360400623731635131669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1689177606653137441404469 158360400623731635131669)
                  ·
                    rfl

theorem cell22_1387826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1387826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387826 prefixEnd_1387826 := by exact prefixLift 1387826
  have htrace : WordTrace (prefixWord ++ tailWord_1387826) baseStart_1387826 baseEnd_1387826 := by
    simpa [prefixWord, tailWord_1387826, baseEnd_1387826] using wordTrace_append hprefix tailTrace_1387826
  have hstable : (prefixWord ++ tailWord_1387826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387826).length < 2 ^ (prefixWord ++ tailWord_1387826).sum := by decide
  have hdescent : baseEnd_1387826 < baseStart_1387826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387830 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1387830 : Nat := 118140960795 + 1387830 * 2 ^ 59
def prefixEnd_1387830 : Nat := 4983230072969 + 3 ^ 40 * 1387830 * 2
def baseEnd_1387830 : Nat := 475082571152940228294995

theorem tailTrace_1387830 : CollatzResearch.WordTrace tailWord_1387830 prefixEnd_1387830 475082571152940228294995 := by
  unfold tailWord_1387830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163644910133525458674059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33745545708090938225856629 3163644910133525458674059)
  ·
    refine ⟨4745467365200288188011089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3163644910133525458674059 4745467365200288188011089)
    ·
      refine ⟨3559100523900216141008317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4745467365200288188011089 3559100523900216141008317)
      ·
        refine ⟨1334662696462581052878119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3559100523900216141008317 1334662696462581052878119)
        ·
          refine ⟨2001994044693871579317179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334662696462581052878119 2001994044693871579317179)
          ·
            refine ⟨3002991067040807368975769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001994044693871579317179 3002991067040807368975769)
            ·
              refine ⟨2252243300280605526731827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002991067040807368975769 2252243300280605526731827)
              ·
                refine ⟨3378364950420908290097741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252243300280605526731827 3378364950420908290097741)
                ·
                  refine ⟨1266886856407840608786653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3378364950420908290097741 1266886856407840608786653)
                  ·
                    refine ⟨475082571152940228294995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266886856407840608786653 475082571152940228294995)
                    ·
                      rfl

theorem cell22_1387830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1387830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387830 prefixEnd_1387830 := by exact prefixLift 1387830
  have htrace : WordTrace (prefixWord ++ tailWord_1387830) baseStart_1387830 baseEnd_1387830 := by
    simpa [prefixWord, tailWord_1387830, baseEnd_1387830] using wordTrace_append hprefix tailTrace_1387830
  have hstable : (prefixWord ++ tailWord_1387830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387830).length < 2 ^ (prefixWord ++ tailWord_1387830).sum := by decide
  have hdescent : baseEnd_1387830 < baseStart_1387830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387884 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1387884 : Nat := 118140960795 + 1387884 * 2 ^ 59
def prefixEnd_1387884 : Nat := 4983230072969 + 3 ^ 40 * 1387884 * 2
def baseEnd_1387884 : Nat := 475101056456502087444829

theorem tailTrace_1387884 : CollatzResearch.WordTrace tailWord_1387884 prefixEnd_1387884 475101056456502087444829 := by
  unfold tailWord_1387884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25310144051970387280625353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33746858735960516374167137 25310144051970387280625353)
  ·
    refine ⟨18982608038977790460469015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25310144051970387280625353 18982608038977790460469015)
    ·
      refine ⟨28473912058466685690703523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18982608038977790460469015 28473912058466685690703523)
      ·
        refine ⟨42710868087700028536055285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28473912058466685690703523 42710868087700028536055285)
        ·
          refine ⟨4004143883221877675255183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42710868087700028536055285 4004143883221877675255183)
          ·
            refine ⟨6006215824832816512882775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004143883221877675255183 6006215824832816512882775)
            ·
              refine ⟨9009323737249224769324163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6006215824832816512882775 9009323737249224769324163)
              ·
                refine ⟨13513985605873837153986245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009323737249224769324163 13513985605873837153986245)
                ·
                  refine ⟨2533872301101344466372421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13513985605873837153986245 2533872301101344466372421)
                  ·
                    refine ⟨475101056456502087444829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2533872301101344466372421 475101056456502087444829)
                    ·
                      rfl

theorem cell22_1387884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1387884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387884 prefixEnd_1387884 := by exact prefixLift 1387884
  have htrace : WordTrace (prefixWord ++ tailWord_1387884) baseStart_1387884 baseEnd_1387884 := by
    simpa [prefixWord, tailWord_1387884, baseEnd_1387884] using wordTrace_append hprefix tailTrace_1387884
  have hstable : (prefixWord ++ tailWord_1387884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387884).length < 2 ^ (prefixWord ++ tailWord_1387884).sum := by decide
  have hdescent : baseEnd_1387884 < baseStart_1387884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387918 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1387918 : Nat := 118140960795 + 1387918 * 2 ^ 59
def prefixEnd_1387918 : Nat := 4983230072969 + 3 ^ 40 * 1387918 * 2
def baseEnd_1387918 : Nat := 475112695351337332094725

theorem tailTrace_1387918 : CollatzResearch.WordTrace tailWord_1387918 prefixEnd_1387918 475112695351337332094725 := by
  unfold tailWord_1387918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327691023227199795998551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33747685457211732245325605 6327691023227199795998551)
  ·
    refine ⟨9491536534840799693997827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6327691023227199795998551 9491536534840799693997827)
    ·
      refine ⟨14237304802261199540996741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9491536534840799693997827 14237304802261199540996741)
      ·
        refine ⟨2669494650423974913936889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14237304802261199540996741 2669494650423974913936889)
        ·
          refine ⟨2002120987817981185452667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669494650423974913936889 2002120987817981185452667)
          ·
            refine ⟨3003181481726971778179001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002120987817981185452667 3003181481726971778179001)
            ·
              refine ⟨2252386111295228833634251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003181481726971778179001 2252386111295228833634251)
              ·
                refine ⟨3378579166942843250451377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252386111295228833634251 3378579166942843250451377)
                ·
                  refine ⟨2533934375207132437838533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3378579166942843250451377 2533934375207132437838533)
                  ·
                    refine ⟨475112695351337332094725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2533934375207132437838533 475112695351337332094725)
                    ·
                      rfl

theorem cell22_1387918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1387918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387918 prefixEnd_1387918 := by exact prefixLift 1387918
  have htrace : WordTrace (prefixWord ++ tailWord_1387918) baseStart_1387918 baseEnd_1387918 := by
    simpa [prefixWord, tailWord_1387918, baseEnd_1387918] using wordTrace_append hprefix tailTrace_1387918
  have hstable : (prefixWord ++ tailWord_1387918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387918).length < 2 ^ (prefixWord ++ tailWord_1387918).sum := by decide
  have hdescent : baseEnd_1387918 < baseStart_1387918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387959 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 2, 5]
def baseStart_1387959 : Nat := 118140960795 + 1387959 * 2 ^ 59
def prefixEnd_1387959 : Nat := 4983230072969 + 3 ^ 40 * 1387959 * 2
def baseEnd_1387959 : Nat := 475126730489226891819599

theorem tailTrace_1387959 : CollatzResearch.WordTrace tailWord_1387959 prefixEnd_1387959 475126730489226891819599 := by
  unfold tailWord_1387959
  simp only [CollatzResearch.WordTrace]
  refine ⟨50623023578669062370230931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33748682385779374913487287 50623023578669062370230931)
  ·
    refine ⟨75934535368003593555346397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50623023578669062370230931 75934535368003593555346397)
    ·
      refine ⟨28475450763001347583254899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75934535368003593555346397 28475450763001347583254899)
      ·
        refine ⟨42713176144502021374882349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28475450763001347583254899 42713176144502021374882349)
        ·
          refine ⟨16017441054188258015580881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42713176144502021374882349 16017441054188258015580881)
          ·
            refine ⟨12013080790641193511685661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16017441054188258015580881 12013080790641193511685661)
            ·
              refine ⟨4504905296490447566882123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12013080790641193511685661 4504905296490447566882123)
              ·
                refine ⟨6757357944735671350323185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504905296490447566882123 6757357944735671350323185)
                ·
                  refine ⟨5068018458551753512742389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757357944735671350323185 5068018458551753512742389)
                  ·
                    refine ⟨475126730489226891819599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5068018458551753512742389 475126730489226891819599)
                    ·
                      rfl

theorem cell22_1387959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_1387959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387959 prefixEnd_1387959 := by exact prefixLift 1387959
  have htrace : WordTrace (prefixWord ++ tailWord_1387959) baseStart_1387959 baseEnd_1387959 := by
    simpa [prefixWord, tailWord_1387959, baseEnd_1387959] using wordTrace_append hprefix tailTrace_1387959
  have hstable : (prefixWord ++ tailWord_1387959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387959).length < 2 ^ (prefixWord ++ tailWord_1387959).sum := by decide
  have hdescent : baseEnd_1387959 < baseStart_1387959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387989 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 8]
def baseStart_1387989 : Nat := 118140960795 + 1387989 * 2 ^ 59
def prefixEnd_1387989 : Nat := 4983230072969 + 3 ^ 40 * 1387989 * 2
def baseEnd_1387989 : Nat := 158379000034105604523169

theorem tailTrace_1387989 : CollatzResearch.WordTrace tailWord_1387989 prefixEnd_1387989 158379000034105604523169 := by
  unfold tailWord_1387989
  simp only [CollatzResearch.WordTrace]
  refine ⟨50624117768560377493823021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33749411845706918329215347 50624117768560377493823021)
  ·
    refine ⟨18984044163210141560183633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50624117768560377493823021 18984044163210141560183633)
    ·
      refine ⟨14238033122407606170137725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18984044163210141560183633 14238033122407606170137725)
      ·
        refine ⟨5339262420902852313801647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14238033122407606170137725 5339262420902852313801647)
        ·
          refine ⟨8008893631354278470702471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5339262420902852313801647 8008893631354278470702471)
          ·
            refine ⟨12013340447031417706053707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008893631354278470702471 12013340447031417706053707)
            ·
              refine ⟨18020010670547126559080561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12013340447031417706053707 18020010670547126559080561)
              ·
                refine ⟨13515008002910344919310421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18020010670547126559080561 13515008002910344919310421)
                ·
                  refine ⟨158379000034105604523169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13515008002910344919310421 158379000034105604523169)
                  ·
                    rfl

theorem cell22_1387989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_1387989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1387989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1387989 prefixEnd_1387989 := by exact prefixLift 1387989
  have htrace : WordTrace (prefixWord ++ tailWord_1387989) baseStart_1387989 baseEnd_1387989 := by
    simpa [prefixWord, tailWord_1387989, baseEnd_1387989] using wordTrace_append hprefix tailTrace_1387989
  have hstable : (prefixWord ++ tailWord_1387989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387989).length < 2 ^ (prefixWord ++ tailWord_1387989).sum := by decide
  have hdescent : baseEnd_1387989 < baseStart_1387989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388004 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1388004 : Nat := 118140960795 + 1388004 * 2 ^ 59
def prefixEnd_1388004 : Nat := 4983230072969 + 3 ^ 40 * 1388004 * 2
def baseEnd_1388004 : Nat := 475142134908861774444461

theorem tailTrace_1388004 : CollatzResearch.WordTrace tailWord_1388004 prefixEnd_1388004 475142134908861774444461 := by
  unfold tailWord_1388004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25312332431753017527809533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33749776575670690037079377 25312332431753017527809533)
  ·
    refine ⟨9492124661907381572928575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25312332431753017527809533 9492124661907381572928575)
    ·
      refine ⟨14238186992861072359392863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492124661907381572928575 14238186992861072359392863)
      ·
        refine ⟨21357280489291608539089295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14238186992861072359392863 21357280489291608539089295)
        ·
          refine ⟨32035920733937412808633943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21357280489291608539089295 32035920733937412808633943)
          ·
            refine ⟨48053881100906119212950915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32035920733937412808633943 48053881100906119212950915)
            ·
              refine ⟨72080821651359178819426373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48053881100906119212950915 72080821651359178819426373)
              ·
                refine ⟨13515154059629846028642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72080821651359178819426373 13515154059629846028642445)
                ·
                  refine ⟨5068182772361192260740917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13515154059629846028642445 5068182772361192260740917)
                  ·
                    refine ⟨475142134908861774444461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5068182772361192260740917 475142134908861774444461)
                    ·
                      rfl

theorem cell22_1388004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1388004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388004 prefixEnd_1388004 := by exact prefixLift 1388004
  have htrace : WordTrace (prefixWord ++ tailWord_1388004) baseStart_1388004 baseEnd_1388004 := by
    simpa [prefixWord, tailWord_1388004, baseEnd_1388004] using wordTrace_append hprefix tailTrace_1388004
  have hstable : (prefixWord ++ tailWord_1388004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388004).length < 2 ^ (prefixWord ++ tailWord_1388004).sum := by decide
  have hdescent : baseEnd_1388004 < baseStart_1388004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388019 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 6, 4]
def baseStart_1388019 : Nat := 118140960795 + 1388019 * 2 ^ 59
def prefixEnd_1388019 : Nat := 4983230072969 + 3 ^ 40 * 1388019 * 2
def baseEnd_1388019 : Nat := 475147269715406735319415

theorem tailTrace_1388019 : CollatzResearch.WordTrace tailWord_1388019 prefixEnd_1388019 475147269715406735319415 := by
  unfold tailWord_1388019
  simp only [CollatzResearch.WordTrace]
  refine ⟨50625211958451692617415111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33750141305634461744943407 50625211958451692617415111)
  ·
    refine ⟨75937817937677538926122667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50625211958451692617415111 75937817937677538926122667)
    ·
      refine ⟨113906726906516308389184001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75937817937677538926122667 113906726906516308389184001)
      ·
        refine ⟨85430045179887231291888001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113906726906516308389184001 85430045179887231291888001)
        ·
          refine ⟨64072533884915423468916001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85430045179887231291888001 64072533884915423468916001)
          ·
            refine ⟨48054400413686567601687001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64072533884915423468916001 48054400413686567601687001)
            ·
              refine ⟨36040800310264925701265251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48054400413686567601687001 36040800310264925701265251)
              ·
                refine ⟨54061200465397388551897877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36040800310264925701265251 54061200465397388551897877)
                ·
                  refine ⟨2534118771815502588370213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54061200465397388551897877 2534118771815502588370213)
                  ·
                    refine ⟨475147269715406735319415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2534118771815502588370213 475147269715406735319415)
                    ·
                      rfl

theorem cell22_1388019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_1388019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388019 prefixEnd_1388019 := by exact prefixLift 1388019
  have htrace : WordTrace (prefixWord ++ tailWord_1388019) baseStart_1388019 baseEnd_1388019 := by
    simpa [prefixWord, tailWord_1388019, baseEnd_1388019] using wordTrace_append hprefix tailTrace_1388019
  have hstable : (prefixWord ++ tailWord_1388019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388019).length < 2 ^ (prefixWord ++ tailWord_1388019).sum := by decide
  have hdescent : baseEnd_1388019 < baseStart_1388019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388171 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 4, 4]
def baseStart_1388171 : Nat := 118140960795 + 1388171 * 2 ^ 59
def prefixEnd_1388171 : Nat := 4983230072969 + 3 ^ 40 * 1388171 * 2
def baseEnd_1388171 : Nat := 475199302421729005518949

theorem tailTrace_1388171 : CollatzResearch.WordTrace tailWord_1388171 prefixEnd_1388171 475199302421729005518949 := by
  unfold tailWord_1388171
  simp only [CollatzResearch.WordTrace]
  refine ⟨50630755853901022576948367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33753837235934015051298911 50630755853901022576948367)
  ·
    refine ⟨75946133780851533865422551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50630755853901022576948367 75946133780851533865422551)
    ·
      refine ⟨113919200671277300798133827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75946133780851533865422551 113919200671277300798133827)
      ·
        refine ⟨170878801006915951197200741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113919200671277300798133827 170878801006915951197200741)
        ·
          refine ⟨32039775188796740849475139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170878801006915951197200741 32039775188796740849475139)
          ·
            refine ⟨48059662783195111274212709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32039775188796740849475139 48059662783195111274212709)
            ·
              refine ⟨9011186771849083363914883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48059662783195111274212709 9011186771849083363914883)
              ·
                refine ⟨13516780157773625045872325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011186771849083363914883 13516780157773625045872325)
                ·
                  refine ⟨2534396279582554696101061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13516780157773625045872325 2534396279582554696101061)
                  ·
                    refine ⟨475199302421729005518949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2534396279582554696101061 475199302421729005518949)
                    ·
                      rfl

theorem cell22_1388171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_1388171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388171 prefixEnd_1388171 := by exact prefixLift 1388171
  have htrace : WordTrace (prefixWord ++ tailWord_1388171) baseStart_1388171 baseEnd_1388171 := by
    simpa [prefixWord, tailWord_1388171, baseEnd_1388171] using wordTrace_append hprefix tailTrace_1388171
  have hstable : (prefixWord ++ tailWord_1388171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388171).length < 2 ^ (prefixWord ++ tailWord_1388171).sum := by decide
  have hdescent : baseEnd_1388171 < baseStart_1388171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388190 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1388190 : Nat := 118140960795 + 1388190 * 2 ^ 59
def prefixEnd_1388190 : Nat := 4983230072969 + 3 ^ 40 * 1388190 * 2
def baseEnd_1388190 : Nat := 475205806510019289293891

theorem tailTrace_1388190 : CollatzResearch.WordTrace tailWord_1388190 prefixEnd_1388190 475205806510019289293891 := by
  unfold tailWord_1388190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328931105104023602736253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33754299227221459214593349 6328931105104023602736253)
  ·
    refine ⟨2373349164414008851026095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6328931105104023602736253 2373349164414008851026095)
    ·
      refine ⟨3560023746621013276539143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373349164414008851026095 3560023746621013276539143)
      ·
        refine ⟨5340035619931519914808715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560023746621013276539143 5340035619931519914808715)
        ·
          refine ⟨8010053429897279872213073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340035619931519914808715 8010053429897279872213073)
          ·
            refine ⟨6007540072422959904159805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8010053429897279872213073 6007540072422959904159805)
            ·
              refine ⟨2252827527158609964059927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6007540072422959904159805 2252827527158609964059927)
              ·
                refine ⟨3379241290737914946089891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252827527158609964059927 3379241290737914946089891)
                ·
                  refine ⟨5068861936106872419134837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379241290737914946089891 5068861936106872419134837)
                  ·
                    refine ⟨475205806510019289293891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5068861936106872419134837 475205806510019289293891)
                    ·
                      rfl

theorem cell22_1388190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1388190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388190 prefixEnd_1388190 := by exact prefixLift 1388190
  have htrace : WordTrace (prefixWord ++ tailWord_1388190) baseStart_1388190 baseEnd_1388190 := by
    simpa [prefixWord, tailWord_1388190, baseEnd_1388190] using wordTrace_append hprefix tailTrace_1388190
  have hstable : (prefixWord ++ tailWord_1388190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388190).length < 2 ^ (prefixWord ++ tailWord_1388190).sum := by decide
  have hdescent : baseEnd_1388190 < baseStart_1388190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388226 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1388226 : Nat := 118140960795 + 1388226 * 2 ^ 59
def prefixEnd_1388226 : Nat := 4983230072969 + 3 ^ 40 * 1388226 * 2
def baseEnd_1388226 : Nat := 158406043348575731797927

theorem tailTrace_1388226 : CollatzResearch.WordTrace tailWord_1388226 prefixEnd_1388226 158406043348575731797927 := by
  unfold tailWord_1388226
  simp only [CollatzResearch.WordTrace]
  refine ⟨12658190467175441742550133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33755174579134511313467021 12658190467175441742550133)
  ·
    refine ⟨1186705356297697663364075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12658190467175441742550133 1186705356297697663364075)
    ·
      refine ⟨1780058034446546495046113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186705356297697663364075 1780058034446546495046113)
      ·
        refine ⟨1335043525834909871284585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780058034446546495046113 1335043525834909871284585)
        ·
          refine ⟨1001282644376182403463439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335043525834909871284585 1001282644376182403463439)
          ·
            refine ⟨1501923966564273605195159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001282644376182403463439 1501923966564273605195159)
            ·
              refine ⟨2252885949846410407792739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501923966564273605195159 2252885949846410407792739)
              ·
                refine ⟨3379328924769615611689109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252885949846410407792739 3379328924769615611689109)
                ·
                  refine ⟨158406043348575731797927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3379328924769615611689109 158406043348575731797927)
                  ·
                    rfl

theorem cell22_1388226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1388226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388226 prefixEnd_1388226 := by exact prefixLift 1388226
  have htrace : WordTrace (prefixWord ++ tailWord_1388226) baseStart_1388226 baseEnd_1388226 := by
    simpa [prefixWord, tailWord_1388226, baseEnd_1388226] using wordTrace_append hprefix tailTrace_1388226
  have hstable : (prefixWord ++ tailWord_1388226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388226).length < 2 ^ (prefixWord ++ tailWord_1388226).sum := by decide
  have hdescent : baseEnd_1388226 < baseStart_1388226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388231 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 7]
def baseStart_1388231 : Nat := 118140960795 + 1388231 * 2 ^ 59
def prefixEnd_1388231 : Nat := 4983230072969 + 3 ^ 40 * 1388231 * 2
def baseEnd_1388231 : Nat := 158406613882636283006255

theorem tailTrace_1388231 : CollatzResearch.WordTrace tailWord_1388231 prefixEnd_1388231 158406613882636283006255 := by
  unfold tailWord_1388231
  simp only [CollatzResearch.WordTrace]
  refine ⟨50632944233683652824132547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33755296155789101882755031 50632944233683652824132547)
  ·
    refine ⟨75949416350525479236198821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50632944233683652824132547 75949416350525479236198821)
    ·
      refine ⟨14240515565723527356787279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75949416350525479236198821 14240515565723527356787279)
      ·
        refine ⟨21360773348585291035180919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14240515565723527356787279 21360773348585291035180919)
        ·
          refine ⟨32041160022877936552771379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21360773348585291035180919 32041160022877936552771379)
          ·
            refine ⟨48061740034316904829157069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32041160022877936552771379 48061740034316904829157069)
            ·
              refine ⟨18023152512868839310933901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48061740034316904829157069 18023152512868839310933901)
              ·
                refine ⟨6758682192325814741600213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18023152512868839310933901 6758682192325814741600213)
                ·
                  refine ⟨158406613882636283006255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6758682192325814741600213 158406613882636283006255)
                  ·
                    rfl

theorem cell22_1388231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_1388231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388231 prefixEnd_1388231 := by exact prefixLift 1388231
  have htrace : WordTrace (prefixWord ++ tailWord_1388231) baseStart_1388231 baseEnd_1388231 := by
    simpa [prefixWord, tailWord_1388231, baseEnd_1388231] using wordTrace_append hprefix tailTrace_1388231
  have hstable : (prefixWord ++ tailWord_1388231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388231).length < 2 ^ (prefixWord ++ tailWord_1388231).sum := by decide
  have hdescent : baseEnd_1388231 < baseStart_1388231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388235 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 1, 3]
def baseStart_1388235 : Nat := 118140960795 + 1388235 * 2 ^ 59
def prefixEnd_1388235 : Nat := 4983230072969 + 3 ^ 40 * 1388235 * 2
def baseEnd_1388235 : Nat := 475221210929654171918753

theorem tailTrace_1388235 : CollatzResearch.WordTrace tailWord_1388235 prefixEnd_1388235 475221210929654171918753 := by
  unfold tailWord_1388235
  simp only [CollatzResearch.WordTrace]
  refine ⟨50633090125669161507278159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33755393417112774338185439 50633090125669161507278159)
  ·
    refine ⟨75949635188503742260917239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50633090125669161507278159 75949635188503742260917239)
    ·
      refine ⟨113924452782755613391375859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75949635188503742260917239 113924452782755613391375859)
      ·
        refine ⟨170886679174133420087063789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113924452782755613391375859 170886679174133420087063789)
        ·
          refine ⟨64082504690300032532648921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170886679174133420087063789 64082504690300032532648921)
          ·
            refine ⟨48061878517725024399486691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64082504690300032532648921 48061878517725024399486691)
            ·
              refine ⟨72092817776587536599230037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48061878517725024399486691 72092817776587536599230037)
              ·
                refine ⟨844837708319385194522227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 72092817776587536599230037 844837708319385194522227)
                ·
                  refine ⟨1267256562479077791783341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844837708319385194522227 1267256562479077791783341)
                  ·
                    refine ⟨475221210929654171918753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1267256562479077791783341 475221210929654171918753)
                    ·
                      rfl

theorem cell22_1388235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 3].length) (baseStart_1388235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388235 prefixEnd_1388235 := by exact prefixLift 1388235
  have htrace : WordTrace (prefixWord ++ tailWord_1388235) baseStart_1388235 baseEnd_1388235 := by
    simpa [prefixWord, tailWord_1388235, baseEnd_1388235] using wordTrace_append hprefix tailTrace_1388235
  have hstable : (prefixWord ++ tailWord_1388235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388235).length < 2 ^ (prefixWord ++ tailWord_1388235).sum := by decide
  have hdescent : baseEnd_1388235 < baseStart_1388235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388248 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_1388248 : Nat := 118140960795 + 1388248 * 2 ^ 59
def prefixEnd_1388248 : Nat := 4983230072969 + 3 ^ 40 * 1388248 * 2
def baseEnd_1388248 : Nat := 158408553698442157114571

theorem tailTrace_1388248 : CollatzResearch.WordTrace tailWord_1388248 prefixEnd_1388248 158408553698442157114571 := by
  unfold tailWord_1388248
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316782137311032363750699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33755709516414709818334265 25316782137311032363750699)
  ·
    refine ⟨37975173205966548545626049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25316782137311032363750699 37975173205966548545626049)
    ·
      refine ⟨28481379904474911409219537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37975173205966548545626049 28481379904474911409219537)
      ·
        refine ⟨21361034928356183556914653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28481379904474911409219537 21361034928356183556914653)
        ·
          refine ⟨8010388098133568833842995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21361034928356183556914653 8010388098133568833842995)
          ·
            refine ⟨12015582147200353250764493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8010388098133568833842995 12015582147200353250764493)
            ·
              refine ⟨4505843305200132469036685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12015582147200353250764493 4505843305200132469036685)
              ·
                refine ⟨1689691239450049675888757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4505843305200132469036685 1689691239450049675888757)
                ·
                  refine ⟨158408553698442157114571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1689691239450049675888757 158408553698442157114571)
                  ·
                    rfl

theorem cell22_1388248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_1388248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388248 prefixEnd_1388248 := by exact prefixLift 1388248
  have htrace : WordTrace (prefixWord ++ tailWord_1388248) baseStart_1388248 baseEnd_1388248 := by
    simpa [prefixWord, tailWord_1388248, baseEnd_1388248] using wordTrace_append hprefix tailTrace_1388248
  have hstable : (prefixWord ++ tailWord_1388248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388248).length < 2 ^ (prefixWord ++ tailWord_1388248).sum := by decide
  have hdescent : baseEnd_1388248 < baseStart_1388248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388338 : List Nat := [3, 2, 1, 1, 3, 3, 9]
def baseStart_1388338 : Nat := 118140960795 + 1388338 * 2 ^ 59
def prefixEnd_1388338 : Nat := 4983230072969 + 3 ^ 40 * 1388338 * 2
def baseEnd_1388338 : Nat := 17602091479059119873831

theorem tailTrace_1388338 : CollatzResearch.WordTrace tailWord_1388338 prefixEnd_1388338 17602091479059119873831 := by
  unfold tailWord_1388338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12659211711074002524569417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33757897896197340065518445 12659211711074002524569417)
  ·
    refine ⟨9494408783305501893427063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12659211711074002524569417 9494408783305501893427063)
    ·
      refine ⟨14241613174958252840140595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9494408783305501893427063 14241613174958252840140595)
      ·
        refine ⟨21362419762437379260210893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14241613174958252840140595 21362419762437379260210893)
        ·
          refine ⟨8010907410914017222579085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21362419762437379260210893 8010907410914017222579085)
          ·
            refine ⟨3004090279092756458467157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8010907410914017222579085 3004090279092756458467157)
            ·
              refine ⟨17602091479059119873831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3004090279092756458467157 17602091479059119873831)
              ·
                rfl

theorem cell22_1388338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 9].length) (baseStart_1388338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388338 prefixEnd_1388338 := by exact prefixLift 1388338
  have htrace : WordTrace (prefixWord ++ tailWord_1388338) baseStart_1388338 baseEnd_1388338 := by
    simpa [prefixWord, tailWord_1388338, baseEnd_1388338] using wordTrace_append hprefix tailTrace_1388338
  have hstable : (prefixWord ++ tailWord_1388338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388338).length < 2 ^ (prefixWord ++ tailWord_1388338).sum := by decide
  have hdescent : baseEnd_1388338 < baseStart_1388338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388372 : List Nat := [2, 4, 1, 1, 3, 3, 2, 6]
def baseStart_1388372 : Nat := 118140960795 + 1388372 * 2 ^ 59
def prefixEnd_1388372 : Nat := 4983230072969 + 3 ^ 40 * 1388372 * 2
def baseEnd_1388372 : Nat := 52807567647714609027037

theorem tailTrace_1388372 : CollatzResearch.WordTrace tailWord_1388372 prefixEnd_1388372 52807567647714609027037 := by
  unfold tailWord_1388372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25319043463086416952507685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33758724617448555936676913 25319043463086416952507685)
  ·
    refine ⟨4747320649328703178595191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25319043463086416952507685 4747320649328703178595191)
    ·
      refine ⟨7120980973993054767892787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4747320649328703178595191 7120980973993054767892787)
      ·
        refine ⟨10681471460989582151839181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7120980973993054767892787 10681471460989582151839181)
        ·
          refine ⟨4005551797871093306939693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10681471460989582151839181 4005551797871093306939693)
          ·
            refine ⟨1502081924201659990102385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4005551797871093306939693 1502081924201659990102385)
            ·
              refine ⟨1126561443151244992576789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502081924201659990102385 1126561443151244992576789)
              ·
                refine ⟨52807567647714609027037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1126561443151244992576789 52807567647714609027037)
                ·
                  rfl

theorem cell22_1388372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 6].length) (baseStart_1388372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388372 prefixEnd_1388372 := by exact prefixLift 1388372
  have htrace : WordTrace (prefixWord ++ tailWord_1388372) baseStart_1388372 baseEnd_1388372 := by
    simpa [prefixWord, tailWord_1388372, baseEnd_1388372] using wordTrace_append hprefix tailTrace_1388372
  have hstable : (prefixWord ++ tailWord_1388372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388372).length < 2 ^ (prefixWord ++ tailWord_1388372).sum := by decide
  have hdescent : baseEnd_1388372 < baseStart_1388372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388383 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 7]
def baseStart_1388383 : Nat := 118140960795 + 1388383 * 2 ^ 59
def prefixEnd_1388383 : Nat := 4983230072969 + 3 ^ 40 * 1388383 * 2
def baseEnd_1388383 : Nat := 158423958118077039739433

theorem tailTrace_1388383 : CollatzResearch.WordTrace tailWord_1388383 prefixEnd_1388383 158423958118077039739433 := by
  unfold tailWord_1388383
  simp only [CollatzResearch.WordTrace]
  refine ⟨50638488129132982783665803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33758992086088655189110535 50638488129132982783665803)
  ·
    refine ⟨75957732193699474175498705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50638488129132982783665803 75957732193699474175498705)
    ·
      refine ⟨56968299145274605631624029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75957732193699474175498705 56968299145274605631624029)
      ·
        refine ⟨21363112179477977111859011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56968299145274605631624029 21363112179477977111859011)
        ·
          refine ⟨32044668269216965667788517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21363112179477977111859011 32044668269216965667788517)
          ·
            refine ⟨6008375300478181062710347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32044668269216965667788517 6008375300478181062710347)
            ·
              refine ⟨9012562950717271594065521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6008375300478181062710347 9012562950717271594065521)
              ·
                refine ⟨6759422213037953695549141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9012562950717271594065521 6759422213037953695549141)
                ·
                  refine ⟨158423958118077039739433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6759422213037953695549141 158423958118077039739433)
                  ·
                    rfl

theorem cell22_1388383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_1388383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388383 prefixEnd_1388383 := by exact prefixLift 1388383
  have htrace : WordTrace (prefixWord ++ tailWord_1388383) baseStart_1388383 baseEnd_1388383 := by
    simpa [prefixWord, tailWord_1388383, baseEnd_1388383] using wordTrace_append hprefix tailTrace_1388383
  have hstable : (prefixWord ++ tailWord_1388383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388383).length < 2 ^ (prefixWord ++ tailWord_1388383).sum := by decide
  have hdescent : baseEnd_1388383 < baseStart_1388383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388413 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1388413 : Nat := 118140960795 + 1388413 * 2 ^ 59
def prefixEnd_1388413 : Nat := 4983230072969 + 3 ^ 40 * 1388413 * 2
def baseEnd_1388413 : Nat := 475282143967321040968207

theorem tailTrace_1388413 : CollatzResearch.WordTrace tailWord_1388413 prefixEnd_1388413 475282143967321040968207 := by
  unfold tailWord_1388413
  simp only [CollatzResearch.WordTrace]
  refine ⟨50639582319024297907257893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33759721546016198604838595 50639582319024297907257893)
  ·
    refine ⟨9494921684817055857610855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50639582319024297907257893 9494921684817055857610855)
    ·
      refine ⟨14242382527225583786416283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9494921684817055857610855 14242382527225583786416283)
      ·
        refine ⟨21363573790838375679624425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14242382527225583786416283 21363573790838375679624425)
        ·
          refine ⟨16022680343128781759718319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21363573790838375679624425 16022680343128781759718319)
          ·
            refine ⟨24034020514693172639577479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16022680343128781759718319 24034020514693172639577479)
            ·
              refine ⟨36051030772039758959366219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24034020514693172639577479 36051030772039758959366219)
              ·
                refine ⟨54076546158059638439049329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36051030772039758959366219 54076546158059638439049329)
                ·
                  refine ⟨40557409618544728829286997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54076546158059638439049329 40557409618544728829286997)
                  ·
                    refine ⟨475282143967321040968207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40557409618544728829286997 475282143967321040968207)
                    ·
                      rfl

theorem cell22_1388413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1388413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388413 prefixEnd_1388413 := by exact prefixLift 1388413
  have htrace : WordTrace (prefixWord ++ tailWord_1388413) baseStart_1388413 baseEnd_1388413 := by
    simpa [prefixWord, tailWord_1388413, baseEnd_1388413] using wordTrace_append hprefix tailTrace_1388413
  have hstable : (prefixWord ++ tailWord_1388413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388413).length < 2 ^ (prefixWord ++ tailWord_1388413).sum := by decide
  have hdescent : baseEnd_1388413 < baseStart_1388413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388428 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_1388428 : Nat := 118140960795 + 1388428 * 2 ^ 59
def prefixEnd_1388428 : Nat := 4983230072969 + 3 ^ 40 * 1388428 * 2
def baseEnd_1388428 : Nat := 158429092924622000614387

theorem tailTrace_1388428 : CollatzResearch.WordTrace tailWord_1388428 prefixEnd_1388428 158429092924622000614387 := by
  unfold tailWord_1388428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25320064706984977734526969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33760086275979970312702625 25320064706984977734526969)
  ·
    refine ⟨18990048530238733300895227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25320064706984977734526969 18990048530238733300895227)
    ·
      refine ⟨28485072795358099951342841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18990048530238733300895227 28485072795358099951342841)
      ·
        refine ⟨21363804596518574963507131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28485072795358099951342841 21363804596518574963507131)
        ·
          refine ⟨32045706894777862445260697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21363804596518574963507131 32045706894777862445260697)
          ·
            refine ⟨24034280171083396833945523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32045706894777862445260697 24034280171083396833945523)
            ·
              refine ⟨36051420256625095250918285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24034280171083396833945523 36051420256625095250918285)
              ·
                refine ⟨13519282596234410719094357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36051420256625095250918285 13519282596234410719094357)
                ·
                  refine ⟨158429092924622000614387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13519282596234410719094357 158429092924622000614387)
                  ·
                    rfl

theorem cell22_1388428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_1388428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388428 prefixEnd_1388428 := by exact prefixLift 1388428
  have htrace : WordTrace (prefixWord ++ tailWord_1388428) baseStart_1388428 baseEnd_1388428 := by
    simpa [prefixWord, tailWord_1388428, baseEnd_1388428] using wordTrace_append hprefix tailTrace_1388428
  have hstable : (prefixWord ++ tailWord_1388428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388428).length < 2 ^ (prefixWord ++ tailWord_1388428).sum := by decide
  have hdescent : baseEnd_1388428 < baseStart_1388428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388477 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1388477 : Nat := 118140960795 + 1388477 * 2 ^ 59
def prefixEnd_1388477 : Nat := 4983230072969 + 3 ^ 40 * 1388477 * 2
def baseEnd_1388477 : Nat := 475304052475246207368011

theorem tailTrace_1388477 : CollatzResearch.WordTrace tailWord_1388477 prefixEnd_1388477 475304052475246207368011 := by
  unfold tailWord_1388477
  simp only [CollatzResearch.WordTrace]
  refine ⟨50641916590792436837587685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33761277727194957891725123 50641916590792436837587685)
  ·
    refine ⟨9495359360773581907047691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50641916590792436837587685 9495359360773581907047691)
    ·
      refine ⟨14243039041160372860571537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9495359360773581907047691 14243039041160372860571537)
      ·
        refine ⟨10682279280870279645428653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14243039041160372860571537 10682279280870279645428653)
        ·
          refine ⟨4005854730326354867035745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10682279280870279645428653 4005854730326354867035745)
          ·
            refine ⟨3004391047744766150276809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4005854730326354867035745 3004391047744766150276809)
            ·
              refine ⟨2253293285808574612707607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3004391047744766150276809 2253293285808574612707607)
              ·
                refine ⟨3379939928712861919061411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253293285808574612707607 3379939928712861919061411)
                ·
                  refine ⟨5069909893069292878592117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379939928712861919061411 5069909893069292878592117)
                  ·
                    refine ⟨475304052475246207368011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5069909893069292878592117 475304052475246207368011)
                    ·
                      rfl

theorem cell22_1388477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1388477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388477 prefixEnd_1388477 := by exact prefixLift 1388477
  have htrace : WordTrace (prefixWord ++ tailWord_1388477) baseStart_1388477 baseEnd_1388477 := by
    simpa [prefixWord, tailWord_1388477, baseEnd_1388477] using wordTrace_append hprefix tailTrace_1388477
  have hstable : (prefixWord ++ tailWord_1388477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388477).length < 2 ^ (prefixWord ++ tailWord_1388477).sum := by decide
  have hdescent : baseEnd_1388477 < baseStart_1388477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388492 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_1388492 : Nat := 118140960795 + 1388492 * 2 ^ 59
def prefixEnd_1388492 : Nat := 4983230072969 + 3 ^ 40 * 1388492 * 2
def baseEnd_1388492 : Nat := 475309187281791168242965

theorem tailTrace_1388492 : CollatzResearch.WordTrace tailWord_1388492 prefixEnd_1388492 475309187281791168242965 := by
  unfold tailWord_1388492
  simp only [CollatzResearch.WordTrace]
  refine ⟨25321231842869047199691865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33761642457158729599589153 25321231842869047199691865)
  ·
    refine ⟨18990923882151785399768899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25321231842869047199691865 18990923882151785399768899)
    ·
      refine ⟨28486385823227678099653349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18990923882151785399768899 28486385823227678099653349)
      ·
        refine ⟨5341197341855189643685003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28486385823227678099653349 5341197341855189643685003)
        ·
          refine ⟨8011796012782784465527505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341197341855189643685003 8011796012782784465527505)
          ·
            refine ⟨6008847009587088349145629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8011796012782784465527505 6008847009587088349145629)
            ·
              refine ⟨2253317628595158130929611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6008847009587088349145629 2253317628595158130929611)
              ·
                refine ⟨3379976442892737196394417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253317628595158130929611 3379976442892737196394417)
                ·
                  refine ⟨2534982332169552897295813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3379976442892737196394417 2534982332169552897295813)
                  ·
                    refine ⟨475309187281791168242965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2534982332169552897295813 475309187281791168242965)
                    ·
                      rfl

theorem cell22_1388492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_1388492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388492 prefixEnd_1388492 := by exact prefixLift 1388492
  have htrace : WordTrace (prefixWord ++ tailWord_1388492) baseStart_1388492 baseEnd_1388492 := by
    simpa [prefixWord, tailWord_1388492, baseEnd_1388492] using wordTrace_append hprefix tailTrace_1388492
  have hstable : (prefixWord ++ tailWord_1388492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388492).length < 2 ^ (prefixWord ++ tailWord_1388492).sum := by decide
  have hdescent : baseEnd_1388492 < baseStart_1388492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388498 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_1388498 : Nat := 118140960795 + 1388498 * 2 ^ 59
def prefixEnd_1388498 : Nat := 4983230072969 + 3 ^ 40 * 1388498 * 2
def baseEnd_1388498 : Nat := 475311241204409152592947

theorem tailTrace_1388498 : CollatzResearch.WordTrace tailWord_1388498 prefixEnd_1388498 475311241204409152592947 := by
  unfold tailWord_1388498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12660670630929089356025537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33761788349144238282734765 12660670630929089356025537)
  ·
    refine ⟨9495502973196817017019153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12660670630929089356025537 9495502973196817017019153)
    ·
      refine ⟨7121627229897612762764365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9495502973196817017019153 7121627229897612762764365)
      ·
        refine ⟨2670610211211604786036637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7121627229897612762764365 2670610211211604786036637)
        ·
          refine ⟨1001478829204351794763739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2670610211211604786036637 1001478829204351794763739)
          ·
            refine ⟨1502218243806527692145609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001478829204351794763739 1502218243806527692145609)
            ·
              refine ⟨1126663682854895769109207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502218243806527692145609 1126663682854895769109207)
              ·
                refine ⟨1689995524282343653663811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126663682854895769109207 1689995524282343653663811)
                ·
                  refine ⟨2534993286423515480495717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689995524282343653663811 2534993286423515480495717)
                  ·
                    refine ⟨475311241204409152592947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2534993286423515480495717 475311241204409152592947)
                    ·
                      rfl

theorem cell22_1388498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_1388498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388498 prefixEnd_1388498 := by exact prefixLift 1388498
  have htrace : WordTrace (prefixWord ++ tailWord_1388498) baseStart_1388498 baseEnd_1388498 := by
    simpa [prefixWord, tailWord_1388498, baseEnd_1388498] using wordTrace_append hprefix tailTrace_1388498
  have hstable : (prefixWord ++ tailWord_1388498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388498).length < 2 ^ (prefixWord ++ tailWord_1388498).sum := by decide
  have hdescent : baseEnd_1388498 < baseStart_1388498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388573 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_1388573 : Nat := 118140960795 + 1388573 * 2 ^ 59
def prefixEnd_1388573 : Nat := 4983230072969 + 3 ^ 40 * 1388573 * 2
def baseEnd_1388573 : Nat := 475336915237133956967717

theorem tailTrace_1388573 : CollatzResearch.WordTrace tailWord_1388573 prefixEnd_1388573 475336915237133956967717 := by
  unfold tailWord_1388573
  simp only [CollatzResearch.WordTrace]
  refine ⟨50645417998444645233082373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33763611998963096822054915 50645417998444645233082373)
  ·
    refine ⟨9496015874708370981202945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50645417998444645233082373 9496015874708370981202945)
    ·
      refine ⟨7122011906031278235902209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9496015874708370981202945 7122011906031278235902209)
      ·
        refine ⟨5341508929523458676926657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7122011906031278235902209 5341508929523458676926657)
        ·
          refine ⟨4006131697142594007694993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341508929523458676926657 4006131697142594007694993)
          ·
            refine ⟨3004598772856945505771245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4006131697142594007694993 3004598772856945505771245)
            ·
              refine ⟨1126724539821354564664217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3004598772856945505771245 1126724539821354564664217)
              ·
                refine ⟨845043404866015923498163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126724539821354564664217 845043404866015923498163)
                ·
                  refine ⟨1267565107299023885247245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845043404866015923498163 1267565107299023885247245)
                  ·
                    refine ⟨475336915237133956967717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1267565107299023885247245 475336915237133956967717)
                    ·
                      rfl

theorem cell22_1388573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_1388573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388573 prefixEnd_1388573 := by exact prefixLift 1388573
  have htrace : WordTrace (prefixWord ++ tailWord_1388573) baseStart_1388573 baseEnd_1388573 := by
    simpa [prefixWord, tailWord_1388573, baseEnd_1388573] using wordTrace_append hprefix tailTrace_1388573
  have hstable : (prefixWord ++ tailWord_1388573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388573).length < 2 ^ (prefixWord ++ tailWord_1388573).sum := by decide
  have hdescent : baseEnd_1388573 < baseStart_1388573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388586 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_1388586 : Nat := 118140960795 + 1388586 * 2 ^ 59
def prefixEnd_1388586 : Nat := 4983230072969 + 3 ^ 40 * 1388586 * 2
def baseEnd_1388586 : Nat := 158447121800935418797559

theorem tailTrace_1388586 : CollatzResearch.WordTrace tailWord_1388586 prefixEnd_1388586 158447121800935418797559 := by
  unfold tailWord_1388586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12661473036849387113326403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33763928098265032302203741 12661473036849387113326403)
  ·
    refine ⟨18992209555274080669989605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12661473036849387113326403 18992209555274080669989605)
    ·
      refine ⟨3561039291613890125623051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18992209555274080669989605 3561039291613890125623051)
      ·
        refine ⟨5341558937420835188434577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561039291613890125623051 5341558937420835188434577)
        ·
          refine ⟨4006169203065626391325933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341558937420835188434577 4006169203065626391325933)
          ·
            refine ⟨1502313451149609896747225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4006169203065626391325933 1502313451149609896747225)
            ·
              refine ⟨1126735088362207422560419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502313451149609896747225 1126735088362207422560419)
              ·
                refine ⟨1690102632543311133840629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126735088362207422560419 1690102632543311133840629)
                ·
                  refine ⟨158447121800935418797559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690102632543311133840629 158447121800935418797559)
                  ·
                    rfl

theorem cell22_1388586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_1388586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388586 prefixEnd_1388586 := by exact prefixLift 1388586
  have htrace : WordTrace (prefixWord ++ tailWord_1388586) baseStart_1388586 baseEnd_1388586 := by
    simpa [prefixWord, tailWord_1388586, baseEnd_1388586] using wordTrace_append hprefix tailTrace_1388586
  have hstable : (prefixWord ++ tailWord_1388586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388586).length < 2 ^ (prefixWord ++ tailWord_1388586).sum := by decide
  have hdescent : baseEnd_1388586 < baseStart_1388586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388629 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1388629 : Nat := 118140960795 + 1388629 * 2 ^ 59
def prefixEnd_1388629 : Nat := 4983230072969 + 3 ^ 40 * 1388629 * 2
def baseEnd_1388629 : Nat := 475356085181568477567545

theorem tailTrace_1388629 : CollatzResearch.WordTrace tailWord_1388629 prefixEnd_1388629 475356085181568477567545 := by
  unfold tailWord_1388629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50647460486241766797120941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33764973657494511198080627 50647460486241766797120941)
  ·
    refine ⟨18992797682340662548920353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50647460486241766797120941 18992797682340662548920353)
    ·
      refine ⟨14244598261755496911690265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18992797682340662548920353 14244598261755496911690265)
      ·
        refine ⟨10683448696316622683767699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14244598261755496911690265 10683448696316622683767699)
        ·
          refine ⟨16025173044474934025651549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10683448696316622683767699 16025173044474934025651549)
          ·
            refine ⟨6009439891678100259619331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16025173044474934025651549 6009439891678100259619331)
            ·
              refine ⟨9014159837517150389428997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009439891678100259619331 9014159837517150389428997)
              ·
                refine ⟨1690154969534465698017937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9014159837517150389428997 1690154969534465698017937)
                ·
                  refine ⟨1267616227150849273513453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1690154969534465698017937 1267616227150849273513453)
                  ·
                    refine ⟨475356085181568477567545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1267616227150849273513453 475356085181568477567545)
                    ·
                      rfl

theorem cell22_1388629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1388629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388629 prefixEnd_1388629 := by exact prefixLift 1388629
  have htrace : WordTrace (prefixWord ++ tailWord_1388629) baseStart_1388629 baseEnd_1388629 := by
    simpa [prefixWord, tailWord_1388629, baseEnd_1388629] using wordTrace_append hprefix tailTrace_1388629
  have hstable : (prefixWord ++ tailWord_1388629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388629).length < 2 ^ (prefixWord ++ tailWord_1388629).sum := by decide
  have hdescent : baseEnd_1388629 < baseStart_1388629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388762 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_1388762 : Nat := 118140960795 + 1388762 * 2 ^ 59
def prefixEnd_1388762 : Nat := 4983230072969 + 3 ^ 40 * 1388762 * 2
def baseEnd_1388762 : Nat := 475401613799600463992137

theorem tailTrace_1388762 : CollatzResearch.WordTrace tailWord_1388762 prefixEnd_1388762 475401613799600463992137 := by
  unfold tailWord_1388762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663077848689982627928135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33768207596506620341141693 12663077848689982627928135)
  ·
    refine ⟨18994616773034973941892203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12663077848689982627928135 18994616773034973941892203)
    ·
      refine ⟨28491925159552460912838305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18994616773034973941892203 28491925159552460912838305)
      ·
        refine ⟨21368943869664345684628729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28491925159552460912838305 21368943869664345684628729)
        ·
          refine ⟨16026707902248259263471547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21368943869664345684628729 16026707902248259263471547)
          ·
            refine ⟨24040061853372388895207321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16026707902248259263471547 24040061853372388895207321)
            ·
              refine ⟨18030046390029291671405491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24040061853372388895207321 18030046390029291671405491)
              ·
                refine ⟨27045069585043937507108237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18030046390029291671405491 27045069585043937507108237)
                ·
                  refine ⟨10141901094391476565165589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27045069585043937507108237 10141901094391476565165589)
                  ·
                    refine ⟨475401613799600463992137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10141901094391476565165589 475401613799600463992137)
                    ·
                      rfl

theorem cell22_1388762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_1388762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388762 prefixEnd_1388762 := by exact prefixLift 1388762
  have htrace : WordTrace (prefixWord ++ tailWord_1388762) baseStart_1388762 baseEnd_1388762 := by
    simpa [prefixWord, tailWord_1388762, baseEnd_1388762] using wordTrace_append hprefix tailTrace_1388762
  have hstable : (prefixWord ++ tailWord_1388762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388762).length < 2 ^ (prefixWord ++ tailWord_1388762).sum := by decide
  have hdescent : baseEnd_1388762 < baseStart_1388762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388779 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 2, 4]
def baseStart_1388779 : Nat := 118140960795 + 1388779 * 2 ^ 59
def prefixEnd_1388779 : Nat := 4983230072969 + 3 ^ 40 * 1388779 * 2
def baseEnd_1388779 : Nat := 475407433247018086317085

theorem tailTrace_1388779 : CollatzResearch.WordTrace tailWord_1388779 prefixEnd_1388779 475407433247018086317085 := by
  unfold tailWord_1388779
  simp only [CollatzResearch.WordTrace]
  refine ⟨50652931435698342415081391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33768620957132228276720927 50652931435698342415081391)
  ·
    refine ⟨75979397153547513622622087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50652931435698342415081391 75979397153547513622622087)
    ·
      refine ⟨113969095730321270433933131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75979397153547513622622087 113969095730321270433933131)
      ·
        refine ⟨170953643595481905650899697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113969095730321270433933131 170953643595481905650899697)
        ·
          refine ⟨128215232696611429238174773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170953643595481905650899697 128215232696611429238174773)
          ·
            refine ⟨12020178065307321491078885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128215232696611429238174773 12020178065307321491078885)
            ·
              refine ⟨2253783387245122779577291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12020178065307321491078885 2253783387245122779577291)
              ·
                refine ⟨3380675080867684169365937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253783387245122779577291 3380675080867684169365937)
                ·
                  refine ⟨2535506310650763127024453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380675080867684169365937 2535506310650763127024453)
                  ·
                    refine ⟨475407433247018086317085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2535506310650763127024453 475407433247018086317085)
                    ·
                      rfl

theorem cell22_1388779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].length) (baseStart_1388779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388779 prefixEnd_1388779 := by exact prefixLift 1388779
  have htrace : WordTrace (prefixWord ++ tailWord_1388779) baseStart_1388779 baseEnd_1388779 := by
    simpa [prefixWord, tailWord_1388779, baseEnd_1388779] using wordTrace_append hprefix tailTrace_1388779
  have hstable : (prefixWord ++ tailWord_1388779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388779).length < 2 ^ (prefixWord ++ tailWord_1388779).sum := by decide
  have hdescent : baseEnd_1388779 < baseStart_1388779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388781 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1388781 : Nat := 118140960795 + 1388781 * 2 ^ 59
def prefixEnd_1388781 : Nat := 4983230072969 + 3 ^ 40 * 1388781 * 2
def baseEnd_1388781 : Nat := 475408117887890747767079

theorem tailTrace_1388781 : CollatzResearch.WordTrace tailWord_1388781 prefixEnd_1388781 475408117887890747767079 := by
  unfold tailWord_1388781
  simp only [CollatzResearch.WordTrace]
  refine ⟨50653004381691096756654197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33768669587794064504436131 50653004381691096756654197)
  ·
    refine ⟨4748719160783540320936331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50653004381691096756654197 4748719160783540320936331)
    ·
      refine ⟨7123078741175310481404497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748719160783540320936331 7123078741175310481404497)
      ·
        refine ⟨5342309055881482861053373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7123078741175310481404497 5342309055881482861053373)
        ·
          refine ⟨2003365895955556072895015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5342309055881482861053373 2003365895955556072895015)
          ·
            refine ⟨3005048843933334109342523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003365895955556072895015 3005048843933334109342523)
            ·
              refine ⟨4507573265900001164013785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005048843933334109342523 4507573265900001164013785)
              ·
                refine ⟨3380679949425000873010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507573265900001164013785 3380679949425000873010339)
                ·
                  refine ⟨5071019924137501309515509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380679949425000873010339 5071019924137501309515509)
                  ·
                    refine ⟨475408117887890747767079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5071019924137501309515509 475408117887890747767079)
                    ·
                      rfl

theorem cell22_1388781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1388781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388781 prefixEnd_1388781 := by exact prefixLift 1388781
  have htrace : WordTrace (prefixWord ++ tailWord_1388781) baseStart_1388781 baseEnd_1388781 := by
    simpa [prefixWord, tailWord_1388781, baseEnd_1388781] using wordTrace_append hprefix tailTrace_1388781
  have hstable : (prefixWord ++ tailWord_1388781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388781).length < 2 ^ (prefixWord ++ tailWord_1388781).sum := by decide
  have hdescent : baseEnd_1388781 < baseStart_1388781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388798 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1388798 : Nat := 118140960795 + 1388798 * 2 ^ 59
def prefixEnd_1388798 : Nat := 4983230072969 + 3 ^ 40 * 1388798 * 2
def baseEnd_1388798 : Nat := 475413937335308370092027

theorem tailTrace_1388798 : CollatzResearch.WordTrace tailWord_1388798 prefixEnd_1388798 475413937335308370092027 := by
  unfold tailWord_1388798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331703052828688582502881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33769082948419672440015365 6331703052828688582502881)
  ·
    refine ⟨4748777289621516436877161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6331703052828688582502881 4748777289621516436877161)
    ·
      refine ⟨3561582967216137327657871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4748777289621516436877161 3561582967216137327657871)
      ·
        refine ⟨5342374450824205991486807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561582967216137327657871 5342374450824205991486807)
        ·
          refine ⟨8013561676236308987230211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342374450824205991486807 8013561676236308987230211)
          ·
            refine ⟨12020342514354463480845317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8013561676236308987230211 12020342514354463480845317)
            ·
              refine ⟨2253814221441461902658497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12020342514354463480845317 2253814221441461902658497)
              ·
                refine ⟨1690360666081096426993873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253814221441461902658497 1690360666081096426993873)
                ·
                  refine ⟨1267770499560822320245405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1690360666081096426993873 1267770499560822320245405)
                  ·
                    refine ⟨475413937335308370092027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1267770499560822320245405 475413937335308370092027)
                    ·
                      rfl

theorem cell22_1388798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1388798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388798 prefixEnd_1388798 := by exact prefixLift 1388798
  have htrace : WordTrace (prefixWord ++ tailWord_1388798) baseStart_1388798 baseEnd_1388798 := by
    simpa [prefixWord, tailWord_1388798, baseEnd_1388798] using wordTrace_append hprefix tailTrace_1388798
  have hstable : (prefixWord ++ tailWord_1388798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388798).length < 2 ^ (prefixWord ++ tailWord_1388798).sum := by decide
  have hdescent : baseEnd_1388798 < baseStart_1388798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388830 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1388830 : Nat := 118140960795 + 1388830 * 2 ^ 59
def prefixEnd_1388830 : Nat := 4983230072969 + 3 ^ 40 * 1388830 * 2
def baseEnd_1388830 : Nat := 475424891589270953291929

theorem tailTrace_1388830 : CollatzResearch.WordTrace tailWord_1388830 prefixEnd_1388830 475424891589270953291929 := by
  unfold tailWord_1388830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331848944814197265648493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33769861039009052083458629 6331848944814197265648493)
  ·
    refine ⟨2374443354305323974618185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6331848944814197265648493 2374443354305323974618185)
    ·
      refine ⟨1780832515728992980963639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2374443354305323974618185 1780832515728992980963639)
      ·
        refine ⟨2671248773593489471445459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780832515728992980963639 2671248773593489471445459)
        ·
          refine ⟨4006873160390234207168189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671248773593489471445459 4006873160390234207168189)
          ·
            refine ⟨1502577435146337827688071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4006873160390234207168189 1502577435146337827688071)
            ·
              refine ⟨2253866152719506741532107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502577435146337827688071 2253866152719506741532107)
              ·
                refine ⟨3380799229079260112298161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253866152719506741532107 3380799229079260112298161)
                ·
                  refine ⟨2535599421809445084223621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380799229079260112298161 2535599421809445084223621)
                  ·
                    refine ⟨475424891589270953291929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2535599421809445084223621 475424891589270953291929)
                    ·
                      rfl

theorem cell22_1388830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1388830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388830 prefixEnd_1388830 := by exact prefixLift 1388830
  have htrace : WordTrace (prefixWord ++ tailWord_1388830) baseStart_1388830 baseEnd_1388830 := by
    simpa [prefixWord, tailWord_1388830, baseEnd_1388830] using wordTrace_append hprefix tailTrace_1388830
  have hstable : (prefixWord ++ tailWord_1388830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388830).length < 2 ^ (prefixWord ++ tailWord_1388830).sum := by decide
  have hdescent : baseEnd_1388830 < baseStart_1388830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388899 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_1388899 : Nat := 118140960795 + 1388899 * 2 ^ 59
def prefixEnd_1388899 : Nat := 4983230072969 + 3 ^ 40 * 1388899 * 2
def baseEnd_1388899 : Nat := 475448511699377773316717

theorem tailTrace_1388899 : CollatzResearch.WordTrace tailWord_1388899 prefixEnd_1388899 475448511699377773316717 := by
  unfold tailWord_1388899
  simp only [CollatzResearch.WordTrace]
  refine ⟨50657308195263602909449751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33771538796842401939633167 50657308195263602909449751)
  ·
    refine ⟨75985962292895404364174627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50657308195263602909449751 75985962292895404364174627)
    ·
      refine ⟨113978943439343106546261941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75985962292895404364174627 113978943439343106546261941)
      ·
        refine ⟨10685525947438416238712057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113978943439343106546261941 10685525947438416238712057)
        ·
          refine ⟨8014144460578812179034043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10685525947438416238712057 8014144460578812179034043)
          ·
            refine ⟨12021216690868218268551065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014144460578812179034043 12021216690868218268551065)
            ·
              refine ⟨9015912518151163701413299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12021216690868218268551065 9015912518151163701413299)
              ·
                refine ⟨13523868777226745552119949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9015912518151163701413299 13523868777226745552119949)
                ·
                  refine ⟨5071450791460029582044981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13523868777226745552119949 5071450791460029582044981)
                  ·
                    refine ⟨475448511699377773316717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5071450791460029582044981 475448511699377773316717)
                    ·
                      rfl

theorem cell22_1388899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_1388899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1388899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1388899 prefixEnd_1388899 := by exact prefixLift 1388899
  have htrace : WordTrace (prefixWord ++ tailWord_1388899) baseStart_1388899 baseEnd_1388899 := by
    simpa [prefixWord, tailWord_1388899, baseEnd_1388899] using wordTrace_append hprefix tailTrace_1388899
  have hstable : (prefixWord ++ tailWord_1388899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388899).length < 2 ^ (prefixWord ++ tailWord_1388899).sum := by decide
  have hdescent : baseEnd_1388899 < baseStart_1388899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389012 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1389012 : Nat := 118140960795 + 1389012 * 2 ^ 59
def prefixEnd_1389012 : Nat := 4983230072969 + 3 ^ 40 * 1389012 * 2
def baseEnd_1389012 : Nat := 475487193908683145241371

theorem tailTrace_1389012 : CollatzResearch.WordTrace tailWord_1389012 prefixEnd_1389012 475487193908683145241371 := by
  unfold tailWord_1389012
  simp only [CollatzResearch.WordTrace]
  refine ⟨25330714821927111604156645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33774286429236148805542193 25330714821927111604156645)
  ·
    refine ⟨4749509029111333425779371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25330714821927111604156645 4749509029111333425779371)
    ·
      refine ⟨7124263543667000138669057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4749509029111333425779371 7124263543667000138669057)
      ·
        refine ⟨5343197657750250104001793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7124263543667000138669057 5343197657750250104001793)
        ·
          refine ⟨4007398243312687578001345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5343197657750250104001793 4007398243312687578001345)
          ·
            refine ⟨3005548682484515683501009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007398243312687578001345 3005548682484515683501009)
            ·
              refine ⟨2254161511863386762625757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005548682484515683501009 2254161511863386762625757)
              ·
                refine ⟨845310566948770035984659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254161511863386762625757 845310566948770035984659)
                ·
                  refine ⟨1267965850423155053976989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845310566948770035984659 1267965850423155053976989)
                  ·
                    refine ⟨475487193908683145241371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1267965850423155053976989 475487193908683145241371)
                    ·
                      rfl

theorem cell22_1389012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1389012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389012 prefixEnd_1389012 := by exact prefixLift 1389012
  have htrace : WordTrace (prefixWord ++ tailWord_1389012) baseStart_1389012 baseEnd_1389012 := by
    simpa [prefixWord, tailWord_1389012, baseEnd_1389012] using wordTrace_append hprefix tailTrace_1389012
  have hstable : (prefixWord ++ tailWord_1389012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389012).length < 2 ^ (prefixWord ++ tailWord_1389012).sum := by decide
  have hdescent : baseEnd_1389012 < baseStart_1389012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389036 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_1389036 : Nat := 118140960795 + 1389036 * 2 ^ 59
def prefixEnd_1389036 : Nat := 4983230072969 + 3 ^ 40 * 1389036 * 2
def baseEnd_1389036 : Nat := 158498469866385027547099

theorem tailTrace_1389036 : CollatzResearch.WordTrace tailWord_1389036 prefixEnd_1389036 158498469866385027547099 := by
  unfold tailWord_1389036
  simp only [CollatzResearch.WordTrace]
  refine ⟨25331152497883637653593481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33774869997178183538124641 25331152497883637653593481)
  ·
    refine ⟨18998364373412728240195111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25331152497883637653593481 18998364373412728240195111)
    ·
      refine ⟨28497546560119092360292667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18998364373412728240195111 28497546560119092360292667)
      ·
        refine ⟨42746319840178638540439001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28497546560119092360292667 42746319840178638540439001)
        ·
          refine ⟨32059739880133978905329251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42746319840178638540439001 32059739880133978905329251)
          ·
            refine ⟨48089609820200968357993877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32059739880133978905329251 48089609820200968357993877)
            ·
              refine ⟨2254200460321920391780963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48089609820200968357993877 2254200460321920391780963)
              ·
                refine ⟨3381300690482880587671445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254200460321920391780963 3381300690482880587671445)
                ·
                  refine ⟨158498469866385027547099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3381300690482880587671445 158498469866385027547099)
                  ·
                    rfl

theorem cell22_1389036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_1389036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389036 prefixEnd_1389036 := by exact prefixLift 1389036
  have htrace : WordTrace (prefixWord ++ tailWord_1389036) baseStart_1389036 baseEnd_1389036 := by
    simpa [prefixWord, tailWord_1389036, baseEnd_1389036] using wordTrace_append hprefix tailTrace_1389036
  have hstable : (prefixWord ++ tailWord_1389036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389036).length < 2 ^ (prefixWord ++ tailWord_1389036).sum := by decide
  have hdescent : baseEnd_1389036 < baseStart_1389036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389051 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 8, 3]
def baseStart_1389051 : Nat := 118140960795 + 1389051 * 2 ^ 59
def prefixEnd_1389051 : Nat := 4983230072969 + 3 ^ 40 * 1389051 * 2
def baseEnd_1389051 : Nat := 475500544405700043516251

theorem tailTrace_1389051 : CollatzResearch.WordTrace tailWord_1389051 prefixEnd_1389051 475500544405700043516251 := by
  unfold tailWord_1389051
  simp only [CollatzResearch.WordTrace]
  refine ⟨50662852090712932868983007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33775234727141955245988671 50662852090712932868983007)
  ·
    refine ⟨75994278136069399303474511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50662852090712932868983007 75994278136069399303474511)
    ·
      refine ⟨113991417204104098955211767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75994278136069399303474511 113991417204104098955211767)
      ·
        refine ⟨170987125806156148432817651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113991417204104098955211767 170987125806156148432817651)
        ·
          refine ⟨256480688709234222649226477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170987125806156148432817651 256480688709234222649226477)
          ·
            refine ⟨96180258265962833493459929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256480688709234222649226477 96180258265962833493459929)
            ·
              refine ⟨72135193699472125120094947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96180258265962833493459929 72135193699472125120094947)
              ·
                refine ⟨108202790549208187680142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72135193699472125120094947 108202790549208187680142421)
                ·
                  refine ⟨1268001451748533449376669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 108202790549208187680142421 1268001451748533449376669)
                  ·
                    refine ⟨475500544405700043516251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268001451748533449376669 475500544405700043516251)
                    ·
                      rfl

theorem cell22_1389051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 3].length) (baseStart_1389051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389051 prefixEnd_1389051 := by exact prefixLift 1389051
  have htrace : WordTrace (prefixWord ++ tailWord_1389051) baseStart_1389051 baseEnd_1389051 := by
    simpa [prefixWord, tailWord_1389051, baseEnd_1389051] using wordTrace_append hprefix tailTrace_1389051
  have hstable : (prefixWord ++ tailWord_1389051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389051).length < 2 ^ (prefixWord ++ tailWord_1389051).sum := by decide
  have hdescent : baseEnd_1389051 < baseStart_1389051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389066 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1389066 : Nat := 118140960795 + 1389066 * 2 ^ 59
def prefixEnd_1389066 : Nat := 4983230072969 + 3 ^ 40 * 1389066 * 2
def baseEnd_1389066 : Nat := 475505679212245004391205

theorem tailTrace_1389066 : CollatzResearch.WordTrace tailWord_1389066 prefixEnd_1389066 475505679212245004391205 := by
  unfold tailWord_1389066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665849796414647607694763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33775599457105726953852701 12665849796414647607694763)
  ·
    refine ⟨18998774694621971411542145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12665849796414647607694763 18998774694621971411542145)
    ·
      refine ⟨14249081020966478558656609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18998774694621971411542145 14249081020966478558656609)
      ·
        refine ⟨10686810765724858918992457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14249081020966478558656609 10686810765724858918992457)
        ·
          refine ⟨8015108074293644189244343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10686810765724858918992457 8015108074293644189244343)
          ·
            refine ⟨12022662111440466283866515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8015108074293644189244343 12022662111440466283866515)
            ·
              refine ⟨18033993167160699425799773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12022662111440466283866515 18033993167160699425799773)
              ·
                refine ⟨6762747437685262284674915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18033993167160699425799773 6762747437685262284674915)
                ·
                  refine ⟨10144121156527893427012373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762747437685262284674915 10144121156527893427012373)
                  ·
                    refine ⟨475505679212245004391205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10144121156527893427012373 475505679212245004391205)
                    ·
                      rfl

theorem cell22_1389066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1389066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389066 prefixEnd_1389066 := by exact prefixLift 1389066
  have htrace : WordTrace (prefixWord ++ tailWord_1389066) baseStart_1389066 baseEnd_1389066 := by
    simpa [prefixWord, tailWord_1389066, baseEnd_1389066] using wordTrace_append hprefix tailTrace_1389066
  have hstable : (prefixWord ++ tailWord_1389066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389066).length < 2 ^ (prefixWord ++ tailWord_1389066).sum := by decide
  have hdescent : baseEnd_1389066 < baseStart_1389066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389068 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_1389068 : Nat := 118140960795 + 1389068 * 2 ^ 59
def prefixEnd_1389068 : Nat := 4983230072969 + 3 ^ 40 * 1389068 * 2
def baseEnd_1389068 : Nat := 475506363853117665841199

theorem tailTrace_1389068 : CollatzResearch.WordTrace tailWord_1389068 prefixEnd_1389068 475506363853117665841199 := by
  unfold tailWord_1389068
  simp only [CollatzResearch.WordTrace]
  refine ⟨25331736065825672386175929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33775648087767563181567905 25331736065825672386175929)
  ·
    refine ⟨18998802049369254289631947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25331736065825672386175929 18998802049369254289631947)
    ·
      refine ⟨28498203074053881434447921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18998802049369254289631947 28498203074053881434447921)
      ·
        refine ⟨21373652305540411075835941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28498203074053881434447921 21373652305540411075835941)
        ·
          refine ⟨4007559807288827076719239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21373652305540411075835941 4007559807288827076719239)
          ·
            refine ⟨6011339710933240615078859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007559807288827076719239 6011339710933240615078859)
            ·
              refine ⟨9017009566399860922618289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011339710933240615078859 9017009566399860922618289)
              ·
                refine ⟨6762757174799895691963717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9017009566399860922618289 6762757174799895691963717)
                ·
                  refine ⟨1268016970274980442243197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6762757174799895691963717 1268016970274980442243197)
                  ·
                    refine ⟨475506363853117665841199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268016970274980442243197 475506363853117665841199)
                    ·
                      rfl

theorem cell22_1389068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_1389068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389068 prefixEnd_1389068 := by exact prefixLift 1389068
  have htrace : WordTrace (prefixWord ++ tailWord_1389068) baseStart_1389068 baseEnd_1389068 := by
    simpa [prefixWord, tailWord_1389068, baseEnd_1389068] using wordTrace_append hprefix tailTrace_1389068
  have hstable : (prefixWord ++ tailWord_1389068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389068).length < 2 ^ (prefixWord ++ tailWord_1389068).sum := by decide
  have hdescent : baseEnd_1389068 < baseStart_1389068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389070 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_1389070 : Nat := 118140960795 + 1389070 * 2 ^ 59
def prefixEnd_1389070 : Nat := 4983230072969 + 3 ^ 40 * 1389070 * 2
def baseEnd_1389070 : Nat := 158502349497996775763731

theorem tailTrace_1389070 : CollatzResearch.WordTrace tailWord_1389070 prefixEnd_1389070 158502349497996775763731 := by
  unfold tailWord_1389070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332943134705512389240583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33775696718429399409283109 6332943134705512389240583)
  ·
    refine ⟨9499414702058268583860875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6332943134705512389240583 9499414702058268583860875)
    ·
      refine ⟨14249122053087402875791313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499414702058268583860875 14249122053087402875791313)
      ·
        refine ⟨10686841539815552156843485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14249122053087402875791313 10686841539815552156843485)
        ·
          refine ⟨4007565577430832058816307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10686841539815552156843485 4007565577430832058816307)
          ·
            refine ⟨6011348366146248088224461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007565577430832058816307 6011348366146248088224461)
            ·
              refine ⟨2254255637304843033084173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6011348366146248088224461 2254255637304843033084173)
              ·
                refine ⟨845345863989316137406565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254255637304843033084173 845345863989316137406565)
                ·
                  refine ⟨158502349497996775763731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845345863989316137406565 158502349497996775763731)
                  ·
                    rfl

theorem cell22_1389070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_1389070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389070 prefixEnd_1389070 := by exact prefixLift 1389070
  have htrace : WordTrace (prefixWord ++ tailWord_1389070) baseStart_1389070 baseEnd_1389070 := by
    simpa [prefixWord, tailWord_1389070, baseEnd_1389070] using wordTrace_append hprefix tailTrace_1389070
  have hstable : (prefixWord ++ tailWord_1389070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389070).length < 2 ^ (prefixWord ++ tailWord_1389070).sum := by decide
  have hdescent : baseEnd_1389070 < baseStart_1389070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389098 : List Nat := [3, 1, 4, 1, 1, 3, 2, 7]
def baseStart_1389098 : Nat := 118140960795 + 1389098 * 2 ^ 59
def prefixEnd_1389098 : Nat := 4983230072969 + 3 ^ 40 * 1389098 * 2
def baseEnd_1389098 : Nat := 52835181496245287510123

theorem tailTrace_1389098 : CollatzResearch.WordTrace tailWord_1389098 prefixEnd_1389098 52835181496245287510123 := by
  unfold tailWord_1389098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12666141580385664973985987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33776377547695106597295965 12666141580385664973985987)
  ·
    refine ⟨18999212370578497460978981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12666141580385664973985987 18999212370578497460978981)
    ·
      refine ⟨3562352319483468273933559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18999212370578497460978981 3562352319483468273933559)
      ·
        refine ⟨5343528479225202410900339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562352319483468273933559 5343528479225202410900339)
        ·
          refine ⟨8015292718837803616350509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343528479225202410900339 8015292718837803616350509)
          ·
            refine ⟨3005734769564176356131441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8015292718837803616350509 3005734769564176356131441)
            ·
              refine ⟨2254301077173132267098581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005734769564176356131441 2254301077173132267098581)
              ·
                refine ⟨52835181496245287510123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2254301077173132267098581 52835181496245287510123)
                ·
                  rfl

theorem cell22_1389098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_1389098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389098 prefixEnd_1389098 := by exact prefixLift 1389098
  have htrace : WordTrace (prefixWord ++ tailWord_1389098) baseStart_1389098 baseEnd_1389098 := by
    simpa [prefixWord, tailWord_1389098, baseEnd_1389098] using wordTrace_append hprefix tailTrace_1389098
  have hstable : (prefixWord ++ tailWord_1389098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389098).length < 2 ^ (prefixWord ++ tailWord_1389098).sum := by decide
  have hdescent : baseEnd_1389098 < baseStart_1389098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389102 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1389102 : Nat := 118140960795 + 1389102 * 2 ^ 59
def prefixEnd_1389102 : Nat := 4983230072969 + 3 ^ 40 * 1389102 * 2
def baseEnd_1389102 : Nat := 475518002747952910491095

theorem tailTrace_1389102 : CollatzResearch.WordTrace tailWord_1389102 prefixEnd_1389102 475518002747952910491095 := by
  unfold tailWord_1389102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333089026691021072386195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33776474809018779052726373 6333089026691021072386195)
  ·
    refine ⟨9499633540036531608579293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333089026691021072386195 9499633540036531608579293)
    ·
      refine ⟨3562362577513699353217235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9499633540036531608579293 3562362577513699353217235)
      ·
        refine ⟨5343543866270549029825853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562362577513699353217235 5343543866270549029825853)
        ·
          refine ⟨2003828949851455886184695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5343543866270549029825853 2003828949851455886184695)
          ·
            refine ⟨3005743424777183829277043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003828949851455886184695 3005743424777183829277043)
            ·
              refine ⟨4508615137165775743915565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005743424777183829277043 4508615137165775743915565)
              ·
                refine ⟨1690730676437165903968337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4508615137165775743915565 1690730676437165903968337)
                ·
                  refine ⟨1268048007327874427976253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1690730676437165903968337 1268048007327874427976253)
                  ·
                    refine ⟨475518002747952910491095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268048007327874427976253 475518002747952910491095)
                    ·
                      rfl

theorem cell22_1389102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1389102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389102 prefixEnd_1389102 := by exact prefixLift 1389102
  have htrace : WordTrace (prefixWord ++ tailWord_1389102) baseStart_1389102 baseEnd_1389102 := by
    simpa [prefixWord, tailWord_1389102, baseEnd_1389102] using wordTrace_append hprefix tailTrace_1389102
  have hstable : (prefixWord ++ tailWord_1389102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389102).length < 2 ^ (prefixWord ++ tailWord_1389102).sum := by decide
  have hdescent : baseEnd_1389102 < baseStart_1389102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389113 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_1389113 : Nat := 118140960795 + 1389113 * 2 ^ 59
def prefixEnd_1389113 : Nat := 4983230072969 + 3 ^ 40 * 1389113 * 2
def baseEnd_1389113 : Nat := 475521768272752548466061

theorem tailTrace_1389113 : CollatzResearch.WordTrace tailWord_1389113 prefixEnd_1389113 475521768272752548466061 := by
  unfold tailWord_1389113
  simp only [CollatzResearch.WordTrace]
  refine ⟨50665113416488317457739993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33776742277658878305159995 50665113416488317457739993)
  ·
    refine ⟨37998835062366238093304995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50665113416488317457739993 37998835062366238093304995)
    ·
      refine ⟨56998252593549357139957493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37998835062366238093304995 56998252593549357139957493)
      ·
        refine ⟨5343586180645252231871015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56998252593549357139957493 5343586180645252231871015)
        ·
          refine ⟨8015379270967878347806523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343586180645252231871015 8015379270967878347806523)
          ·
            refine ⟨12023068906451817521709785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8015379270967878347806523 12023068906451817521709785)
            ·
              refine ⟨9017301679838863141282339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12023068906451817521709785 9017301679838863141282339)
              ·
                refine ⟨13525952519758294711923509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9017301679838863141282339 13525952519758294711923509)
                ·
                  refine ⟨1268058048727340129242829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13525952519758294711923509 1268058048727340129242829)
                  ·
                    refine ⟨475521768272752548466061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268058048727340129242829 475521768272752548466061)
                    ·
                      rfl

theorem cell22_1389113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_1389113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389113 prefixEnd_1389113 := by exact prefixLift 1389113
  have htrace : WordTrace (prefixWord ++ tailWord_1389113) baseStart_1389113 baseEnd_1389113 := by
    simpa [prefixWord, tailWord_1389113, baseEnd_1389113] using wordTrace_append hprefix tailTrace_1389113
  have hstable : (prefixWord ++ tailWord_1389113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389113).length < 2 ^ (prefixWord ++ tailWord_1389113).sum := by decide
  have hdescent : baseEnd_1389113 < baseStart_1389113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389143 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 5]
def baseStart_1389143 : Nat := 118140960795 + 1389143 * 2 ^ 59
def prefixEnd_1389143 : Nat := 4983230072969 + 3 ^ 40 * 1389143 * 2
def baseEnd_1389143 : Nat := 158510679295280823405323

theorem tailTrace_1389143 : CollatzResearch.WordTrace tailWord_1389143 prefixEnd_1389143 158510679295280823405323 := by
  unfold tailWord_1389143
  simp only [CollatzResearch.WordTrace]
  refine ⟨50666207606379632581332083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33777471737586421720888055 50666207606379632581332083)
  ·
    refine ⟨75999311409569448871998125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50666207606379632581332083 75999311409569448871998125)
    ·
      refine ⟨28499741778588543326999297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75999311409569448871998125 28499741778588543326999297)
      ·
        refine ⟨21374806333941407495249473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28499741778588543326999297 21374806333941407495249473)
        ·
          refine ⟨16031104750456055621437105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21374806333941407495249473 16031104750456055621437105)
          ·
            refine ⟨12023328562842041716077829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16031104750456055621437105 12023328562842041716077829)
            ·
              refine ⟨2254374105532882821764593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12023328562842041716077829 2254374105532882821764593)
              ·
                refine ⟨1690780579149662116323445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254374105532882821764593 1690780579149662116323445)
                ·
                  refine ⟨158510679295280823405323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690780579149662116323445 158510679295280823405323)
                  ·
                    rfl

theorem cell22_1389143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 5].length) (baseStart_1389143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389143 prefixEnd_1389143 := by exact prefixLift 1389143
  have htrace : WordTrace (prefixWord ++ tailWord_1389143) baseStart_1389143 baseEnd_1389143 := by
    simpa [prefixWord, tailWord_1389143, baseEnd_1389143] using wordTrace_append hprefix tailTrace_1389143
  have hstable : (prefixWord ++ tailWord_1389143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389143).length < 2 ^ (prefixWord ++ tailWord_1389143).sum := by decide
  have hdescent : baseEnd_1389143 < baseStart_1389143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389203 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 4, 3]
def baseStart_1389203 : Nat := 118140960795 + 1389203 * 2 ^ 59
def prefixEnd_1389203 : Nat := 4983230072969 + 3 ^ 40 * 1389203 * 2
def baseEnd_1389203 : Nat := 475552577112022313715785

theorem tailTrace_1389203 : CollatzResearch.WordTrace tailWord_1389203 prefixEnd_1389203 475552577112022313715785 := by
  unfold tailWord_1389203
  simp only [CollatzResearch.WordTrace]
  refine ⟨50668395986162262828516263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33778930657441508552344175 50668395986162262828516263)
  ·
    refine ⟨76002593979243394242774395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50668395986162262828516263 76002593979243394242774395)
    ·
      refine ⟨114003890968865091364161593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76002593979243394242774395 114003890968865091364161593)
      ·
        refine ⟨85502918226648818523121195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114003890968865091364161593 85502918226648818523121195)
        ·
          refine ⟨128254377339973227784681793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85502918226648818523121195 128254377339973227784681793)
          ·
            refine ⟨96190783004979920838511345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128254377339973227784681793 96190783004979920838511345)
            ·
              refine ⟨72143087253734940628883509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96190783004979920838511345 72143087253734940628883509)
              ·
                refine ⟨6763414430037650683957829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72143087253734940628883509 6763414430037650683957829)
                ·
                  refine ⟨1268140205632059503242093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6763414430037650683957829 1268140205632059503242093)
                  ·
                    refine ⟨475552577112022313715785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268140205632059503242093 475552577112022313715785)
                    ·
                      rfl

theorem cell22_1389203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 3].length) (baseStart_1389203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389203 prefixEnd_1389203 := by exact prefixLift 1389203
  have htrace : WordTrace (prefixWord ++ tailWord_1389203) baseStart_1389203 baseEnd_1389203 := by
    simpa [prefixWord, tailWord_1389203, baseEnd_1389203] using wordTrace_append hprefix tailTrace_1389203
  have hstable : (prefixWord ++ tailWord_1389203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389203).length < 2 ^ (prefixWord ++ tailWord_1389203).sum := by decide
  have hdescent : baseEnd_1389203 < baseStart_1389203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389239 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 4]
def baseStart_1389239 : Nat := 118140960795 + 1389239 * 2 ^ 59
def prefixEnd_1389239 : Nat := 4983230072969 + 3 ^ 40 * 1389239 * 2
def baseEnd_1389239 : Nat := 158521633549243406605225

theorem tailTrace_1389239 : CollatzResearch.WordTrace tailWord_1389239 prefixEnd_1389239 158521633549243406605225 := by
  unfold tailWord_1389239
  simp only [CollatzResearch.WordTrace]
  refine ⟨50669709014031840976826771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33779806009354560651217847 50669709014031840976826771)
  ·
    refine ⟨76004563521047761465240157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50669709014031840976826771 76004563521047761465240157)
    ·
      refine ⟨28501711320392910549465059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76004563521047761465240157 28501711320392910549465059)
      ·
        refine ⟨42752566980589365824197589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28501711320392910549465059 42752566980589365824197589)
        ·
          refine ⟨1002013288607563261504631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42752566980589365824197589 1002013288607563261504631)
          ·
            refine ⟨1503019932911344892256947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002013288607563261504631 1503019932911344892256947)
            ·
              refine ⟨2254529899367017338385421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503019932911344892256947 2254529899367017338385421)
              ·
                refine ⟨845448712262631501894533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254529899367017338385421 845448712262631501894533)
                ·
                  refine ⟨158521633549243406605225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845448712262631501894533 158521633549243406605225)
                  ·
                    rfl

theorem cell22_1389239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 4].length) (baseStart_1389239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389239 prefixEnd_1389239 := by exact prefixLift 1389239
  have htrace : WordTrace (prefixWord ++ tailWord_1389239) baseStart_1389239 baseEnd_1389239 := by
    simpa [prefixWord, tailWord_1389239, baseEnd_1389239] using wordTrace_append hprefix tailTrace_1389239
  have hstable : (prefixWord ++ tailWord_1389239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389239).length < 2 ^ (prefixWord ++ tailWord_1389239).sum := by decide
  have hdescent : baseEnd_1389239 < baseStart_1389239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389323 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 6]
def baseStart_1389323 : Nat := 118140960795 + 1389323 * 2 ^ 59
def prefixEnd_1389323 : Nat := 4983230072969 + 3 ^ 40 * 1389323 * 2
def baseEnd_1389323 : Nat := 158531218521460666905139

theorem tailTrace_1389323 : CollatzResearch.WordTrace tailWord_1389323 prefixEnd_1389323 158531218521460666905139 := by
  unfold tailWord_1389323
  simp only [CollatzResearch.WordTrace]
  refine ⟨50672772745727523322884623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33781848497151682215256415 50672772745727523322884623)
  ·
    refine ⟨76009159118591284984326935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50672772745727523322884623 76009159118591284984326935)
    ·
      refine ⟨114013738677886927476490403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76009159118591284984326935 114013738677886927476490403)
      ·
        refine ⟨171020608016830391214735605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114013738677886927476490403 171020608016830391214735605)
        ·
          refine ⟨16033182001577849176381463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171020608016830391214735605 16033182001577849176381463)
          ·
            refine ⟨24049773002366773764572195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16033182001577849176381463 24049773002366773764572195)
            ·
              refine ⟨36074659503550160646858293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24049773002366773764572195 36074659503550160646858293)
              ·
                refine ⟨3381999328457827560642965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36074659503550160646858293 3381999328457827560642965)
                ·
                  refine ⟨158531218521460666905139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3381999328457827560642965 158531218521460666905139)
                  ·
                    rfl

theorem cell22_1389323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_1389323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389323 prefixEnd_1389323 := by exact prefixLift 1389323
  have htrace : WordTrace (prefixWord ++ tailWord_1389323) baseStart_1389323 baseEnd_1389323 := by
    simpa [prefixWord, tailWord_1389323, baseEnd_1389323] using wordTrace_append hprefix tailTrace_1389323
  have hstable : (prefixWord ++ tailWord_1389323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389323).length < 2 ^ (prefixWord ++ tailWord_1389323).sum := by decide
  have hdescent : baseEnd_1389323 < baseStart_1389323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389340 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_1389340 : Nat := 118140960795 + 1389340 * 2 ^ 59
def prefixEnd_1389340 : Nat := 4983230072969 + 3 ^ 40 * 1389340 * 2
def baseEnd_1389340 : Nat := 158533158337266541013455

theorem tailTrace_1389340 : CollatzResearch.WordTrace tailWord_1389340 prefixEnd_1389340 158533158337266541013455 := by
  unfold tailWord_1389340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25336696393332967613126737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33782261857777290150835649 25336696393332967613126737)
  ·
    refine ⟨19002522294999725709845053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25336696393332967613126737 19002522294999725709845053)
    ·
      refine ⟨7125945860624897141191895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19002522294999725709845053 7125945860624897141191895)
      ·
        refine ⟨10688918790937345711787843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7125945860624897141191895 10688918790937345711787843)
        ·
          refine ⟨16033378186406018567681765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10688918790937345711787843 16033378186406018567681765)
          ·
            refine ⟨3006258409951128481440331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16033378186406018567681765 3006258409951128481440331)
            ·
              refine ⟨4509387614926692722160497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006258409951128481440331 4509387614926692722160497)
              ·
                refine ⟨3382040711195019541620373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4509387614926692722160497 3382040711195019541620373)
                ·
                  refine ⟨158533158337266541013455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3382040711195019541620373 158533158337266541013455)
                  ·
                    rfl

theorem cell22_1389340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_1389340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389340 prefixEnd_1389340 := by exact prefixLift 1389340
  have htrace : WordTrace (prefixWord ++ tailWord_1389340) baseStart_1389340 baseEnd_1389340 := by
    simpa [prefixWord, tailWord_1389340, baseEnd_1389340] using wordTrace_append hprefix tailTrace_1389340
  have hstable : (prefixWord ++ tailWord_1389340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389340).length < 2 ^ (prefixWord ++ tailWord_1389340).sum := by decide
  have hdescent : baseEnd_1389340 < baseStart_1389340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389353 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_1389353 : Nat := 118140960795 + 1389353 * 2 ^ 59
def prefixEnd_1389353 : Nat := 4983230072969 + 3 ^ 40 * 1389353 * 2
def baseEnd_1389353 : Nat := 475603925177471922465325

theorem tailTrace_1389353 : CollatzResearch.WordTrace tailWord_1389353 prefixEnd_1389353 475603925177471922465325 := by
  unfold tailWord_1389353
  simp only [CollatzResearch.WordTrace]
  refine ⟨50673866935618838446476713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33782577957079225630984475 50673866935618838446476713)
  ·
    refine ⟨38005400201714128834857535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50673866935618838446476713 38005400201714128834857535)
    ·
      refine ⟨57008100302571193252286303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38005400201714128834857535 57008100302571193252286303)
      ·
        refine ⟨85512150453856789878429455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57008100302571193252286303 85512150453856789878429455)
        ·
          refine ⟨128268225680785184817644183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85512150453856789878429455 128268225680785184817644183)
          ·
            refine ⟨192402338521177777226466275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128268225680785184817644183 192402338521177777226466275)
            ·
              refine ⟨288603507781766665839699413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192402338521177777226466275 288603507781766665839699413)
              ·
                refine ⟨6764144713635156230617955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 288603507781766665839699413 6764144713635156230617955)
                ·
                  refine ⟨10146217070452734345926933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6764144713635156230617955 10146217070452734345926933)
                  ·
                    refine ⟨475603925177471922465325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10146217070452734345926933 475603925177471922465325)
                    ·
                      rfl

theorem cell22_1389353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_1389353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389353 prefixEnd_1389353 := by exact prefixLift 1389353
  have htrace : WordTrace (prefixWord ++ tailWord_1389353) baseStart_1389353 baseEnd_1389353 := by
    simpa [prefixWord, tailWord_1389353, baseEnd_1389353] using wordTrace_append hprefix tailTrace_1389353
  have hstable : (prefixWord ++ tailWord_1389353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389353).length < 2 ^ (prefixWord ++ tailWord_1389353).sum := by decide
  have hdescent : baseEnd_1389353 < baseStart_1389353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389368 : List Nat := [2, 1, 2, 1, 3, 2, 11]
def baseStart_1389368 : Nat := 118140960795 + 1389368 * 2 ^ 59
def prefixEnd_1389368 : Nat := 4983230072969 + 3 ^ 40 * 1389368 * 2
def baseEnd_1389368 : Nat := 17615150369778403086677

theorem tailTrace_1389368 : CollatzResearch.WordTrace tailWord_1389368 prefixEnd_1389368 17615150369778403086677 := by
  unfold tailWord_1389368
  simp only [CollatzResearch.WordTrace]
  refine ⟨25337207015282248004136379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33782942687042997338848505 25337207015282248004136379)
  ·
    refine ⟨38005810522923372006204569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25337207015282248004136379 38005810522923372006204569)
    ·
      refine ⟨28504357892192529004653427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38005810522923372006204569 28504357892192529004653427)
      ·
        refine ⟨42756536838288793506980141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28504357892192529004653427 42756536838288793506980141)
        ·
          refine ⟨16033701314358297565117553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42756536838288793506980141 16033701314358297565117553)
          ·
            refine ⟨12025275985768723173838165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16033701314358297565117553 12025275985768723173838165)
            ·
              refine ⟨17615150369778403086677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12025275985768723173838165 17615150369778403086677)
              ·
                rfl

theorem cell22_1389368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 11].length) (baseStart_1389368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389368 prefixEnd_1389368 := by exact prefixLift 1389368
  have htrace : WordTrace (prefixWord ++ tailWord_1389368) baseStart_1389368 baseEnd_1389368 := by
    simpa [prefixWord, tailWord_1389368, baseEnd_1389368] using wordTrace_append hprefix tailTrace_1389368
  have hstable : (prefixWord ++ tailWord_1389368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389368).length < 2 ^ (prefixWord ++ tailWord_1389368).sum := by decide
  have hdescent : baseEnd_1389368 < baseStart_1389368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389402 : List Nat := [3, 1, 1, 2, 1, 6, 2, 6]
def baseStart_1389402 : Nat := 118140960795 + 1389402 * 2 ^ 59
def prefixEnd_1389402 : Nat := 4983230072969 + 3 ^ 40 * 1389402 * 2
def baseEnd_1389402 : Nat := 52846744319872458665575

theorem tailTrace_1389402 : CollatzResearch.WordTrace tailWord_1389402 prefixEnd_1389402 52846744319872458665575 := by
  unfold tailWord_1389402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12668913528110329953752615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33783769408294213210006973 12668913528110329953752615)
  ·
    refine ⟨19003370292165494930628923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12668913528110329953752615 19003370292165494930628923)
    ·
      refine ⟨28505055438248242395943385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19003370292165494930628923 28505055438248242395943385)
      ·
        refine ⟨21378791578686181796957539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28505055438248242395943385 21378791578686181796957539)
        ·
          refine ⟨32068187368029272695436309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21378791578686181796957539 32068187368029272695436309)
          ·
            refine ⟨1503196282876372157598577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32068187368029272695436309 1503196282876372157598577)
            ·
              refine ⟨1127397212157279118198933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1503196282876372157598577 1127397212157279118198933)
              ·
                refine ⟨52846744319872458665575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1127397212157279118198933 52846744319872458665575)
                ·
                  rfl

theorem cell22_1389402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_1389402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389402 prefixEnd_1389402 := by exact prefixLift 1389402
  have htrace : WordTrace (prefixWord ++ tailWord_1389402) baseStart_1389402 baseEnd_1389402 := by
    simpa [prefixWord, tailWord_1389402, baseEnd_1389402] using wordTrace_append hprefix tailTrace_1389402
  have hstable : (prefixWord ++ tailWord_1389402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389402).length < 2 ^ (prefixWord ++ tailWord_1389402).sum := by decide
  have hdescent : baseEnd_1389402 < baseStart_1389402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389447 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 5]
def baseStart_1389447 : Nat := 118140960795 + 1389447 * 2 ^ 59
def prefixEnd_1389447 : Nat := 4983230072969 + 3 ^ 40 * 1389447 * 2
def baseEnd_1389447 : Nat := 158545367766162336871679

theorem tailTrace_1389447 : CollatzResearch.WordTrace tailWord_1389447 prefixEnd_1389447 158545367766162336871679 := by
  unfold tailWord_1389447
  simp only [CollatzResearch.WordTrace]
  refine ⟨50677295397278292500398595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33784863598185528333599063 50677295397278292500398595)
  ·
    refine ⟨76015943095917438750597893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50677295397278292500398595 76015943095917438750597893)
    ·
      refine ⟨14252989330484519765737105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76015943095917438750597893 14252989330484519765737105)
      ·
        refine ⟨10689741997863389824302829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14252989330484519765737105 10689741997863389824302829)
        ·
          refine ⟨4008653249198771184113561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10689741997863389824302829 4008653249198771184113561)
          ·
            refine ⟨3006489936899078388085171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4008653249198771184113561 3006489936899078388085171)
            ·
              refine ⟨4509734905348617582127757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006489936899078388085171 4509734905348617582127757)
              ·
                refine ⟨1691150589505731593297909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4509734905348617582127757 1691150589505731593297909)
                ·
                  refine ⟨158545367766162336871679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691150589505731593297909 158545367766162336871679)
                  ·
                    rfl

theorem cell22_1389447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 5].length) (baseStart_1389447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389447 prefixEnd_1389447 := by exact prefixLift 1389447
  have htrace : WordTrace (prefixWord ++ tailWord_1389447) baseStart_1389447 baseEnd_1389447 := by
    simpa [prefixWord, tailWord_1389447, baseEnd_1389447] using wordTrace_append hprefix tailTrace_1389447
  have hstable : (prefixWord ++ tailWord_1389447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389447).length < 2 ^ (prefixWord ++ tailWord_1389447).sum := by decide
  have hdescent : baseEnd_1389447 < baseStart_1389447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389526 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1389526 : Nat := 118140960795 + 1389526 * 2 ^ 59
def prefixEnd_1389526 : Nat := 4983230072969 + 3 ^ 40 * 1389526 * 2
def baseEnd_1389526 : Nat := 158554382204319045963265

theorem tailTrace_1389526 : CollatzResearch.WordTrace tailWord_1389526 prefixEnd_1389526 158554382204319045963265 := by
  unfold tailWord_1389526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167511047749505562032777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33786784509328059328349621 3167511047749505562032777)
  ·
    refine ⟨2375633285812129171524583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3167511047749505562032777 2375633285812129171524583)
    ·
      refine ⟨3563449928718193757286875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375633285812129171524583 3563449928718193757286875)
      ·
        refine ⟨5345174893077290635930313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563449928718193757286875 5345174893077290635930313)
        ·
          refine ⟨4008881169807967976947735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5345174893077290635930313 4008881169807967976947735)
          ·
            refine ⟨6013321754711951965421603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008881169807967976947735 6013321754711951965421603)
            ·
              refine ⟨9019982632067927948132405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013321754711951965421603 9019982632067927948132405)
              ·
                refine ⟨845623371756368245137413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9019982632067927948132405 845623371756368245137413)
                ·
                  refine ⟨158554382204319045963265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845623371756368245137413 158554382204319045963265)
                  ·
                    rfl

theorem cell22_1389526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1389526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389526 prefixEnd_1389526 := by exact prefixLift 1389526
  have htrace : WordTrace (prefixWord ++ tailWord_1389526) baseStart_1389526 baseEnd_1389526 := by
    simpa [prefixWord, tailWord_1389526, baseEnd_1389526] using wordTrace_append hprefix tailTrace_1389526
  have hstable : (prefixWord ++ tailWord_1389526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389526).length < 2 ^ (prefixWord ++ tailWord_1389526).sum := by decide
  have hdescent : baseEnd_1389526 < baseStart_1389526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389541 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_1389541 : Nat := 118140960795 + 1389541 * 2 ^ 59
def prefixEnd_1389541 : Nat := 4983230072969 + 3 ^ 40 * 1389541 * 2
def baseEnd_1389541 : Nat := 475668281419502098764749

theorem tailTrace_1389541 : CollatzResearch.WordTrace tailWord_1389541 prefixEnd_1389541 475668281419502098764749 := by
  unfold tailWord_1389541
  simp only [CollatzResearch.WordTrace]
  refine ⟨50680723858937746554320477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33787149239291831036213651 50680723858937746554320477)
  ·
    refine ⟨19005271447101654957870179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50680723858937746554320477 19005271447101654957870179)
    ·
      refine ⟨28507907170652482436805269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19005271447101654957870179 28507907170652482436805269)
      ·
        refine ⟨1336308148624335114225247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28507907170652482436805269 1336308148624335114225247)
        ·
          refine ⟨2004462222936502671337871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336308148624335114225247 2004462222936502671337871)
          ·
            refine ⟨3006693334404754007006807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004462222936502671337871 3006693334404754007006807)
            ·
              refine ⟨4510040001607131010510211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006693334404754007006807 4510040001607131010510211)
              ·
                refine ⟨6765060002410696515765317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510040001607131010510211 6765060002410696515765317)
                ·
                  refine ⟨1268448750452005596705997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6765060002410696515765317 1268448750452005596705997)
                  ·
                    refine ⟨475668281419502098764749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268448750452005596705997 475668281419502098764749)
                    ·
                      rfl

theorem cell22_1389541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_1389541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389541 prefixEnd_1389541 := by exact prefixLift 1389541
  have htrace : WordTrace (prefixWord ++ tailWord_1389541) baseStart_1389541 baseEnd_1389541 := by
    simpa [prefixWord, tailWord_1389541, baseEnd_1389541] using wordTrace_append hprefix tailTrace_1389541
  have hstable : (prefixWord ++ tailWord_1389541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389541).length < 2 ^ (prefixWord ++ tailWord_1389541).sum := by decide
  have hdescent : baseEnd_1389541 < baseStart_1389541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389558 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_1389558 : Nat := 118140960795 + 1389558 * 2 ^ 59
def prefixEnd_1389558 : Nat := 4983230072969 + 3 ^ 40 * 1389558 * 2
def baseEnd_1389558 : Nat := 475674100866919721089697

theorem tailTrace_1389558 : CollatzResearch.WordTrace tailWord_1389558 prefixEnd_1389558 475674100866919721089697 := by
  unfold tailWord_1389558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167583993742259903605583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33787562599917438971792885 3167583993742259903605583)
  ·
    refine ⟨4751375990613389855408375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167583993742259903605583 4751375990613389855408375)
    ·
      refine ⟨7127063985920084783112563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751375990613389855408375 7127063985920084783112563)
      ·
        refine ⟨10690595978880127174668845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127063985920084783112563 10690595978880127174668845)
        ·
          refine ⟨4008973492080047690500817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10690595978880127174668845 4008973492080047690500817)
          ·
            refine ⟨3006730119060035767875613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4008973492080047690500817 3006730119060035767875613)
            ·
              refine ⟨1127523794647513412953355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3006730119060035767875613 1127523794647513412953355)
              ·
                refine ⟨1691285691971270119430033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127523794647513412953355 1691285691971270119430033)
                ·
                  refine ⟨1268464268978452589572525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1691285691971270119430033 1268464268978452589572525)
                  ·
                    refine ⟨475674100866919721089697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268464268978452589572525 475674100866919721089697)
                    ·
                      rfl

theorem cell22_1389558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_1389558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389558 prefixEnd_1389558 := by exact prefixLift 1389558
  have htrace : WordTrace (prefixWord ++ tailWord_1389558) baseStart_1389558 baseEnd_1389558 := by
    simpa [prefixWord, tailWord_1389558, baseEnd_1389558] using wordTrace_append hprefix tailTrace_1389558
  have hstable : (prefixWord ++ tailWord_1389558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389558).length < 2 ^ (prefixWord ++ tailWord_1389558).sum := by decide
  have hdescent : baseEnd_1389558 < baseStart_1389558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389569 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1389569 : Nat := 118140960795 + 1389569 * 2 ^ 59
def prefixEnd_1389569 : Nat := 4983230072969 + 3 ^ 40 * 1389569 * 2
def baseEnd_1389569 : Nat := 475677866391719359064663

theorem tailTrace_1389569 : CollatzResearch.WordTrace tailWord_1389569 prefixEnd_1389569 475677866391719359064663 := by
  unfold tailWord_1389569
  simp only [CollatzResearch.WordTrace]
  refine ⟨50681745102836307336339761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33787830068557538224226507 50681745102836307336339761)
  ·
    refine ⟨38011308827127230502254821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50681745102836307336339761 38011308827127230502254821)
    ·
      refine ⟨7127120405086355719172779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38011308827127230502254821 7127120405086355719172779)
      ·
        refine ⟨10690680607629533578759169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127120405086355719172779 10690680607629533578759169)
        ·
          refine ⟨8018010455722150184069377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10690680607629533578759169 8018010455722150184069377)
          ·
            refine ⟨6013507841791612638052033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8018010455722150184069377 6013507841791612638052033)
            ·
              refine ⟨4510130881343709478539025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6013507841791612638052033 4510130881343709478539025)
              ·
                refine ⟨3382598161007782108904269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510130881343709478539025 3382598161007782108904269)
                ·
                  refine ⟨1268474310377918290839101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3382598161007782108904269 1268474310377918290839101)
                  ·
                    refine ⟨475677866391719359064663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268474310377918290839101 475677866391719359064663)
                    ·
                      rfl

theorem cell22_1389569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1389569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389569 prefixEnd_1389569 := by exact prefixLift 1389569
  have htrace : WordTrace (prefixWord ++ tailWord_1389569) baseStart_1389569 baseEnd_1389569 := by
    simpa [prefixWord, tailWord_1389569, baseEnd_1389569] using wordTrace_append hprefix tailTrace_1389569
  have hstable : (prefixWord ++ tailWord_1389569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389569).length < 2 ^ (prefixWord ++ tailWord_1389569).sum := by decide
  have hdescent : baseEnd_1389569 < baseStart_1389569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389582 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_1389582 : Nat := 118140960795 + 1389582 * 2 ^ 59
def prefixEnd_1389582 : Nat := 4983230072969 + 3 ^ 40 * 1389582 * 2
def baseEnd_1389582 : Nat := 158560772185797219496541

theorem tailTrace_1389582 : CollatzResearch.WordTrace tailWord_1389582 prefixEnd_1389582 158560772185797219496541 := by
  unfold tailWord_1389582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335277406473651319570375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33788146167859473704375333 6335277406473651319570375)
  ·
    refine ⟨9502916109710476979355563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6335277406473651319570375 9502916109710476979355563)
    ·
      refine ⟨14254374164565715469033345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9502916109710476979355563 14254374164565715469033345)
      ·
        refine ⟨10690780623424286601775009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14254374164565715469033345 10690780623424286601775009)
        ·
          refine ⟨8018085467568214951331257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10690780623424286601775009 8018085467568214951331257)
          ·
            refine ⟨6013564100676161213498443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8018085467568214951331257 6013564100676161213498443)
            ·
              refine ⟨9020346151014241820247665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013564100676161213498443 9020346151014241820247665)
              ·
                refine ⟨6765259613260681365185749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9020346151014241820247665 6765259613260681365185749)
                ·
                  refine ⟨158560772185797219496541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6765259613260681365185749 158560772185797219496541)
                  ·
                    rfl

theorem cell22_1389582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_1389582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389582 prefixEnd_1389582 := by exact prefixLift 1389582
  have htrace : WordTrace (prefixWord ++ tailWord_1389582) baseStart_1389582 baseEnd_1389582 := by
    simpa [prefixWord, tailWord_1389582, baseEnd_1389582] using wordTrace_append hprefix tailTrace_1389582
  have hstable : (prefixWord ++ tailWord_1389582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389582).length < 2 ^ (prefixWord ++ tailWord_1389582).sum := by decide
  have hdescent : baseEnd_1389582 < baseStart_1389582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389595 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_1389595 : Nat := 118140960795 + 1389595 * 2 ^ 59
def prefixEnd_1389595 : Nat := 4983230072969 + 3 ^ 40 * 1389595 * 2
def baseEnd_1389595 : Nat := 475686766723063957914583

theorem tailTrace_1389595 : CollatzResearch.WordTrace tailWord_1389595 prefixEnd_1389595 475686766723063957914583 := by
  unfold tailWord_1389595
  simp only [CollatzResearch.WordTrace]
  refine ⟨50682693400742113776786239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33788462267161409184524159 50682693400742113776786239)
  ·
    refine ⟨76024040101113170665179359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50682693400742113776786239 76024040101113170665179359)
    ·
      refine ⟨114036060151669755997769039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76024040101113170665179359 114036060151669755997769039)
      ·
        refine ⟨171054090227504633996653559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114036060151669755997769039 171054090227504633996653559)
        ·
          refine ⟨256581135341256950994980339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171054090227504633996653559 256581135341256950994980339)
          ·
            refine ⟨384871703011885426492470509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256581135341256950994980339 384871703011885426492470509)
            ·
              refine ⟨144326888629457034934676441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384871703011885426492470509 144326888629457034934676441)
              ·
                refine ⟨108245166472092776201007331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144326888629457034934676441 108245166472092776201007331)
                ·
                  refine ⟨162367749708139164301510997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108245166472092776201007331 162367749708139164301510997)
                  ·
                    refine ⟨475686766723063957914583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 162367749708139164301510997 475686766723063957914583)
                    ·
                      rfl

theorem cell22_1389595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_1389595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389595 prefixEnd_1389595 := by exact prefixLift 1389595
  have htrace : WordTrace (prefixWord ++ tailWord_1389595) baseStart_1389595 baseEnd_1389595 := by
    simpa [prefixWord, tailWord_1389595, baseEnd_1389595] using wordTrace_append hprefix tailTrace_1389595
  have hstable : (prefixWord ++ tailWord_1389595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389595).length < 2 ^ (prefixWord ++ tailWord_1389595).sum := by decide
  have hdescent : baseEnd_1389595 < baseStart_1389595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389603 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 1, 3]
def baseStart_1389603 : Nat := 118140960795 + 1389603 * 2 ^ 59
def prefixEnd_1389603 : Nat := 4983230072969 + 3 ^ 40 * 1389603 * 2
def baseEnd_1389603 : Nat := 475689505286554603714559

theorem tailTrace_1389603 : CollatzResearch.WordTrace tailWord_1389603 prefixEnd_1389603 475689505286554603714559 := by
  unfold tailWord_1389603
  simp only [CollatzResearch.WordTrace]
  refine ⟨50682985184713131143077463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33788656789808754095384975 50682985184713131143077463)
  ·
    refine ⟨76024477777069696714616195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50682985184713131143077463 76024477777069696714616195)
    ·
      refine ⟨114036716665604545071924293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76024477777069696714616195 114036716665604545071924293)
      ·
        refine ⟨21381884374800852200985805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114036716665604545071924293 21381884374800852200985805)
        ·
          refine ⟨8018206640550319575369677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21381884374800852200985805 8018206640550319575369677)
          ·
            refine ⟨3006827490206369840763629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8018206640550319575369677 3006827490206369840763629)
            ·
              refine ⟨1127560308827388690286361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3006827490206369840763629 1127560308827388690286361)
              ·
                refine ⟨845670231620541517714771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127560308827388690286361 845670231620541517714771)
                ·
                  refine ⟨1268505347430812276572157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845670231620541517714771 1268505347430812276572157)
                  ·
                    refine ⟨475689505286554603714559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268505347430812276572157 475689505286554603714559)
                    ·
                      rfl

theorem cell22_1389603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 3].length) (baseStart_1389603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389603 prefixEnd_1389603 := by exact prefixLift 1389603
  have htrace : WordTrace (prefixWord ++ tailWord_1389603) baseStart_1389603 baseEnd_1389603 := by
    simpa [prefixWord, tailWord_1389603, baseEnd_1389603] using wordTrace_append hprefix tailTrace_1389603
  have hstable : (prefixWord ++ tailWord_1389603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389603).length < 2 ^ (prefixWord ++ tailWord_1389603).sum := by decide
  have hdescent : baseEnd_1389603 < baseStart_1389603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389612 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1389612 : Nat := 118140960795 + 1389612 * 2 ^ 59
def prefixEnd_1389612 : Nat := 4983230072969 + 3 ^ 40 * 1389612 * 2
def baseEnd_1389612 : Nat := 475692586170481580239531

theorem tailTrace_1389612 : CollatzResearch.WordTrace tailWord_1389612 prefixEnd_1389612 475692586170481580239531 := by
  unfold tailWord_1389612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25341656720840262840077545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33788875627787017120103393 25341656720840262840077545)
  ·
    refine ⟨19006242540630197130058159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25341656720840262840077545 19006242540630197130058159)
    ·
      refine ⟨28509363810945295695087239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19006242540630197130058159 28509363810945295695087239)
      ·
        refine ⟨42764045716417943542630859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28509363810945295695087239 42764045716417943542630859)
        ·
          refine ⟨64146068574626915313946289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42764045716417943542630859 64146068574626915313946289)
          ·
            refine ⟨48109551430970186485459717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64146068574626915313946289 48109551430970186485459717)
            ·
              refine ⟨9020540893306909966023697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48109551430970186485459717 9020540893306909966023697)
              ·
                refine ⟨6765405669980182474517773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9020540893306909966023697 6765405669980182474517773)
                ·
                  refine ⟨2537027126242568427944165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6765405669980182474517773 2537027126242568427944165)
                  ·
                    refine ⟨475692586170481580239531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537027126242568427944165 475692586170481580239531)
                    ·
                      rfl

theorem cell22_1389612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1389612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389612 prefixEnd_1389612 := by exact prefixLift 1389612
  have htrace : WordTrace (prefixWord ++ tailWord_1389612) baseStart_1389612 baseEnd_1389612 := by
    simpa [prefixWord, tailWord_1389612, baseEnd_1389612] using wordTrace_append hprefix tailTrace_1389612
  have hstable : (prefixWord ++ tailWord_1389612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389612).length < 2 ^ (prefixWord ++ tailWord_1389612).sum := by decide
  have hdescent : baseEnd_1389612 < baseStart_1389612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389629 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_1389629 : Nat := 118140960795 + 1389629 * 2 ^ 59
def prefixEnd_1389629 : Nat := 4983230072969 + 3 ^ 40 * 1389629 * 2
def baseEnd_1389629 : Nat := 475698405617899202564479

theorem tailTrace_1389629 : CollatzResearch.WordTrace tailWord_1389629 prefixEnd_1389629 475698405617899202564479 := by
  unfold tailWord_1389629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50683933482618937583523941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33789288988412625055682627 50683933482618937583523941)
  ·
    refine ⟨9503237527991050796910739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50683933482618937583523941 9503237527991050796910739)
    ·
      refine ⟨14254856291986576195366109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503237527991050796910739 14254856291986576195366109)
      ·
        refine ⟨5345571109494966073262291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14254856291986576195366109 5345571109494966073262291)
        ·
          refine ⟨8018356664242449109893437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5345571109494966073262291 8018356664242449109893437)
          ·
            refine ⟨3006883749090918416210039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8018356664242449109893437 3006883749090918416210039)
            ·
              refine ⟨4510325623636377624315059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006883749090918416210039 4510325623636377624315059)
              ·
                refine ⟨6765488435454566436472589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510325623636377624315059 6765488435454566436472589)
                ·
                  refine ⟨2537058163295462413677221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6765488435454566436472589 2537058163295462413677221)
                  ·
                    refine ⟨475698405617899202564479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537058163295462413677221 475698405617899202564479)
                    ·
                      rfl

theorem cell22_1389629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_1389629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389629 prefixEnd_1389629 := by exact prefixLift 1389629
  have htrace : WordTrace (prefixWord ++ tailWord_1389629) baseStart_1389629 baseEnd_1389629 := by
    simpa [prefixWord, tailWord_1389629, baseEnd_1389629] using wordTrace_append hprefix tailTrace_1389629
  have hstable : (prefixWord ++ tailWord_1389629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389629).length < 2 ^ (prefixWord ++ tailWord_1389629).sum := by decide
  have hdescent : baseEnd_1389629 < baseStart_1389629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389642 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1389642 : Nat := 118140960795 + 1389642 * 2 ^ 59
def prefixEnd_1389642 : Nat := 4983230072969 + 3 ^ 40 * 1389642 * 2
def baseEnd_1389642 : Nat := 475702855783571501989439

theorem tailTrace_1389642 : CollatzResearch.WordTrace tailWord_1389642 prefixEnd_1389642 475702855783571501989439 := by
  unfold tailWord_1389642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671101907892960200936795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33789605087714560535831453 12671101907892960200936795)
  ·
    refine ⟨19006652861839440301405193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12671101907892960200936795 19006652861839440301405193)
    ·
      refine ⟨14254989646379580226053895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19006652861839440301405193 14254989646379580226053895)
      ·
        refine ⟨21382484469569370339080843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14254989646379580226053895 21382484469569370339080843)
        ·
          refine ⟨32073726704354055508621265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21382484469569370339080843 32073726704354055508621265)
          ·
            refine ⟨24055295028265541631465949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32073726704354055508621265 24055295028265541631465949)
            ·
              refine ⟨9020735635599578111799731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24055295028265541631465949 9020735635599578111799731)
              ·
                refine ⟨13531103453399367167699597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9020735635599578111799731 13531103453399367167699597)
                ·
                  refine ⟨5074163795024762687887349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13531103453399367167699597 5074163795024762687887349)
                  ·
                    refine ⟨475702855783571501989439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5074163795024762687887349 475702855783571501989439)
                    ·
                      rfl

theorem cell22_1389642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1389642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389642 prefixEnd_1389642 := by exact prefixLift 1389642
  have htrace : WordTrace (prefixWord ++ tailWord_1389642) baseStart_1389642 baseEnd_1389642 := by
    simpa [prefixWord, tailWord_1389642, baseEnd_1389642] using wordTrace_append hprefix tailTrace_1389642
  have hstable : (prefixWord ++ tailWord_1389642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389642).length < 2 ^ (prefixWord ++ tailWord_1389642).sum := by decide
  have hdescent : baseEnd_1389642 < baseStart_1389642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389644 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 4]
def baseStart_1389644 : Nat := 118140960795 + 1389644 * 2 ^ 59
def prefixEnd_1389644 : Nat := 4983230072969 + 3 ^ 40 * 1389644 * 2
def baseEnd_1389644 : Nat := 158567846808148054479811

theorem tailTrace_1389644 : CollatzResearch.WordTrace tailWord_1389644 prefixEnd_1389644 158567846808148054479811 := by
  unfold tailWord_1389644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342240288782297572659993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33789653718376396763546657 25342240288782297572659993)
  ·
    refine ⟨19006680216586723179494995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25342240288782297572659993 19006680216586723179494995)
    ·
      refine ⟨28510020324880084769242493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19006680216586723179494995 28510020324880084769242493)
      ·
        refine ⟨10691257621830031788465935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28510020324880084769242493 10691257621830031788465935)
        ·
          refine ⟨16036886432745047682698903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10691257621830031788465935 16036886432745047682698903)
          ·
            refine ⟨24055329649117571524048355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036886432745047682698903 24055329649117571524048355)
            ·
              refine ⟨36082994473676357286072533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24055329649117571524048355 36082994473676357286072533)
              ·
                refine ⟨845695182976789623892325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36082994473676357286072533 845695182976789623892325)
                ·
                  refine ⟨158567846808148054479811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845695182976789623892325 158567846808148054479811)
                  ·
                    rfl

theorem cell22_1389644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_1389644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389644 prefixEnd_1389644 := by exact prefixLift 1389644
  have htrace : WordTrace (prefixWord ++ tailWord_1389644) baseStart_1389644 baseEnd_1389644 := by
    simpa [prefixWord, tailWord_1389644, baseEnd_1389644] using wordTrace_append hprefix tailTrace_1389644
  have hstable : (prefixWord ++ tailWord_1389644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389644).length < 2 ^ (prefixWord ++ tailWord_1389644).sum := by decide
  have hdescent : baseEnd_1389644 < baseStart_1389644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389646 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_1389646 : Nat := 118140960795 + 1389646 * 2 ^ 59
def prefixEnd_1389646 : Nat := 4983230072969 + 3 ^ 40 * 1389646 * 2
def baseEnd_1389646 : Nat := 475704225065316824889427

theorem tailTrace_1389646 : CollatzResearch.WordTrace tailWord_1389646 prefixEnd_1389646 475704225065316824889427 := by
  unfold tailWord_1389646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335569190444668685861599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33789702349038232991261861 6335569190444668685861599)
  ·
    refine ⟨9503353785667003028792399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6335569190444668685861599 9503353785667003028792399)
    ·
      refine ⟨14255030678500504543188599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503353785667003028792399 14255030678500504543188599)
      ·
        refine ⟨21382546017750756814782899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14255030678500504543188599 21382546017750756814782899)
        ·
          refine ⟨32073819026626135222174349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21382546017750756814782899 32073819026626135222174349)
          ·
            refine ⟨12027682134984800708315381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32073819026626135222174349 12027682134984800708315381)
            ·
              refine ⟨1127595200154825066404567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12027682134984800708315381 1127595200154825066404567)
              ·
                refine ⟨1691392800232237599606851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127595200154825066404567 1691392800232237599606851)
                ·
                  refine ⟨2537089200348356399410277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691392800232237599606851 2537089200348356399410277)
                  ·
                    refine ⟨475704225065316824889427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537089200348356399410277 475704225065316824889427)
                    ·
                      rfl

theorem cell22_1389646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_1389646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389646 prefixEnd_1389646 := by exact prefixLift 1389646
  have htrace : WordTrace (prefixWord ++ tailWord_1389646) baseStart_1389646 baseEnd_1389646 := by
    simpa [prefixWord, tailWord_1389646, baseEnd_1389646] using wordTrace_append hprefix tailTrace_1389646
  have hstable : (prefixWord ++ tailWord_1389646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389646).length < 2 ^ (prefixWord ++ tailWord_1389646).sum := by decide
  have hdescent : baseEnd_1389646 < baseStart_1389646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389654 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1389654 : Nat := 118140960795 + 1389654 * 2 ^ 59
def prefixEnd_1389654 : Nat := 4983230072969 + 3 ^ 40 * 1389654 * 2
def baseEnd_1389654 : Nat := 475706963628807470689403

theorem tailTrace_1389654 : CollatzResearch.WordTrace tailWord_1389654 prefixEnd_1389654 475706963628807470689403 := by
  unfold tailWord_1389654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167802831720522928324001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33789896871685577902122677 3167802831720522928324001)
  ·
    refine ⟨2375852123790392196243001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3167802831720522928324001 2375852123790392196243001)
    ·
      refine ⟨1781889092842794147182251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375852123790392196243001 1781889092842794147182251)
      ·
        refine ⟨2672833639264191220773377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781889092842794147182251 2672833639264191220773377)
        ·
          refine ⟨2004625229448143415580033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2672833639264191220773377 2004625229448143415580033)
          ·
            refine ⟨1503468922086107561685025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004625229448143415580033 1503468922086107561685025)
            ·
              refine ⟨1127601691564580671263769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1503468922086107561685025 1127601691564580671263769)
              ·
                refine ⟨845701268673435503447827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127601691564580671263769 845701268673435503447827)
                ·
                  refine ⟨1268551903010153255171741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845701268673435503447827 1268551903010153255171741)
                  ·
                    refine ⟨475706963628807470689403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268551903010153255171741 475706963628807470689403)
                    ·
                      rfl

theorem cell22_1389654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1389654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389654 prefixEnd_1389654 := by exact prefixLift 1389654
  have htrace : WordTrace (prefixWord ++ tailWord_1389654) baseStart_1389654 baseEnd_1389654 := by
    simpa [prefixWord, tailWord_1389654, baseEnd_1389654] using wordTrace_append hprefix tailTrace_1389654
  have hstable : (prefixWord ++ tailWord_1389654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389654).length < 2 ^ (prefixWord ++ tailWord_1389654).sum := by decide
  have hdescent : baseEnd_1389654 < baseStart_1389654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389657 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_1389657 : Nat := 118140960795 + 1389657 * 2 ^ 59
def prefixEnd_1389657 : Nat := 4983230072969 + 3 ^ 40 * 1389657 * 2
def baseEnd_1389657 : Nat := 475707990590116462864393

theorem tailTrace_1389657 : CollatzResearch.WordTrace tailWord_1389657 prefixEnd_1389657 475707990590116462864393 := by
  unfold tailWord_1389657
  simp only [CollatzResearch.WordTrace]
  refine ⟨50684954726517498365543225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33789969817678332243695483 50684954726517498365543225)
  ·
    refine ⟨38013716044888123774157419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50684954726517498365543225 38013716044888123774157419)
    ·
      refine ⟨57020574067332185661236129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38013716044888123774157419 57020574067332185661236129)
      ·
        refine ⟨42765430550499139245927097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57020574067332185661236129 42765430550499139245927097)
        ·
          refine ⟨32074072912874354434445323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42765430550499139245927097 32074072912874354434445323)
          ·
            refine ⟨48111109369311531651667985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32074072912874354434445323 48111109369311531651667985)
            ·
              refine ⟨36083332026983648738750989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48111109369311531651667985 36083332026983648738750989)
              ·
                refine ⟨13531249510118868277031621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36083332026983648738750989 13531249510118868277031621)
                ·
                  refine ⟨2537109283147287801943429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13531249510118868277031621 2537109283147287801943429)
                  ·
                    refine ⟨475707990590116462864393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537109283147287801943429 475707990590116462864393)
                    ·
                      rfl

theorem cell22_1389657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_1389657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389657 prefixEnd_1389657 := by exact prefixLift 1389657
  have htrace : WordTrace (prefixWord ++ tailWord_1389657) baseStart_1389657 baseEnd_1389657 := by
    simpa [prefixWord, tailWord_1389657, baseEnd_1389657] using wordTrace_append hprefix tailTrace_1389657
  have hstable : (prefixWord ++ tailWord_1389657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389657).length < 2 ^ (prefixWord ++ tailWord_1389657).sum := by decide
  have hdescent : baseEnd_1389657 < baseStart_1389657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389738 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1389738 : Nat := 118140960795 + 1389738 * 2 ^ 59
def prefixEnd_1389738 : Nat := 4983230072969 + 3 ^ 40 * 1389738 * 2
def baseEnd_1389738 : Nat := 475735718545459251589145

theorem tailTrace_1389738 : CollatzResearch.WordTrace tailWord_1389738 prefixEnd_1389738 475735718545459251589145 := by
  unfold tailWord_1389738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671977259806012299810467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33791939359482699466161245 12671977259806012299810467)
  ·
    refine ⟨19007965889709018449715701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12671977259806012299810467 19007965889709018449715701)
    ·
      refine ⟨1781996802160220479660847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19007965889709018449715701 1781996802160220479660847)
      ·
        refine ⟨2672995203240330719491271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781996802160220479660847 2672995203240330719491271)
        ·
          refine ⟨4009492804860496079236907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672995203240330719491271 4009492804860496079236907)
          ·
            refine ⟨6014239207290744118855361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009492804860496079236907 6014239207290744118855361)
            ·
              refine ⟨4510679405468058089141521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014239207290744118855361 4510679405468058089141521)
              ·
                refine ⟨3383009554101043566856141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510679405468058089141521 3383009554101043566856141)
                ·
                  refine ⟨1268628582787891337571053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3383009554101043566856141 1268628582787891337571053)
                  ·
                    refine ⟨475735718545459251589145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268628582787891337571053 475735718545459251589145)
                    ·
                      rfl

theorem cell22_1389738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1389738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389738 prefixEnd_1389738 := by exact prefixLift 1389738
  have htrace : WordTrace (prefixWord ++ tailWord_1389738) baseStart_1389738 baseEnd_1389738 := by
    simpa [prefixWord, tailWord_1389738, baseEnd_1389738] using wordTrace_append hprefix tailTrace_1389738
  have hstable : (prefixWord ++ tailWord_1389738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389738).length < 2 ^ (prefixWord ++ tailWord_1389738).sum := by decide
  have hdescent : baseEnd_1389738 < baseStart_1389738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389828 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_1389828 : Nat := 118140960795 + 1389828 * 2 ^ 59
def prefixEnd_1389828 : Nat := 4983230072969 + 3 ^ 40 * 1389828 * 2
def baseEnd_1389828 : Nat := 475766527384729016838869

theorem tailTrace_1389828 : CollatzResearch.WordTrace tailWord_1389828 prefixEnd_1389828 475766527384729016838869 := by
  unfold tailWord_1389828
  simp only [CollatzResearch.WordTrace]
  refine ⟨25345595804448997285009069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33794127739265329713345425 25345595804448997285009069)
  ·
    refine ⟨9504598426668373981878401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25345595804448997285009069 9504598426668373981878401)
    ·
      refine ⟨7128448820001280486408801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9504598426668373981878401 7128448820001280486408801)
      ·
        refine ⟨5346336615000960364806601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7128448820001280486408801 5346336615000960364806601)
        ·
          refine ⟨4009752461250720273604951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5346336615000960364806601 4009752461250720273604951)
          ·
            refine ⟨6014628691876080410407427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009752461250720273604951 6014628691876080410407427)
            ·
              refine ⟨9021943037814120615611141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6014628691876080410407427 9021943037814120615611141)
              ·
                refine ⟨1691614319590147615427089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9021943037814120615611141 1691614319590147615427089)
                ·
                  refine ⟨1268710739692610711570317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1691614319590147615427089 1268710739692610711570317)
                  ·
                    refine ⟨475766527384729016838869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268710739692610711570317 475766527384729016838869)
                    ·
                      rfl

theorem cell22_1389828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_1389828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389828 prefixEnd_1389828 := by exact prefixLift 1389828
  have htrace : WordTrace (prefixWord ++ tailWord_1389828) baseStart_1389828 baseEnd_1389828 := by
    simpa [prefixWord, tailWord_1389828, baseEnd_1389828] using wordTrace_append hprefix tailTrace_1389828
  have hstable : (prefixWord ++ tailWord_1389828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389828).length < 2 ^ (prefixWord ++ tailWord_1389828).sum := by decide
  have hdescent : baseEnd_1389828 < baseStart_1389828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389858 : List Nat := [3, 3, 1, 1, 4, 1, 3, 6]
def baseStart_1389858 : Nat := 118140960795 + 1389858 * 2 ^ 59
def prefixEnd_1389858 : Nat := 4983230072969 + 3 ^ 40 * 1389858 * 2
def baseEnd_1389858 : Nat := 52864088555313215398753

theorem tailTrace_1389858 : CollatzResearch.WordTrace tailWord_1389858 prefixEnd_1389858 52864088555313215398753 := by
  unfold tailWord_1389858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12673071449697327423402557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33794857199192873129073485 12673071449697327423402557)
  ·
    refine ⟨4752401793636497783775959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12673071449697327423402557 4752401793636497783775959)
    ·
      refine ⟨7128602690454746675663939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4752401793636497783775959 7128602690454746675663939)
      ·
        refine ⟨10692904035682120013495909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7128602690454746675663939 10692904035682120013495909)
        ·
          refine ⟨2004919506690397502530483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10692904035682120013495909 2004919506690397502530483)
          ·
            refine ⟨3007379260035596253795725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004919506690397502530483 3007379260035596253795725)
            ·
              refine ⟨1127767222513348595173397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3007379260035596253795725 1127767222513348595173397)
              ·
                refine ⟨52864088555313215398753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1127767222513348595173397 52864088555313215398753)
                ·
                  rfl

theorem cell22_1389858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_1389858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389858 prefixEnd_1389858 := by exact prefixLift 1389858
  have htrace : WordTrace (prefixWord ++ tailWord_1389858) baseStart_1389858 baseEnd_1389858 := by
    simpa [prefixWord, tailWord_1389858, baseEnd_1389858] using wordTrace_append hprefix tailTrace_1389858
  have hstable : (prefixWord ++ tailWord_1389858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389858).length < 2 ^ (prefixWord ++ tailWord_1389858).sum := by decide
  have hdescent : baseEnd_1389858 < baseStart_1389858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389886 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1389886 : Nat := 118140960795 + 1389886 * 2 ^ 59
def prefixEnd_1389886 : Nat := 4983230072969 + 3 ^ 40 * 1389886 * 2
def baseEnd_1389886 : Nat := 158595460656678732962897

theorem tailTrace_1389886 : CollatzResearch.WordTrace tailWord_1389886 prefixEnd_1389886 158595460656678732962897 := by
  unfold tailWord_1389886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336663380335983809453689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33795538028458580317086341 6336663380335983809453689)
  ·
    refine ⟨4752497535251987857090267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6336663380335983809453689 4752497535251987857090267)
    ·
      refine ⟨7128746302877981785635401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4752497535251987857090267 7128746302877981785635401)
      ·
        refine ⟨5346559727158486339226551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7128746302877981785635401 5346559727158486339226551)
        ·
          refine ⟨8019839590737729508839827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346559727158486339226551 8019839590737729508839827)
          ·
            refine ⟨12029759386106594263259741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019839590737729508839827 12029759386106594263259741)
            ·
              refine ⟨4511159769789972848722403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12029759386106594263259741 4511159769789972848722403)
              ·
                refine ⟨6766739654684959273083605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511159769789972848722403 6766739654684959273083605)
                ·
                  refine ⟨158595460656678732962897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6766739654684959273083605 158595460656678732962897)
                  ·
                    rfl

theorem cell22_1389886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1389886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389886 prefixEnd_1389886 := by exact prefixLift 1389886
  have htrace : WordTrace (prefixWord ++ tailWord_1389886) baseStart_1389886 baseEnd_1389886 := by
    simpa [prefixWord, tailWord_1389886, baseEnd_1389886] using wordTrace_append hprefix tailTrace_1389886
  have hstable : (prefixWord ++ tailWord_1389886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389886).length < 2 ^ (prefixWord ++ tailWord_1389886).sum := by decide
  have hdescent : baseEnd_1389886 < baseStart_1389886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389933 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1389933 : Nat := 118140960795 + 1389933 * 2 ^ 59
def prefixEnd_1389933 : Nat := 4983230072969 + 3 ^ 40 * 1389933 * 2
def baseEnd_1389933 : Nat := 475802471030543742963547

theorem tailTrace_1389933 : CollatzResearch.WordTrace tailWord_1389933 prefixEnd_1389933 475802471030543742963547 := by
  unfold tailWord_1389933
  simp only [CollatzResearch.WordTrace]
  refine ⟨50695021273517597502590453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33796680849011731668393635 50695021273517597502590453)
  ·
    refine ⟨4752658244392274765867855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50695021273517597502590453 4752658244392274765867855)
    ·
      refine ⟨7128987366588412148801783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4752658244392274765867855 7128987366588412148801783)
      ·
        refine ⟨10693481049882618223202675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7128987366588412148801783 10693481049882618223202675)
        ·
          refine ⟨16040221574823927334804013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10693481049882618223202675 16040221574823927334804013)
          ·
            refine ⟨6015083090558972750551505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16040221574823927334804013 6015083090558972750551505)
            ·
              refine ⟨4511312317919229562913629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6015083090558972750551505 4511312317919229562913629)
              ·
                refine ⟨1691742119219711086092611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4511312317919229562913629 1691742119219711086092611)
                ·
                  refine ⟨2537613178829566629138917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691742119219711086092611 2537613178829566629138917)
                  ·
                    refine ⟨475802471030543742963547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537613178829566629138917 475802471030543742963547)
                    ·
                      rfl

theorem cell22_1389933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1389933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389933 prefixEnd_1389933 := by exact prefixLift 1389933
  have htrace : WordTrace (prefixWord ++ tailWord_1389933) baseStart_1389933 baseEnd_1389933 := by
    simpa [prefixWord, tailWord_1389933, baseEnd_1389933] using wordTrace_append hprefix tailTrace_1389933
  have hstable : (prefixWord ++ tailWord_1389933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389933).length < 2 ^ (prefixWord ++ tailWord_1389933).sum := by decide
  have hdescent : baseEnd_1389933 < baseStart_1389933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389944 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1389944 : Nat := 118140960795 + 1389944 * 2 ^ 59
def prefixEnd_1389944 : Nat := 4983230072969 + 3 ^ 40 * 1389944 * 2
def baseEnd_1389944 : Nat := 475806236555343380938513

theorem tailTrace_1389944 : CollatzResearch.WordTrace tailWord_1389944 prefixEnd_1389944 475806236555343380938513 := by
  unfold tailWord_1389944
  simp only [CollatzResearch.WordTrace]
  refine ⟨25347711238238873190620443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33796948317651830920827257 25347711238238873190620443)
  ·
    refine ⟨38021566857358309785930665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25347711238238873190620443 38021566857358309785930665)
    ·
      refine ⟨28516175143018732339447999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38021566857358309785930665 28516175143018732339447999)
      ·
        refine ⟨42774262714528098509171999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28516175143018732339447999 42774262714528098509171999)
        ·
          refine ⟨64161394071792147763757999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42774262714528098509171999 64161394071792147763757999)
          ·
            refine ⟨96242091107688221645636999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64161394071792147763757999 96242091107688221645636999)
            ·
              refine ⟨144363136661532332468455499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96242091107688221645636999 144363136661532332468455499)
              ·
                refine ⟨216544704992298498702683249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144363136661532332468455499 216544704992298498702683249)
                ·
                  refine ⟨162408528744223874027012437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216544704992298498702683249 162408528744223874027012437)
                  ·
                    refine ⟨475806236555343380938513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 162408528744223874027012437 475806236555343380938513)
                    ·
                      rfl

theorem cell22_1389944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1389944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389944 prefixEnd_1389944 := by exact prefixLift 1389944
  have htrace : WordTrace (prefixWord ++ tailWord_1389944) baseStart_1389944 baseEnd_1389944 := by
    simpa [prefixWord, tailWord_1389944, baseEnd_1389944] using wordTrace_append hprefix tailTrace_1389944
  have hstable : (prefixWord ++ tailWord_1389944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389944).length < 2 ^ (prefixWord ++ tailWord_1389944).sum := by decide
  have hdescent : baseEnd_1389944 < baseStart_1389944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389963 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 2, 3]
def baseStart_1389963 : Nat := 118140960795 + 1389963 * 2 ^ 59
def prefixEnd_1389963 : Nat := 4983230072969 + 3 ^ 40 * 1389963 * 2
def baseEnd_1389963 : Nat := 475812740643633664713455

theorem tailTrace_1389963 : CollatzResearch.WordTrace tailWord_1389963 prefixEnd_1389963 475812740643633664713455 := by
  unfold tailWord_1389963
  simp only [CollatzResearch.WordTrace]
  refine ⟨50696115463408912626182543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33797410308939275084121695 50696115463408912626182543)
  ·
    refine ⟨76044173195113368939273815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50696115463408912626182543 76044173195113368939273815)
    ·
      refine ⟨114066259792670053408910723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76044173195113368939273815 114066259792670053408910723)
      ·
        refine ⟨171099389689005080113366085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114066259792670053408910723 171099389689005080113366085)
        ·
          refine ⟨32081135566688452521256141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171099389689005080113366085 32081135566688452521256141)
          ·
            refine ⟨12030425837508169695471053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32081135566688452521256141 12030425837508169695471053)
            ·
              refine ⟨4511409689065563635801645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12030425837508169695471053 4511409689065563635801645)
              ·
                refine ⟨1691778633399586363425617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4511409689065563635801645 1691778633399586363425617)
                ·
                  refine ⟨1268833975049689772569213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1691778633399586363425617 1268833975049689772569213)
                  ·
                    refine ⟨475812740643633664713455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268833975049689772569213 475812740643633664713455)
                    ·
                      rfl

theorem cell22_1389963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 3].length) (baseStart_1389963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389963 prefixEnd_1389963 := by exact prefixLift 1389963
  have htrace : WordTrace (prefixWord ++ tailWord_1389963) baseStart_1389963 baseEnd_1389963 := by
    simpa [prefixWord, tailWord_1389963, baseEnd_1389963] using wordTrace_append hprefix tailTrace_1389963
  have hstable : (prefixWord ++ tailWord_1389963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389963).length < 2 ^ (prefixWord ++ tailWord_1389963).sum := by decide
  have hdescent : baseEnd_1389963 < baseStart_1389963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389978 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_1389978 : Nat := 118140960795 + 1389978 * 2 ^ 59
def prefixEnd_1389978 : Nat := 4983230072969 + 3 ^ 40 * 1389978 * 2
def baseEnd_1389978 : Nat := 475817875450178625588409

theorem tailTrace_1389978 : CollatzResearch.WordTrace tailWord_1389978 prefixEnd_1389978 475817875450178625588409 := by
  unfold tailWord_1389978
  simp only [CollatzResearch.WordTrace]
  refine ⟨12674165639588642546994647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33797775038903046791985725 12674165639588642546994647)
  ·
    refine ⟨19011248459382963820491971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12674165639588642546994647 19011248459382963820491971)
    ·
      refine ⟨28516872689074445730737957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19011248459382963820491971 28516872689074445730737957)
      ·
        refine ⟨5346913629201458574513367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28516872689074445730737957 5346913629201458574513367)
        ·
          refine ⟨8020370443802187861770051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346913629201458574513367 8020370443802187861770051)
          ·
            refine ⟨12030555665703281792655077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020370443802187861770051 12030555665703281792655077)
            ·
              refine ⟨2255729187319365336122827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12030555665703281792655077 2255729187319365336122827)
              ·
                refine ⟨3383593780979048004184241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255729187319365336122827 3383593780979048004184241)
                ·
                  refine ⟨2537695335734286003138181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383593780979048004184241 2537695335734286003138181)
                  ·
                    refine ⟨475817875450178625588409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537695335734286003138181 475817875450178625588409)
                    ·
                      rfl

theorem cell22_1389978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_1389978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389978 prefixEnd_1389978 := by exact prefixLift 1389978
  have htrace : WordTrace (prefixWord ++ tailWord_1389978) baseStart_1389978 baseEnd_1389978 := by
    simpa [prefixWord, tailWord_1389978, baseEnd_1389978] using wordTrace_append hprefix tailTrace_1389978
  have hstable : (prefixWord ++ tailWord_1389978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389978).length < 2 ^ (prefixWord ++ tailWord_1389978).sum := by decide
  have hdescent : baseEnd_1389978 < baseStart_1389978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389980 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1389980 : Nat := 118140960795 + 1389980 * 2 ^ 59
def prefixEnd_1389980 : Nat := 4983230072969 + 3 ^ 40 * 1389980 * 2
def baseEnd_1389980 : Nat := 475818560091051287038403

theorem tailTrace_1389980 : CollatzResearch.WordTrace tailWord_1389980 prefixEnd_1389980 475818560091051287038403 := by
  unfold tailWord_1389980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25348367752173662264775697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33797823669564883019700929 25348367752173662264775697)
  ·
    refine ⟨19011275814130246698581773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25348367752173662264775697 19011275814130246698581773)
    ·
      refine ⟨7129228430298842511968165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19011275814130246698581773 7129228430298842511968165)
      ·
        refine ⟨1336730330681032970994031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7129228430298842511968165 1336730330681032970994031)
        ·
          refine ⟨2005095496021549456491047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336730330681032970994031 2005095496021549456491047)
          ·
            refine ⟨3007643244032324184736571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005095496021549456491047 3007643244032324184736571)
            ·
              refine ⟨4511464866048486277104857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007643244032324184736571 4511464866048486277104857)
              ·
                refine ⟨3383598649536364707828643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511464866048486277104857 3383598649536364707828643)
                ·
                  refine ⟨5075397974304547061742965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383598649536364707828643 5075397974304547061742965)
                  ·
                    refine ⟨475818560091051287038403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5075397974304547061742965 475818560091051287038403)
                    ·
                      rfl

theorem cell22_1389980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1389980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389980 prefixEnd_1389980 := by exact prefixLift 1389980
  have htrace : WordTrace (prefixWord ++ tailWord_1389980) baseStart_1389980 baseEnd_1389980 := by
    simpa [prefixWord, tailWord_1389980, baseEnd_1389980] using wordTrace_append hprefix tailTrace_1389980
  have hstable : (prefixWord ++ tailWord_1389980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389980).length < 2 ^ (prefixWord ++ tailWord_1389980).sum := by decide
  have hdescent : baseEnd_1389980 < baseStart_1389980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389997 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1389997 : Nat := 118140960795 + 1389997 * 2 ^ 59
def prefixEnd_1389997 : Nat := 4983230072969 + 3 ^ 40 * 1389997 * 2
def baseEnd_1389997 : Nat := 475824379538468909363351

theorem tailTrace_1389997 : CollatzResearch.WordTrace tailWord_1389997 prefixEnd_1389997 475824379538468909363351 := by
  unfold tailWord_1389997
  simp only [CollatzResearch.WordTrace]
  refine ⟨50697355545285736432920245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33798237030190490955280163 50697355545285736432920245)
  ·
    refine ⟨4752877082370537790586273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50697355545285736432920245 4752877082370537790586273)
    ·
      refine ⟨3564657811777903342939705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4752877082370537790586273 3564657811777903342939705)
      ·
        refine ⟨2673493358833427507204779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3564657811777903342939705 2673493358833427507204779)
        ·
          refine ⟨4010240038250141260807169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673493358833427507204779 4010240038250141260807169)
          ·
            refine ⟨3007680028687605945605377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4010240038250141260807169 3007680028687605945605377)
            ·
              refine ⟨2255760021515704459204033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007680028687605945605377 2255760021515704459204033)
              ·
                refine ⟨1691820016136778344403025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255760021515704459204033 1691820016136778344403025)
                ·
                  refine ⟨1268865012102583758302269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1691820016136778344403025 1268865012102583758302269)
                  ·
                    refine ⟨475824379538468909363351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268865012102583758302269 475824379538468909363351)
                    ·
                      rfl

theorem cell22_1389997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1389997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1389997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1389997 prefixEnd_1389997 := by exact prefixLift 1389997
  have htrace : WordTrace (prefixWord ++ tailWord_1389997) baseStart_1389997 baseEnd_1389997 := by
    simpa [prefixWord, tailWord_1389997, baseEnd_1389997] using wordTrace_append hprefix tailTrace_1389997
  have hstable : (prefixWord ++ tailWord_1389997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389997).length < 2 ^ (prefixWord ++ tailWord_1389997).sum := by decide
  have hdescent : baseEnd_1389997 < baseStart_1389997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390042 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_1390042 : Nat := 118140960795 + 1390042 * 2 ^ 59
def prefixEnd_1390042 : Nat := 4983230072969 + 3 ^ 40 * 1390042 * 2
def baseEnd_1390042 : Nat := 475839783958103791988213

theorem tailTrace_1390042 : CollatzResearch.WordTrace tailWord_1390042 prefixEnd_1390042 475839783958103791988213 := by
  unfold tailWord_1390042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12674749207530677279577095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33799331220081806078872253 12674749207530677279577095)
  ·
    refine ⟨19012123811296015919365643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12674749207530677279577095 19012123811296015919365643)
    ·
      refine ⟨28518185716944023879048465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19012123811296015919365643 28518185716944023879048465)
      ·
        refine ⟨21388639287708017909286349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28518185716944023879048465 21388639287708017909286349)
        ·
          refine ⟨8020739732890506715982381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21388639287708017909286349 8020739732890506715982381)
          ·
            refine ⟨3007777399833940018493393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8020739732890506715982381 3007777399833940018493393)
            ·
              refine ⟨2255833049875455013870045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007777399833940018493393 2255833049875455013870045)
              ·
                refine ⟨845937393703295630201267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2255833049875455013870045 845937393703295630201267)
                ·
                  refine ⟨1268906090554943445301901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845937393703295630201267 1268906090554943445301901)
                  ·
                    refine ⟨475839783958103791988213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268906090554943445301901 475839783958103791988213)
                    ·
                      rfl

theorem cell22_1390042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_1390042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390042 prefixEnd_1390042 := by exact prefixLift 1390042
  have htrace : WordTrace (prefixWord ++ tailWord_1390042) baseStart_1390042 baseEnd_1390042 := by
    simpa [prefixWord, tailWord_1390042, baseEnd_1390042] using wordTrace_append hprefix tailTrace_1390042
  have hstable : (prefixWord ++ tailWord_1390042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390042).length < 2 ^ (prefixWord ++ tailWord_1390042).sum := by decide
  have hdescent : baseEnd_1390042 < baseStart_1390042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390053 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_1390053 : Nat := 118140960795 + 1390053 * 2 ^ 59
def prefixEnd_1390053 : Nat := 4983230072969 + 3 ^ 40 * 1390053 * 2
def baseEnd_1390053 : Nat := 475843549482903429963179

theorem tailTrace_1390053 : CollatzResearch.WordTrace tailWord_1390053 prefixEnd_1390053 475843549482903429963179 := by
  unfold tailWord_1390053
  simp only [CollatzResearch.WordTrace]
  refine ⟨50699398033082857996958813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33799598688721905331305875 50699398033082857996958813)
  ·
    refine ⟨19012274262406071748859555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50699398033082857996958813 19012274262406071748859555)
    ·
      refine ⟨28518411393609107623289333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19012274262406071748859555 28518411393609107623289333)
      ·
        refine ⟨2673601068150853839683375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28518411393609107623289333 2673601068150853839683375)
        ·
          refine ⟨4010401602226280759525063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673601068150853839683375 4010401602226280759525063)
          ·
            refine ⟨6015602403339421139287595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010401602226280759525063 6015602403339421139287595)
            ·
              refine ⟨9023403605009131708931393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015602403339421139287595 9023403605009131708931393)
              ·
                refine ⟨6767552703756848781698545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9023403605009131708931393 6767552703756848781698545)
                ·
                  refine ⟨5075664527817636586273909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6767552703756848781698545 5075664527817636586273909)
                  ·
                    refine ⟨475843549482903429963179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5075664527817636586273909 475843549482903429963179)
                    ·
                      rfl

theorem cell22_1390053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_1390053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390053 prefixEnd_1390053 := by exact prefixLift 1390053
  have htrace : WordTrace (prefixWord ++ tailWord_1390053) baseStart_1390053 baseEnd_1390053 := by
    simpa [prefixWord, tailWord_1390053, baseEnd_1390053] using wordTrace_append hprefix tailTrace_1390053
  have hstable : (prefixWord ++ tailWord_1390053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390053).length < 2 ^ (prefixWord ++ tailWord_1390053).sum := by decide
  have hdescent : baseEnd_1390053 < baseStart_1390053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390055 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 5]
def baseStart_1390055 : Nat := 118140960795 + 1390055 * 2 ^ 59
def prefixEnd_1390055 : Nat := 4983230072969 + 3 ^ 40 * 1390055 * 2
def baseEnd_1390055 : Nat := 158614744707925363804391

theorem tailTrace_1390055 : CollatzResearch.WordTrace tailWord_1390055 prefixEnd_1390055 158614744707925363804391 := by
  unfold tailWord_1390055
  simp only [CollatzResearch.WordTrace]
  refine ⟨50699470979075612338531619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33799647319383741559021079 50699470979075612338531619)
  ·
    refine ⟨76049206468613418507797429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50699470979075612338531619 76049206468613418507797429)
    ·
      refine ⟨7129613106432507985106009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76049206468613418507797429 7129613106432507985106009)
      ·
        refine ⟨5347209829824380988829507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7129613106432507985106009 5347209829824380988829507)
        ·
          refine ⟨8020814744736571483244261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347209829824380988829507 8020814744736571483244261)
          ·
            refine ⟨1503902764638107153108299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8020814744736571483244261 1503902764638107153108299)
            ·
              refine ⟨2255854146957160729662449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503902764638107153108299 2255854146957160729662449)
              ·
                refine ⟨1691890610217870547246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255854146957160729662449 1691890610217870547246837)
                ·
                  refine ⟨158614744707925363804391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691890610217870547246837 158614744707925363804391)
                  ·
                    rfl

theorem cell22_1390055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 5].length) (baseStart_1390055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390055 prefixEnd_1390055 := by exact prefixLift 1390055
  have htrace : WordTrace (prefixWord ++ tailWord_1390055) baseStart_1390055 baseEnd_1390055 := by
    simpa [prefixWord, tailWord_1390055, baseEnd_1390055] using wordTrace_append hprefix tailTrace_1390055
  have hstable : (prefixWord ++ tailWord_1390055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390055).length < 2 ^ (prefixWord ++ tailWord_1390055).sum := by decide
  have hdescent : baseEnd_1390055 < baseStart_1390055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390093 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1390093 : Nat := 118140960795 + 1390093 * 2 ^ 59
def prefixEnd_1390093 : Nat := 4983230072969 + 3 ^ 40 * 1390093 * 2
def baseEnd_1390093 : Nat := 475857242300356658963057

theorem tailTrace_1390093 : CollatzResearch.WordTrace tailWord_1390093 prefixEnd_1390093 475857242300356658963057 := by
  unfold tailWord_1390093
  simp only [CollatzResearch.WordTrace]
  refine ⟨50700856952937944828414933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33800571301958629885609955 50700856952937944828414933)
  ·
    refine ⟨1188301334834483081915975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50700856952937944828414933 1188301334834483081915975)
    ·
      refine ⟨1782452002251724622873963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188301334834483081915975 1782452002251724622873963)
      ·
        refine ⟨2673678003377586934310945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782452002251724622873963 2673678003377586934310945)
        ·
          refine ⟨2005258502533190200733209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673678003377586934310945 2005258502533190200733209)
          ·
            refine ⟨1503943876899892650549907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005258502533190200733209 1503943876899892650549907)
            ·
              refine ⟨2255915815349838975824861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503943876899892650549907 2255915815349838975824861)
              ·
                refine ⟨845968430756189615934323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2255915815349838975824861 845968430756189615934323)
                ·
                  refine ⟨1268952646134284423901485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845968430756189615934323 1268952646134284423901485)
                  ·
                    refine ⟨475857242300356658963057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268952646134284423901485 475857242300356658963057)
                    ·
                      rfl

theorem cell22_1390093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1390093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390093 prefixEnd_1390093 := by exact prefixLift 1390093
  have htrace : WordTrace (prefixWord ++ tailWord_1390093) baseStart_1390093 baseEnd_1390093 := by
    simpa [prefixWord, tailWord_1390093, baseEnd_1390093] using wordTrace_append hprefix tailTrace_1390093
  have hstable : (prefixWord ++ tailWord_1390093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390093).length < 2 ^ (prefixWord ++ tailWord_1390093).sum := by decide
  have hdescent : baseEnd_1390093 < baseStart_1390093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390110 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1390110 : Nat := 118140960795 + 1390110 * 2 ^ 59
def prefixEnd_1390110 : Nat := 4983230072969 + 3 ^ 40 * 1390110 * 2
def baseEnd_1390110 : Nat := 475863061747774281288005

theorem tailTrace_1390110 : CollatzResearch.WordTrace tailWord_1390110 prefixEnd_1390110 475863061747774281288005 := by
  unfold tailWord_1390110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337684624234544591472973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33800984662584237821189189 6337684624234544591472973)
  ·
    refine ⟨2376631734087954221802365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6337684624234544591472973 2376631734087954221802365)
    ·
      refine ⟨891236900282982833175887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2376631734087954221802365 891236900282982833175887)
      ·
        refine ⟨1336855350424474249763831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891236900282982833175887 1336855350424474249763831)
        ·
          refine ⟨2005283025636711374645747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336855350424474249763831 2005283025636711374645747)
          ·
            refine ⟨3007924538455067061968621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005283025636711374645747 3007924538455067061968621)
            ·
              refine ⟨1127971701920650148238233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3007924538455067061968621 1127971701920650148238233)
              ·
                refine ⟨845978776440487611178675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127971701920650148238233 845978776440487611178675)
                ·
                  refine ⟨1268968164660731416768013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845978776440487611178675 1268968164660731416768013)
                  ·
                    refine ⟨475863061747774281288005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268968164660731416768013 475863061747774281288005)
                    ·
                      rfl

theorem cell22_1390110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1390110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390110 prefixEnd_1390110 := by exact prefixLift 1390110
  have htrace : WordTrace (prefixWord ++ tailWord_1390110) baseStart_1390110 baseEnd_1390110 := by
    simpa [prefixWord, tailWord_1390110, baseEnd_1390110] using wordTrace_append hprefix tailTrace_1390110
  have hstable : (prefixWord ++ tailWord_1390110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390110).length < 2 ^ (prefixWord ++ tailWord_1390110).sum := by decide
  have hdescent : baseEnd_1390110 < baseStart_1390110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390111 : List Nat := [1, 1, 2, 4, 1, 1, 12]
def baseStart_1390111 : Nat := 118140960795 + 1390111 * 2 ^ 59
def prefixEnd_1390111 : Nat := 4983230072969 + 3 ^ 40 * 1390111 * 2
def baseEnd_1390111 : Nat := 17624570521044837481963

theorem tailTrace_1390111 : CollatzResearch.WordTrace tailWord_1390111 prefixEnd_1390111 17624570521044837481963 := by
  unfold tailWord_1390111
  simp only [CollatzResearch.WordTrace]
  refine ⟨50701513466872733902570187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33801008977915155935046791 50701513466872733902570187)
  ·
    refine ⟨76052270200309100853855281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50701513466872733902570187 76052270200309100853855281)
    ·
      refine ⟨57039202650231825640391461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76052270200309100853855281 57039202650231825640391461)
      ·
        refine ⟨10694850496918467307573399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57039202650231825640391461 10694850496918467307573399)
        ·
          refine ⟨16042275745377700961360099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10694850496918467307573399 16042275745377700961360099)
          ·
            refine ⟨24063413618066551442040149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16042275745377700961360099 24063413618066551442040149)
            ·
              refine ⟨17624570521044837481963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24063413618066551442040149 17624570521044837481963)
              ·
                rfl

theorem cell22_1390111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 12].length) (baseStart_1390111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390111 prefixEnd_1390111 := by exact prefixLift 1390111
  have htrace : WordTrace (prefixWord ++ tailWord_1390111) baseStart_1390111 baseEnd_1390111 := by
    simpa [prefixWord, tailWord_1390111, baseEnd_1390111] using wordTrace_append hprefix tailTrace_1390111
  have hstable : (prefixWord ++ tailWord_1390111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390111).length < 2 ^ (prefixWord ++ tailWord_1390111).sum := by decide
  have hdescent : baseEnd_1390111 < baseStart_1390111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390113 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1390113 : Nat := 118140960795 + 1390113 * 2 ^ 59
def prefixEnd_1390113 : Nat := 4983230072969 + 3 ^ 40 * 1390113 * 2
def baseEnd_1390113 : Nat := 475864088709083273462995

theorem tailTrace_1390113 : CollatzResearch.WordTrace tailWord_1390113 prefixEnd_1390113 475864088709083273462995 := by
  unfold tailWord_1390113
  simp only [CollatzResearch.WordTrace]
  refine ⟨50701586412865488244142993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33801057608576992162761995 50701586412865488244142993)
  ·
    refine ⟨38026189809649116183107245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50701586412865488244142993 38026189809649116183107245)
    ·
      refine ⟨14259821178618418568665217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38026189809649116183107245 14259821178618418568665217)
      ·
        refine ⟨10694865883963813926498913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14259821178618418568665217 10694865883963813926498913)
        ·
          refine ⟨8021149412972860444874185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694865883963813926498913 8021149412972860444874185)
          ·
            refine ⟨6015862059729645333655639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8021149412972860444874185 6015862059729645333655639)
            ·
              refine ⟨9023793089594468000483459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015862059729645333655639 9023793089594468000483459)
              ·
                refine ⟨13535689634391702000725189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9023793089594468000483459 13535689634391702000725189)
                ·
                  refine ⟨2537941806448444125135973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13535689634391702000725189 2537941806448444125135973)
                  ·
                    refine ⟨475864088709083273462995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537941806448444125135973 475864088709083273462995)
                    ·
                      rfl

theorem cell22_1390113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1390113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390113 prefixEnd_1390113 := by exact prefixLift 1390113
  have htrace : WordTrace (prefixWord ++ tailWord_1390113) baseStart_1390113 baseEnd_1390113 := by
    simpa [prefixWord, tailWord_1390113, baseEnd_1390113] using wordTrace_append hprefix tailTrace_1390113
  have hstable : (prefixWord ++ tailWord_1390113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390113).length < 2 ^ (prefixWord ++ tailWord_1390113).sum := by decide
  have hdescent : baseEnd_1390113 < baseStart_1390113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390177 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 1, 3]
def baseStart_1390177 : Nat := 118140960795 + 1390177 * 2 ^ 59
def prefixEnd_1390177 : Nat := 4983230072969 + 3 ^ 40 * 1390177 * 2
def baseEnd_1390177 : Nat := 475885997217008439862799

theorem tailTrace_1390177 : CollatzResearch.WordTrace tailWord_1390177 prefixEnd_1390177 475885997217008439862799 := by
  unfold tailWord_1390177
  simp only [CollatzResearch.WordTrace]
  refine ⟨50703920684633627174472785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33802613789755751449648523 50703920684633627174472785)
  ·
    refine ⟨38027940513475220380854589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50703920684633627174472785 38027940513475220380854589)
    ·
      refine ⟨14260477692553207642820471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38027940513475220380854589 14260477692553207642820471)
      ·
        refine ⟨21390716538829811464230707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14260477692553207642820471 21390716538829811464230707)
        ·
          refine ⟨32086074808244717196346061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21390716538829811464230707 32086074808244717196346061)
          ·
            refine ⟨12032278053091768948629773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32086074808244717196346061 12032278053091768948629773)
            ·
              refine ⟨4512104269909413355736165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12032278053091768948629773 4512104269909413355736165)
              ·
                refine ⟨846019550608015004200531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4512104269909413355736165 846019550608015004200531)
                ·
                  refine ⟨1269029325912022506300797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846019550608015004200531 1269029325912022506300797)
                  ·
                    refine ⟨475885997217008439862799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269029325912022506300797 475885997217008439862799)
                    ·
                      rfl

theorem cell22_1390177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_1390177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390177 prefixEnd_1390177 := by exact prefixLift 1390177
  have htrace : WordTrace (prefixWord ++ tailWord_1390177) baseStart_1390177 baseEnd_1390177 := by
    simpa [prefixWord, tailWord_1390177, baseEnd_1390177] using wordTrace_append hprefix tailTrace_1390177
  have hstable : (prefixWord ++ tailWord_1390177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390177).length < 2 ^ (prefixWord ++ tailWord_1390177).sum := by decide
  have hdescent : baseEnd_1390177 < baseStart_1390177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390203 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 3, 4]
def baseStart_1390203 : Nat := 118140960795 + 1390203 * 2 ^ 59
def prefixEnd_1390203 : Nat := 4983230072969 + 3 ^ 40 * 1390203 * 2
def baseEnd_1390203 : Nat := 475894897548353038712719

theorem tailTrace_1390203 : CollatzResearch.WordTrace tailWord_1390203 prefixEnd_1390203 475894897548353038712719 := by
  unfold tailWord_1390203
  simp only [CollatzResearch.WordTrace]
  refine ⟨50704868982539433614919263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33803245988359622409946175 50704868982539433614919263)
  ·
    refine ⟨76057303473809150422378895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50704868982539433614919263 76057303473809150422378895)
    ·
      refine ⟨114085955210713725633568343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76057303473809150422378895 114085955210713725633568343)
      ·
        refine ⟨171128932816070588450352515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114085955210713725633568343 171128932816070588450352515)
        ·
          refine ⟨256693399224105882675528773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171128932816070588450352515 256693399224105882675528773)
          ·
            refine ⟨48130012354519853001661645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256693399224105882675528773 48130012354519853001661645)
            ·
              refine ⟨18048754632944944875623117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48130012354519853001661645 18048754632944944875623117)
              ·
                refine ⟨6768282987354354328358669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18048754632944944875623117 6768282987354354328358669)
                ·
                  refine ⟨2538106120257882873134501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6768282987354354328358669 2538106120257882873134501)
                  ·
                    refine ⟨475894897548353038712719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538106120257882873134501 475894897548353038712719)
                    ·
                      rfl

theorem cell22_1390203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_1390203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390203 prefixEnd_1390203 := by exact prefixLift 1390203
  have htrace : WordTrace (prefixWord ++ tailWord_1390203) baseStart_1390203 baseEnd_1390203 := by
    simpa [prefixWord, tailWord_1390203, baseEnd_1390203] using wordTrace_append hprefix tailTrace_1390203
  have hstable : (prefixWord ++ tailWord_1390203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390203).length < 2 ^ (prefixWord ++ tailWord_1390203).sum := by decide
  have hdescent : baseEnd_1390203 < baseStart_1390203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390220 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_1390220 : Nat := 118140960795 + 1390220 * 2 ^ 59
def prefixEnd_1390220 : Nat := 4983230072969 + 3 ^ 40 * 1390220 * 2
def baseEnd_1390220 : Nat := 475900716995770661037667

theorem tailTrace_1390220 : CollatzResearch.WordTrace tailWord_1390220 prefixEnd_1390220 475900716995770661037667 := by
  unfold tailWord_1390220
  simp only [CollatzResearch.WordTrace]
  refine ⟨25352744511738922759144057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33803659348985230345525409 25352744511738922759144057)
  ·
    refine ⟨19014558383804192069358043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25352744511738922759144057 19014558383804192069358043)
    ·
      refine ⟨28521837575706288104037065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19014558383804192069358043 28521837575706288104037065)
      ·
        refine ⟨21391378181779716078027799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28521837575706288104037065 21391378181779716078027799)
        ·
          refine ⟨32087067272669574117041699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21391378181779716078027799 32087067272669574117041699)
          ·
            refine ⟨48130600909004361175562549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32087067272669574117041699 48130600909004361175562549)
            ·
              refine ⟨4512243835219158860208989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48130600909004361175562549 4512243835219158860208989)
              ·
                refine ⟨1692091438207184572578371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4512243835219158860208989 1692091438207184572578371)
                ·
                  refine ⟨2538137157310776858867557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692091438207184572578371 2538137157310776858867557)
                  ·
                    refine ⟨475900716995770661037667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538137157310776858867557 475900716995770661037667)
                    ·
                      rfl

theorem cell22_1390220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_1390220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390220 prefixEnd_1390220 := by exact prefixLift 1390220
  have htrace : WordTrace (prefixWord ++ tailWord_1390220) baseStart_1390220 baseEnd_1390220 := by
    simpa [prefixWord, tailWord_1390220, baseEnd_1390220] using wordTrace_append hprefix tailTrace_1390220
  have hstable : (prefixWord ++ tailWord_1390220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390220).length < 2 ^ (prefixWord ++ tailWord_1390220).sum := by decide
  have hdescent : baseEnd_1390220 < baseStart_1390220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390282 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1390282 : Nat := 118140960795 + 1390282 * 2 ^ 59
def prefixEnd_1390282 : Nat := 4983230072969 + 3 ^ 40 * 1390282 * 2
def baseEnd_1390282 : Nat := 475921940862823165987477

theorem tailTrace_1390282 : CollatzResearch.WordTrace tailWord_1390282 prefixEnd_1390282 475921940862823165987477 := by
  unfold tailWord_1390282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676937587313307526761275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33805166899502153404696733 12676937587313307526761275)
  ·
    refine ⟨19015406380969961290141913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12676937587313307526761275 19015406380969961290141913)
    ·
      refine ⟨14261554785727470967606435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19015406380969961290141913 14261554785727470967606435)
      ·
        refine ⟨21392332178591206451409653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14261554785727470967606435 21392332178591206451409653)
        ·
          refine ⟨2005531141742925604819655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21392332178591206451409653 2005531141742925604819655)
          ·
            refine ⟨3008296712614388407229483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005531141742925604819655 3008296712614388407229483)
            ·
              refine ⟨4512445068921582610844225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008296712614388407229483 4512445068921582610844225)
              ·
                refine ⟨3384333801691186958133169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4512445068921582610844225 3384333801691186958133169)
                ·
                  refine ⟨2538250351268390218599877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384333801691186958133169 2538250351268390218599877)
                  ·
                    refine ⟨475921940862823165987477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538250351268390218599877 475921940862823165987477)
                    ·
                      rfl

theorem cell22_1390282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1390282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390282 prefixEnd_1390282 := by exact prefixLift 1390282
  have htrace : WordTrace (prefixWord ++ tailWord_1390282) baseStart_1390282 baseEnd_1390282 := by
    simpa [prefixWord, tailWord_1390282, baseEnd_1390282] using wordTrace_append hprefix tailTrace_1390282
  have hstable : (prefixWord ++ tailWord_1390282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390282).length < 2 ^ (prefixWord ++ tailWord_1390282).sum := by decide
  have hdescent : baseEnd_1390282 < baseStart_1390282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390301 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1390301 : Nat := 118140960795 + 1390301 * 2 ^ 59
def prefixEnd_1390301 : Nat := 4983230072969 + 3 ^ 40 * 1390301 * 2
def baseEnd_1390301 : Nat := 475928444951113449762419

theorem tailTrace_1390301 : CollatzResearch.WordTrace tailWord_1390301 prefixEnd_1390301 475928444951113449762419 := by
  unfold tailWord_1390301
  simp only [CollatzResearch.WordTrace]
  refine ⟨50708443336184396351986757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33805628890789597567991171 50708443336184396351986757)
  ·
    refine ⟨9507833125534574315997517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50708443336184396351986757 9507833125534574315997517)
    ·
      refine ⟨3565437422075465368499069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9507833125534574315997517 3565437422075465368499069)
      ·
        refine ⟨1337039033278299513187151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3565437422075465368499069 1337039033278299513187151)
        ·
          refine ⟨2005558549917449269780727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337039033278299513187151 2005558549917449269780727)
          ·
            refine ⟨3008337824876173904671091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005558549917449269780727 3008337824876173904671091)
            ·
              refine ⟨4512506737314260857006637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008337824876173904671091 4512506737314260857006637)
              ·
                refine ⟨1692190026492847821377489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4512506737314260857006637 1692190026492847821377489)
                ·
                  refine ⟨1269142519869635866033117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1692190026492847821377489 1269142519869635866033117)
                  ·
                    refine ⟨475928444951113449762419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269142519869635866033117 475928444951113449762419)
                    ·
                      rfl

theorem cell22_1390301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1390301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390301 prefixEnd_1390301 := by exact prefixLift 1390301
  have htrace : WordTrace (prefixWord ++ tailWord_1390301) baseStart_1390301 baseEnd_1390301 := by
    simpa [prefixWord, tailWord_1390301, baseEnd_1390301] using wordTrace_append hprefix tailTrace_1390301
  have hstable : (prefixWord ++ tailWord_1390301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390301).length < 2 ^ (prefixWord ++ tailWord_1390301).sum := by decide
  have hdescent : baseEnd_1390301 < baseStart_1390301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390346 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_1390346 : Nat := 118140960795 + 1390346 * 2 ^ 59
def prefixEnd_1390346 : Nat := 4983230072969 + 3 ^ 40 * 1390346 * 2
def baseEnd_1390346 : Nat := 475943849370748332387281

theorem tailTrace_1390346 : CollatzResearch.WordTrace tailWord_1390346 prefixEnd_1390346 475943849370748332387281 := by
  unfold tailWord_1390346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677521155255342259343723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33806723080680912691583261 12677521155255342259343723)
  ·
    refine ⟨19016281732883013389015585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12677521155255342259343723 19016281732883013389015585)
    ·
      refine ⟨14262211299662260041761689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19016281732883013389015585 14262211299662260041761689)
      ·
        refine ⟨10696658474746695031321267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14262211299662260041761689 10696658474746695031321267)
        ·
          refine ⟨16044987712120042546981901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10696658474746695031321267 16044987712120042546981901)
          ·
            refine ⟨6016870392045015955118213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16044987712120042546981901 6016870392045015955118213)
            ·
              refine ⟨1128163198508440491584665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6016870392045015955118213 1128163198508440491584665)
              ·
                refine ⟨846122398881330368688499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128163198508440491584665 846122398881330368688499)
                ·
                  refine ⟨1269183598321995553032749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846122398881330368688499 1269183598321995553032749)
                  ·
                    refine ⟨475943849370748332387281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269183598321995553032749 475943849370748332387281)
                    ·
                      rfl

theorem cell22_1390346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_1390346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390346 prefixEnd_1390346 := by exact prefixLift 1390346
  have htrace : WordTrace (prefixWord ++ tailWord_1390346) baseStart_1390346 baseEnd_1390346 := by
    simpa [prefixWord, tailWord_1390346, baseEnd_1390346] using wordTrace_append hprefix tailTrace_1390346
  have hstable : (prefixWord ++ tailWord_1390346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390346).length < 2 ^ (prefixWord ++ tailWord_1390346).sum := by decide
  have hdescent : baseEnd_1390346 < baseStart_1390346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390372 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1390372 : Nat := 118140960795 + 1390372 * 2 ^ 59
def prefixEnd_1390372 : Nat := 4983230072969 + 3 ^ 40 * 1390372 * 2
def baseEnd_1390372 : Nat := 475952749702092931237201

theorem tailTrace_1390372 : CollatzResearch.WordTrace tailWord_1390372 prefixEnd_1390372 475952749702092931237201 := by
  unfold tailWord_1390372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25355516459463587738910685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33807355279284783651880913 25355516459463587738910685)
  ·
    refine ⟨9508318672298845402091507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25355516459463587738910685 9508318672298845402091507)
    ·
      refine ⟨14262478008448268103137261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9508318672298845402091507 14262478008448268103137261)
      ·
        refine ⟨5348429253168100538676473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14262478008448268103137261 5348429253168100538676473)
        ·
          refine ⟨4011321939876075404007355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5348429253168100538676473 4011321939876075404007355)
          ·
            refine ⟨6016982909814113106011033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011321939876075404007355 6016982909814113106011033)
            ·
              refine ⟨4512737182360584829508275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6016982909814113106011033 4512737182360584829508275)
              ·
                refine ⟨6769105773540877244262413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512737182360584829508275 6769105773540877244262413)
                ·
                  refine ⟨2538414665077828966598405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6769105773540877244262413 2538414665077828966598405)
                  ·
                    refine ⟨475952749702092931237201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538414665077828966598405 475952749702092931237201)
                    ·
                      rfl

theorem cell22_1390372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1390372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390372 prefixEnd_1390372 := by exact prefixLift 1390372
  have htrace : WordTrace (prefixWord ++ tailWord_1390372) baseStart_1390372 baseEnd_1390372 := by
    simpa [prefixWord, tailWord_1390372, baseEnd_1390372] using wordTrace_append hprefix tailTrace_1390372
  have hstable : (prefixWord ++ tailWord_1390372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390372).length < 2 ^ (prefixWord ++ tailWord_1390372).sum := by decide
  have hdescent : baseEnd_1390372 < baseStart_1390372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390389 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1390389 : Nat := 118140960795 + 1390389 * 2 ^ 59
def prefixEnd_1390389 : Nat := 4983230072969 + 3 ^ 40 * 1390389 * 2
def baseEnd_1390389 : Nat := 475958569149510553562149

theorem tailTrace_1390389 : CollatzResearch.WordTrace tailWord_1390389 prefixEnd_1390389 475958569149510553562149 := by
  unfold tailWord_1390389
  simp only [CollatzResearch.WordTrace]
  refine ⟨50711652959865587381190221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33807768639910391587460147 50711652959865587381190221)
  ·
    refine ⟨19016869859949595267946333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50711652959865587381190221 19016869859949595267946333)
    ·
      refine ⟨7131326197481098225479875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19016869859949595267946333 7131326197481098225479875)
      ·
        refine ⟨10696989296221647338219813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131326197481098225479875 10696989296221647338219813)
        ·
          refine ⟨2005685493041558875916215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10696989296221647338219813 2005685493041558875916215)
          ·
            refine ⟨3008528239562338313874323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005685493041558875916215 3008528239562338313874323)
            ·
              refine ⟨4512792359343507470811485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008528239562338313874323 4512792359343507470811485)
              ·
                refine ⟨1692297134753815301554307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4512792359343507470811485 1692297134753815301554307)
                ·
                  refine ⟨2538445702130722952331461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692297134753815301554307 2538445702130722952331461)
                  ·
                    refine ⟨475958569149510553562149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538445702130722952331461 475958569149510553562149)
                    ·
                      rfl

theorem cell22_1390389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1390389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390389 prefixEnd_1390389 := by exact prefixLift 1390389
  have htrace : WordTrace (prefixWord ++ tailWord_1390389) baseStart_1390389 baseEnd_1390389 := by
    simpa [prefixWord, tailWord_1390389, baseEnd_1390389] using wordTrace_append hprefix tailTrace_1390389
  have hstable : (prefixWord ++ tailWord_1390389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390389).length < 2 ^ (prefixWord ++ tailWord_1390389).sum := by decide
  have hdescent : baseEnd_1390389 < baseStart_1390389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390432 : List Nat := [2, 1, 1, 3, 3, 2, 4, 6]
def baseStart_1390432 : Nat := 118140960795 + 1390432 * 2 ^ 59
def prefixEnd_1390432 : Nat := 4983230072969 + 3 ^ 40 * 1390432 * 2
def baseEnd_1390432 : Nat := 52885920992030308304113

theorem tailTrace_1390432 : CollatzResearch.WordTrace tailWord_1390432 prefixEnd_1390432 52885920992030308304113 := by
  unfold tailWord_1390432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356610649354902862502775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33808814199139870483337033 25356610649354902862502775)
  ·
    refine ⟨38034915974032354293754163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25356610649354902862502775 38034915974032354293754163)
    ·
      refine ⟨57052373961048531440631245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38034915974032354293754163 57052373961048531440631245)
      ·
        refine ⟨21394640235393199290236717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57052373961048531440631245 21394640235393199290236717)
        ·
          refine ⟨8022990088272449733838769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21394640235393199290236717 8022990088272449733838769)
          ·
            refine ⟨6017242566204337300379077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8022990088272449733838769 6017242566204337300379077)
            ·
              refine ⟨1128232981163313243821077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6017242566204337300379077 1128232981163313243821077)
              ·
                refine ⟨52885920992030308304113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1128232981163313243821077 52885920992030308304113)
                ·
                  rfl

theorem cell22_1390432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_1390432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390432 prefixEnd_1390432 := by exact prefixLift 1390432
  have htrace : WordTrace (prefixWord ++ tailWord_1390432) baseStart_1390432 baseEnd_1390432 := by
    simpa [prefixWord, tailWord_1390432, baseEnd_1390432] using wordTrace_append hprefix tailTrace_1390432
  have hstable : (prefixWord ++ tailWord_1390432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390432).length < 2 ^ (prefixWord ++ tailWord_1390432).sum := by decide
  have hdescent : baseEnd_1390432 < baseStart_1390432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390475 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_1390475 : Nat := 118140960795 + 1390475 * 2 ^ 59
def prefixEnd_1390475 : Nat := 4983230072969 + 3 ^ 40 * 1390475 * 2
def baseEnd_1390475 : Nat := 475988008707034995911885

theorem tailTrace_1390475 : CollatzResearch.WordTrace tailWord_1390475 prefixEnd_1390475 475988008707034995911885 := by
  unfold tailWord_1390475
  simp only [CollatzResearch.WordTrace]
  refine ⟨50714789637554024068820879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33809859758369349379213919 50714789637554024068820879)
  ·
    refine ⟨76072184456331036103231319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50714789637554024068820879 76072184456331036103231319)
    ·
      refine ⟨114108276684496554154846979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76072184456331036103231319 114108276684496554154846979)
      ·
        refine ⟨171162415026744831232270469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114108276684496554154846979 171162415026744831232270469)
        ·
          refine ⟨32092952817514655856050713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171162415026744831232270469 32092952817514655856050713)
          ·
            refine ⟨24069714613135991892038035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32092952817514655856050713 24069714613135991892038035)
            ·
              refine ⟨36104571919703987838057053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24069714613135991892038035 36104571919703987838057053)
              ·
                refine ⟨13539214469888995439271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36104571919703987838057053 13539214469888995439271395)
                ·
                  refine ⟨20308821704833493158907093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13539214469888995439271395 20308821704833493158907093)
                  ·
                    refine ⟨475988008707034995911885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20308821704833493158907093 475988008707034995911885)
                    ·
                      rfl

theorem cell22_1390475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_1390475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390475 prefixEnd_1390475 := by exact prefixLift 1390475
  have htrace : WordTrace (prefixWord ++ tailWord_1390475) baseStart_1390475 baseEnd_1390475 := by
    simpa [prefixWord, tailWord_1390475, baseEnd_1390475] using wordTrace_append hprefix tailTrace_1390475
  have hstable : (prefixWord ++ tailWord_1390475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390475).length < 2 ^ (prefixWord ++ tailWord_1390475).sum := by decide
  have hdescent : baseEnd_1390475 < baseStart_1390475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390505 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 10]
def baseStart_1390505 : Nat := 118140960795 + 1390505 * 2 ^ 59
def prefixEnd_1390505 : Nat := 4983230072969 + 3 ^ 40 * 1390505 * 2
def baseEnd_1390505 : Nat := 158666092773374972553931

theorem tailTrace_1390505 : CollatzResearch.WordTrace tailWord_1390505 prefixEnd_1390505 158666092773374972553931 := by
  unfold tailWord_1390505
  simp only [CollatzResearch.WordTrace]
  refine ⟨50715883827445339192412969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33810589218296892794941979 50715883827445339192412969)
  ·
    refine ⟨38036912870584004394309727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50715883827445339192412969 38036912870584004394309727)
    ·
      refine ⟨57055369305876006591464591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38036912870584004394309727 57055369305876006591464591)
      ·
        refine ⟨85583053958814009887196887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57055369305876006591464591 85583053958814009887196887)
        ·
          refine ⟨128374580938221014830795331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85583053958814009887196887 128374580938221014830795331)
          ·
            refine ⟨192561871407331522246192997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128374580938221014830795331 192561871407331522246192997)
            ·
              refine ⟨36105350888874660421161187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192561871407331522246192997 36105350888874660421161187)
              ·
                refine ⟨54158026333311990631741781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36105350888874660421161187 54158026333311990631741781)
                ·
                  refine ⟨158666092773374972553931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54158026333311990631741781 158666092773374972553931)
                  ·
                    rfl

theorem cell22_1390505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_1390505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390505 prefixEnd_1390505 := by exact prefixLift 1390505
  have htrace : WordTrace (prefixWord ++ tailWord_1390505) baseStart_1390505 baseEnd_1390505 := by
    simpa [prefixWord, tailWord_1390505, baseEnd_1390505] using wordTrace_append hprefix tailTrace_1390505
  have hstable : (prefixWord ++ tailWord_1390505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390505).length < 2 ^ (prefixWord ++ tailWord_1390505).sum := by decide
  have hdescent : baseEnd_1390505 < baseStart_1390505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390552 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_1390552 : Nat := 118140960795 + 1390552 * 2 ^ 59
def prefixEnd_1390552 : Nat := 4983230072969 + 3 ^ 40 * 1390552 * 2
def baseEnd_1390552 : Nat := 476014367380632461736649

theorem tailTrace_1390552 : CollatzResearch.WordTrace tailWord_1390552 prefixEnd_1390552 476014367380632461736649 := by
  unfold tailWord_1390552
  simp only [CollatzResearch.WordTrace]
  refine ⟨25358799029137533109686955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33811732038850044146249273 25358799029137533109686955)
  ·
    refine ⟨38038198543706299664530433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25358799029137533109686955 38038198543706299664530433)
    ·
      refine ⟨28528648907779724748397825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38038198543706299664530433 28528648907779724748397825)
      ·
        refine ⟨21396486680834793561298369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28528648907779724748397825 21396486680834793561298369)
        ·
          refine ⟨16047365010626095170973777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21396486680834793561298369 16047365010626095170973777)
          ·
            refine ⟨12035523757969571378230333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16047365010626095170973777 12035523757969571378230333)
            ·
              refine ⟨4513321409238589266836375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12035523757969571378230333 4513321409238589266836375)
              ·
                refine ⟨6769982113857883900254563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513321409238589266836375 6769982113857883900254563)
                ·
                  refine ⟨10154973170786825850381845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769982113857883900254563 10154973170786825850381845)
                  ·
                    refine ⟨476014367380632461736649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10154973170786825850381845 476014367380632461736649)
                    ·
                      rfl

theorem cell22_1390552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_1390552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390552 prefixEnd_1390552 := by exact prefixLift 1390552
  have htrace : WordTrace (prefixWord ++ tailWord_1390552) baseStart_1390552 baseEnd_1390552 := by
    simpa [prefixWord, tailWord_1390552, baseEnd_1390552] using wordTrace_append hprefix tailTrace_1390552
  have hstable : (prefixWord ++ tailWord_1390552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390552).length < 2 ^ (prefixWord ++ tailWord_1390552).sum := by decide
  have hdescent : baseEnd_1390552 < baseStart_1390552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390646 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1390646 : Nat := 118140960795 + 1390646 * 2 ^ 59
def prefixEnd_1390646 : Nat := 4983230072969 + 3 ^ 40 * 1390646 * 2
def baseEnd_1390646 : Nat := 158682181833882516628787

theorem tailTrace_1390646 : CollatzResearch.WordTrace tailWord_1390646 prefixEnd_1390646 158682181833882516628787 := by
  unfold tailWord_1390646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170064157495907517080987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33814017679956346848863861 3170064157495907517080987)
  ·
    refine ⟨4755096236243861275621481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3170064157495907517080987 4755096236243861275621481)
    ·
      refine ⟨3566322177182895956716111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4755096236243861275621481 3566322177182895956716111)
      ·
        refine ⟨5349483265774343935074167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566322177182895956716111 5349483265774343935074167)
        ·
          refine ⟨8024224898661515902611251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5349483265774343935074167 8024224898661515902611251)
          ·
            refine ⟨12036337347992273853916877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024224898661515902611251 12036337347992273853916877)
            ·
              refine ⟨4513626505497102695218829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12036337347992273853916877 4513626505497102695218829)
              ·
                refine ⟨1692609939561413510707061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4513626505497102695218829 1692609939561413510707061)
                ·
                  refine ⟨158682181833882516628787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1692609939561413510707061 158682181833882516628787)
                  ·
                    rfl

theorem cell22_1390646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1390646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390646 prefixEnd_1390646 := by exact prefixLift 1390646
  have htrace : WordTrace (prefixWord ++ tailWord_1390646) baseStart_1390646 baseEnd_1390646 := by
    simpa [prefixWord, tailWord_1390646, baseEnd_1390646] using wordTrace_append hprefix tailTrace_1390646
  have hstable : (prefixWord ++ tailWord_1390646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390646).length < 2 ^ (prefixWord ++ tailWord_1390646).sum := by decide
  have hdescent : baseEnd_1390646 < baseStart_1390646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390659 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 1, 4]
def baseStart_1390659 : Nat := 118140960795 + 1390659 * 2 ^ 59
def prefixEnd_1390659 : Nat := 4983230072969 + 3 ^ 40 * 1390659 * 2
def baseEnd_1390659 : Nat := 476050995667319849311321

theorem tailTrace_1390659 : CollatzResearch.WordTrace tailWord_1390659 prefixEnd_1390659 476050995667319849311321 := by
  unfold tailWord_1390659
  simp only [CollatzResearch.WordTrace]
  refine ⟨50721500668887423493519031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33814333779258282329012687 50721500668887423493519031)
  ·
    refine ⟨76082251003331135240278547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50721500668887423493519031 76082251003331135240278547)
    ·
      refine ⟨114123376504996702860417821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76082251003331135240278547 114123376504996702860417821)
      ·
        refine ⟨42796266189373763572656683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114123376504996702860417821 42796266189373763572656683)
        ·
          refine ⟨64194399284060645358985025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42796266189373763572656683 64194399284060645358985025)
          ·
            refine ⟨48145799463045484019238769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64194399284060645358985025 48145799463045484019238769)
            ·
              refine ⟨36109349597284113014429077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48145799463045484019238769 36109349597284113014429077)
              ·
                refine ⟨1692625762372692797551363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36109349597284113014429077 1692625762372692797551363)
                ·
                  refine ⟨2538938643559039196327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692625762372692797551363 2538938643559039196327045)
                  ·
                    refine ⟨476050995667319849311321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538938643559039196327045 476050995667319849311321)
                    ·
                      rfl

theorem cell22_1390659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 4].length) (baseStart_1390659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390659 prefixEnd_1390659 := by exact prefixLift 1390659
  have htrace : WordTrace (prefixWord ++ tailWord_1390659) baseStart_1390659 baseEnd_1390659 := by
    simpa [prefixWord, tailWord_1390659, baseEnd_1390659] using wordTrace_append hprefix tailTrace_1390659
  have hstable : (prefixWord ++ tailWord_1390659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390659).length < 2 ^ (prefixWord ++ tailWord_1390659).sum := by decide
  have hdescent : baseEnd_1390659 < baseStart_1390659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390706 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1390706 : Nat := 118140960795 + 1390706 * 2 ^ 59
def prefixEnd_1390706 : Nat := 4983230072969 + 3 ^ 40 * 1390706 * 2
def baseEnd_1390706 : Nat := 476067084727827393386177

theorem tailTrace_1390706 : CollatzResearch.WordTrace tailWord_1390706 prefixEnd_1390706 476067084727827393386177 := by
  unfold tailWord_1390706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680803724929287630119993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33815476599811433680319981 12680803724929287630119993)
  ·
    refine ⟨9510602793696965722589995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12680803724929287630119993 9510602793696965722589995)
    ·
      refine ⟨14265904190545448583884993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9510602793696965722589995 14265904190545448583884993)
      ·
        refine ⟨10699428142909086437913745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14265904190545448583884993 10699428142909086437913745)
        ·
          refine ⟨8024571107181814828435309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10699428142909086437913745 8024571107181814828435309)
          ·
            refine ⟨3009214165193180560663241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8024571107181814828435309 3009214165193180560663241)
            ·
              refine ⟨2256910623894885420497431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009214165193180560663241 2256910623894885420497431)
              ·
                refine ⟨3385365935842328130746147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256910623894885420497431 3385365935842328130746147)
                ·
                  refine ⟨5078048903763492196119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385365935842328130746147 5078048903763492196119221)
                  ·
                    refine ⟨476067084727827393386177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5078048903763492196119221 476067084727827393386177)
                    ·
                      rfl

theorem cell22_1390706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1390706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390706 prefixEnd_1390706 := by exact prefixLift 1390706
  have htrace : WordTrace (prefixWord ++ tailWord_1390706) baseStart_1390706 baseEnd_1390706 := by
    simpa [prefixWord, tailWord_1390706, baseEnd_1390706] using wordTrace_append hprefix tailTrace_1390706
  have hstable : (prefixWord ++ tailWord_1390706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390706).length < 2 ^ (prefixWord ++ tailWord_1390706).sum := by decide
  have hdescent : baseEnd_1390706 < baseStart_1390706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390721 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1390721 : Nat := 118140960795 + 1390721 * 2 ^ 59
def prefixEnd_1390721 : Nat := 4983230072969 + 3 ^ 40 * 1390721 * 2
def baseEnd_1390721 : Nat := 476072219534372354261131

theorem tailTrace_1390721 : CollatzResearch.WordTrace tailWord_1390721 prefixEnd_1390721 476072219534372354261131 := by
  unfold tailWord_1390721
  simp only [CollatzResearch.WordTrace]
  refine ⟨50723761994662808082276017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33815841329775205388184011 50723761994662808082276017)
  ·
    refine ⟨38042821495997106061707013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50723761994662808082276017 38042821495997106061707013)
    ·
      refine ⟨7133029030499457386570065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38042821495997106061707013 7133029030499457386570065)
      ·
        refine ⟨5349771772874593039927549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7133029030499457386570065 5349771772874593039927549)
        ·
          refine ⟨2006164414827972389972831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5349771772874593039927549 2006164414827972389972831)
          ·
            refine ⟨3009246622241958584959247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006164414827972389972831 3009246622241958584959247)
            ·
              refine ⟨4513869933362937877438871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009246622241958584959247 4513869933362937877438871)
              ·
                refine ⟨6770804900044406816158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513869933362937877438871 6770804900044406816158307)
                ·
                  refine ⟨10156207350066610224237461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6770804900044406816158307 10156207350066610224237461)
                  ·
                    refine ⟨476072219534372354261131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10156207350066610224237461 476072219534372354261131)
                    ·
                      rfl

theorem cell22_1390721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1390721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390721 prefixEnd_1390721 := by exact prefixLift 1390721
  have htrace : WordTrace (prefixWord ++ tailWord_1390721) baseStart_1390721 baseEnd_1390721 := by
    simpa [prefixWord, tailWord_1390721, baseEnd_1390721] using wordTrace_append hprefix tailTrace_1390721
  have hstable : (prefixWord ++ tailWord_1390721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390721).length < 2 ^ (prefixWord ++ tailWord_1390721).sum := by decide
  have hdescent : baseEnd_1390721 < baseStart_1390721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390740 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1390740 : Nat := 118140960795 + 1390740 * 2 ^ 59
def prefixEnd_1390740 : Nat := 4983230072969 + 3 ^ 40 * 1390740 * 2
def baseEnd_1390740 : Nat := 476078723622662638036073

theorem tailTrace_1390740 : CollatzResearch.WordTrace tailWord_1390740 prefixEnd_1390740 476078723622662638036073 := by
  unfold tailWord_1390740
  simp only [CollatzResearch.WordTrace]
  refine ⟨25362227490796987163608837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33816303321062649551478449 25362227490796987163608837)
  ·
    refine ⟨4755417654524435093176657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25362227490796987163608837 4755417654524435093176657)
    ·
      refine ⟨3566563240893326319882493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4755417654524435093176657 3566563240893326319882493)
      ·
        refine ⟨1337461215334997369955935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3566563240893326319882493 1337461215334997369955935)
        ·
          refine ⟨2006191823002496054933903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337461215334997369955935 2006191823002496054933903)
          ·
            refine ⟨3009287734503744082400855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006191823002496054933903 3009287734503744082400855)
            ·
              refine ⟨4513931601755616123601283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009287734503744082400855 4513931601755616123601283)
              ·
                refine ⟨6770897402633424185401925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513931601755616123601283 6770897402633424185401925)
                ·
                  refine ⟨1269543262993767034762861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6770897402633424185401925 1269543262993767034762861)
                  ·
                    refine ⟨476078723622662638036073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269543262993767034762861 476078723622662638036073)
                    ·
                      rfl

theorem cell22_1390740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1390740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390740 prefixEnd_1390740 := by exact prefixLift 1390740
  have htrace : WordTrace (prefixWord ++ tailWord_1390740) baseStart_1390740 baseEnd_1390740 := by
    simpa [prefixWord, tailWord_1390740, baseEnd_1390740] using wordTrace_append hprefix tailTrace_1390740
  have hstable : (prefixWord ++ tailWord_1390740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390740).length < 2 ^ (prefixWord ++ tailWord_1390740).sum := by decide
  have hdescent : baseEnd_1390740 < baseStart_1390740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390802 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_1390802 : Nat := 118140960795 + 1390802 * 2 ^ 59
def prefixEnd_1390802 : Nat := 4983230072969 + 3 ^ 40 * 1390802 * 2
def baseEnd_1390802 : Nat := 476099947489715142985883

theorem tailTrace_1390802 : CollatzResearch.WordTrace tailWord_1390802 prefixEnd_1390802 476099947489715142985883 := by
  unfold tailWord_1390802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12681679076842339728993665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33817810871579572610649773 12681679076842339728993665)
  ·
    refine ⟨9511259307631754796745249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12681679076842339728993665 9511259307631754796745249)
    ·
      refine ⟨7133444480723816097558937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9511259307631754796745249 7133444480723816097558937)
      ·
        refine ⟨5350083360542862073169203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7133444480723816097558937 5350083360542862073169203)
        ·
          refine ⟨8025125040814293109753805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350083360542862073169203 8025125040814293109753805)
          ·
            refine ⟨3009421890305359916157677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8025125040814293109753805 3009421890305359916157677)
            ·
              refine ⟨1128533208864509968559129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3009421890305359916157677 1128533208864509968559129)
              ·
                refine ⟨846399906648382476419347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128533208864509968559129 846399906648382476419347)
                ·
                  refine ⟨1269599859972573714629021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846399906648382476419347 1269599859972573714629021)
                  ·
                    refine ⟨476099947489715142985883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269599859972573714629021 476099947489715142985883)
                    ·
                      rfl

theorem cell22_1390802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_1390802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390802 prefixEnd_1390802 := by exact prefixLift 1390802
  have htrace : WordTrace (prefixWord ++ tailWord_1390802) baseStart_1390802 baseEnd_1390802 := by
    simpa [prefixWord, tailWord_1390802, baseEnd_1390802] using wordTrace_append hprefix tailTrace_1390802
  have hstable : (prefixWord ++ tailWord_1390802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390802).length < 2 ^ (prefixWord ++ tailWord_1390802).sum := by decide
  have hdescent : baseEnd_1390802 < baseStart_1390802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390841 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_1390841 : Nat := 118140960795 + 1390841 * 2 ^ 59
def prefixEnd_1390841 : Nat := 4983230072969 + 3 ^ 40 * 1390841 * 2
def baseEnd_1390841 : Nat := 476113297986732041260763

theorem tailTrace_1390841 : CollatzResearch.WordTrace tailWord_1390841 prefixEnd_1390841 476113297986732041260763 := by
  unfold tailWord_1390841
  simp only [CollatzResearch.WordTrace]
  refine ⟨50728138754228068576644377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33818759169485379051096251 50728138754228068576644377)
  ·
    refine ⟨38046104065671051432483283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50728138754228068576644377 38046104065671051432483283)
    ·
      refine ⟨57069156098506577148724925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38046104065671051432483283 57069156098506577148724925)
      ·
        refine ⟨21400933536939966430771847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57069156098506577148724925 21400933536939966430771847)
        ·
          refine ⟨32101400305409949646157771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21400933536939966430771847 32101400305409949646157771)
          ·
            refine ⟨48152100458114924469236657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32101400305409949646157771 48152100458114924469236657)
            ·
              refine ⟨36114075343586193351927493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48152100458114924469236657 36114075343586193351927493)
              ·
                refine ⟨6771389126922411253486405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36114075343586193351927493 6771389126922411253486405)
                ·
                  refine ⟨1269635461297952110028701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6771389126922411253486405 1269635461297952110028701)
                  ·
                    refine ⟨476113297986732041260763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269635461297952110028701 476113297986732041260763)
                    ·
                      rfl

theorem cell22_1390841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_1390841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390841 prefixEnd_1390841 := by exact prefixLift 1390841
  have htrace : WordTrace (prefixWord ++ tailWord_1390841) baseStart_1390841 baseEnd_1390841 := by
    simpa [prefixWord, tailWord_1390841, baseEnd_1390841] using wordTrace_append hprefix tailTrace_1390841
  have hstable : (prefixWord ++ tailWord_1390841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390841).length < 2 ^ (prefixWord ++ tailWord_1390841).sum := by decide
  have hdescent : baseEnd_1390841 < baseStart_1390841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390858 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1390858 : Nat := 118140960795 + 1390858 * 2 ^ 59
def prefixEnd_1390858 : Nat := 4983230072969 + 3 ^ 40 * 1390858 * 2
def baseEnd_1390858 : Nat := 476119117434149663585711

theorem tailTrace_1390858 : CollatzResearch.WordTrace tailWord_1390858 prefixEnd_1390858 476119117434149663585711 := by
  unfold tailWord_1390858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682189698791620120003307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33819172530110986986675485 12682189698791620120003307)
  ·
    refine ⟨19023284548187430180004961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12682189698791620120003307 19023284548187430180004961)
    ·
      refine ⟨14267463411140572635003721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19023284548187430180004961 14267463411140572635003721)
      ·
        refine ⟨10700597558355429476252791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14267463411140572635003721 10700597558355429476252791)
        ·
          refine ⟨16050896337533144214379187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10700597558355429476252791 16050896337533144214379187)
          ·
            refine ⟨24076344506299716321568781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16050896337533144214379187 24076344506299716321568781)
            ·
              refine ⟨9028629189862393620588293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24076344506299716321568781 9028629189862393620588293)
              ·
                refine ⟨1692867973099198803860305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9028629189862393620588293 1692867973099198803860305)
                ·
                  refine ⟨1269650979824399102895229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1692867973099198803860305 1269650979824399102895229)
                  ·
                    refine ⟨476119117434149663585711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269650979824399102895229 476119117434149663585711)
                    ·
                      rfl

theorem cell22_1390858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1390858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390858 prefixEnd_1390858 := by exact prefixLift 1390858
  have htrace : WordTrace (prefixWord ++ tailWord_1390858) baseStart_1390858 baseEnd_1390858 := by
    simpa [prefixWord, tailWord_1390858, baseEnd_1390858] using wordTrace_append hprefix tailTrace_1390858
  have hstable : (prefixWord ++ tailWord_1390858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390858).length < 2 ^ (prefixWord ++ tailWord_1390858).sum := by decide
  have hdescent : baseEnd_1390858 < baseStart_1390858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390871 : List Nat := [1, 1, 3, 4, 1, 2, 3, 7]
def baseStart_1390871 : Nat := 118140960795 + 1390871 * 2 ^ 59
def prefixEnd_1390871 : Nat := 4983230072969 + 3 ^ 40 * 1390871 * 2
def baseEnd_1390871 : Nat := 52902618622202440334519

theorem tailTrace_1390871 : CollatzResearch.WordTrace tailWord_1390871 prefixEnd_1390871 52902618622202440334519 := by
  unfold tailWord_1390871
  simp only [CollatzResearch.WordTrace]
  refine ⟨50729232944119383700236467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33819488629412922466824311 50729232944119383700236467)
  ·
    refine ⟨76093849416179075550354701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50729232944119383700236467 76093849416179075550354701)
    ·
      refine ⟨28535193531067153331383013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76093849416179075550354701 28535193531067153331383013)
      ·
        refine ⟨5350348787075091249634315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28535193531067153331383013 5350348787075091249634315)
        ·
          refine ⟨8025523180612636874451473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350348787075091249634315 8025523180612636874451473)
          ·
            refine ⟨6019142385459477655838605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8025523180612636874451473 6019142385459477655838605)
            ·
              refine ⟨2257178394547304120939477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6019142385459477655838605 2257178394547304120939477)
              ·
                refine ⟨52902618622202440334519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2257178394547304120939477 52902618622202440334519)
                ·
                  rfl

theorem cell22_1390871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 7].length) (baseStart_1390871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390871 prefixEnd_1390871 := by exact prefixLift 1390871
  have htrace : WordTrace (prefixWord ++ tailWord_1390871) baseStart_1390871 baseEnd_1390871 := by
    simpa [prefixWord, tailWord_1390871, baseEnd_1390871] using wordTrace_append hprefix tailTrace_1390871
  have hstable : (prefixWord ++ tailWord_1390871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390871).length < 2 ^ (prefixWord ++ tailWord_1390871).sum := by decide
  have hdescent : baseEnd_1390871 < baseStart_1390871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390920 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 1, 3]
def baseStart_1390920 : Nat := 118140960795 + 1390920 * 2 ^ 59
def prefixEnd_1390920 : Nat := 4983230072969 + 3 ^ 40 * 1390920 * 2
def baseEnd_1390920 : Nat := 476140341301202168535521

theorem tailTrace_1390920 : CollatzResearch.WordTrace tailWord_1390920 prefixEnd_1390920 476140341301202168535521 := by
  unfold tailWord_1390920
  simp only [CollatzResearch.WordTrace]
  refine ⟨25365510060470932534385107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33820680080627910045846809 25365510060470932534385107)
  ·
    refine ⟨38048265090706398801577661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25365510060470932534385107 38048265090706398801577661)
    ·
      refine ⟨14268099409014899550591623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38048265090706398801577661 14268099409014899550591623)
      ·
        refine ⟨21402149113522349325887435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14268099409014899550591623 21402149113522349325887435)
        ·
          refine ⟨32103223670283523988831153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21402149113522349325887435 32103223670283523988831153)
          ·
            refine ⟨24077417752712642991623365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32103223670283523988831153 24077417752712642991623365)
            ·
              refine ⟨4514515828633620560929381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24077417752712642991623365 4514515828633620560929381)
              ·
                refine ⟨846471717868803855174259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4514515828633620560929381 846471717868803855174259)
                ·
                  refine ⟨1269707576803205782761389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846471717868803855174259 1269707576803205782761389)
                  ·
                    refine ⟨476140341301202168535521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269707576803205782761389 476140341301202168535521)
                    ·
                      rfl

theorem cell22_1390920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_1390920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390920 prefixEnd_1390920 := by exact prefixLift 1390920
  have htrace : WordTrace (prefixWord ++ tailWord_1390920) baseStart_1390920 baseEnd_1390920 := by
    simpa [prefixWord, tailWord_1390920, baseEnd_1390920] using wordTrace_append hprefix tailTrace_1390920
  have hstable : (prefixWord ++ tailWord_1390920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390920).length < 2 ^ (prefixWord ++ tailWord_1390920).sum := by decide
  have hdescent : baseEnd_1390920 < baseStart_1390920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390954 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_1390954 : Nat := 118140960795 + 1390954 * 2 ^ 59
def prefixEnd_1390954 : Nat := 4983230072969 + 3 ^ 40 * 1390954 * 2
def baseEnd_1390954 : Nat := 476151980196037413185417

theorem tailTrace_1390954 : CollatzResearch.WordTrace tailWord_1390954 prefixEnd_1390954 476151980196037413185417 := by
  unfold tailWord_1390954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12683065050704672218876979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33821506801879125917005277 12683065050704672218876979)
  ·
    refine ⟨19024597576057008328315469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12683065050704672218876979 19024597576057008328315469)
    ·
      refine ⟨7134224091021378123118301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19024597576057008328315469 7134224091021378123118301)
      ·
        refine ⟨2675334034133016796169363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7134224091021378123118301 2675334034133016796169363)
        ·
          refine ⟨4013001051199525194254045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675334034133016796169363 4013001051199525194254045)
          ·
            refine ⟨1504875394199821947845267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4013001051199525194254045 1504875394199821947845267)
            ·
              refine ⟨2257313091299732921767901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504875394199821947845267 2257313091299732921767901)
              ·
                refine ⟨846492409237399845662963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257313091299732921767901 846492409237399845662963)
                ·
                  refine ⟨1269738613856099768494445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846492409237399845662963 1269738613856099768494445)
                  ·
                    refine ⟨476151980196037413185417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269738613856099768494445 476151980196037413185417)
                    ·
                      rfl

theorem cell22_1390954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_1390954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1390954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1390954 prefixEnd_1390954 := by exact prefixLift 1390954
  have htrace : WordTrace (prefixWord ++ tailWord_1390954) baseStart_1390954 baseEnd_1390954 := by
    simpa [prefixWord, tailWord_1390954, baseEnd_1390954] using wordTrace_append hprefix tailTrace_1390954
  have hstable : (prefixWord ++ tailWord_1390954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390954).length < 2 ^ (prefixWord ++ tailWord_1390954).sum := by decide
  have hdescent : baseEnd_1390954 < baseStart_1390954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391008 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_1391008 : Nat := 118140960795 + 1391008 * 2 ^ 59
def prefixEnd_1391008 : Nat := 4983230072969 + 3 ^ 40 * 1391008 * 2
def baseEnd_1391008 : Nat := 476170465499599272335251

theorem tailTrace_1391008 : CollatzResearch.WordTrace tailWord_1391008 prefixEnd_1391008 476170465499599272335251 := by
  unfold tailWord_1391008
  simp only [CollatzResearch.WordTrace]
  refine ⟨25367114872311528048986839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33822819829748704065315785 25367114872311528048986839)
  ·
    refine ⟨38050672308467292073480259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25367114872311528048986839 38050672308467292073480259)
    ·
      refine ⟨57076008462700938110220389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38050672308467292073480259 57076008462700938110220389)
      ·
        refine ⟨10701751586756425895666323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57076008462700938110220389 10701751586756425895666323)
        ·
          refine ⟨16052627380134638843499485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10701751586756425895666323 16052627380134638843499485)
          ·
            refine ⟨6019735267550489566312307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16052627380134638843499485 6019735267550489566312307)
            ·
              refine ⟨9029602901325734349468461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019735267550489566312307 9029602901325734349468461)
              ·
                refine ⟨3386101087997150381050673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9029602901325734349468461 3386101087997150381050673)
                ·
                  refine ⟨2539575815997862785788005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3386101087997150381050673 2539575815997862785788005)
                  ·
                    refine ⟨476170465499599272335251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539575815997862785788005 476170465499599272335251)
                    ·
                      rfl

theorem cell22_1391008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_1391008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391008 prefixEnd_1391008 := by exact prefixLift 1391008
  have htrace : WordTrace (prefixWord ++ tailWord_1391008) baseStart_1391008 baseEnd_1391008 := by
    simpa [prefixWord, tailWord_1391008, baseEnd_1391008] using wordTrace_append hprefix tailTrace_1391008
  have hstable : (prefixWord ++ tailWord_1391008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391008).length < 2 ^ (prefixWord ++ tailWord_1391008).sum := by decide
  have hdescent : baseEnd_1391008 < baseStart_1391008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391029 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 4]
def baseStart_1391029 : Nat := 118140960795 + 1391029 * 2 ^ 59
def prefixEnd_1391029 : Nat := 4983230072969 + 3 ^ 40 * 1391029 * 2
def baseEnd_1391029 : Nat := 158725884742920739186729

theorem tailTrace_1391029 : CollatzResearch.WordTrace tailWord_1391029 prefixEnd_1391029 158725884742920739186729 := by
  unfold tailWord_1391029
  simp only [CollatzResearch.WordTrace]
  refine ⟨50734995677546976684488141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33823330451697984456325427 50734995677546976684488141)
  ·
    refine ⟨19025623379080116256683053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50734995677546976684488141 19025623379080116256683053)
    ·
      refine ⟨7134608767155043596256145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19025623379080116256683053 7134608767155043596256145)
      ·
        refine ⟨5350956575366282697192109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7134608767155043596256145 5350956575366282697192109)
        ·
          refine ⟨2006608715762356011447041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5350956575366282697192109 2006608715762356011447041)
          ·
            refine ⟨1504956536821767008585281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006608715762356011447041 1504956536821767008585281)
            ·
              refine ⟨1128717402616325256438961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504956536821767008585281 1128717402616325256438961)
              ·
                refine ⟨846538051962243942329221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128717402616325256438961 846538051962243942329221)
                ·
                  refine ⟨158725884742920739186729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846538051962243942329221 158725884742920739186729)
                  ·
                    rfl

theorem cell22_1391029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_1391029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391029 prefixEnd_1391029 := by exact prefixLift 1391029
  have htrace : WordTrace (prefixWord ++ tailWord_1391029) baseStart_1391029 baseEnd_1391029 := by
    simpa [prefixWord, tailWord_1391029, baseEnd_1391029] using wordTrace_append hprefix tailTrace_1391029
  have hstable : (prefixWord ++ tailWord_1391029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391029).length < 2 ^ (prefixWord ++ tailWord_1391029).sum := by decide
  have hdescent : baseEnd_1391029 < baseStart_1391029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391051 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 9]
def baseStart_1391051 : Nat := 118140960795 + 1391051 * 2 ^ 59
def prefixEnd_1391051 : Nat := 4983230072969 + 3 ^ 40 * 1391051 * 2
def baseEnd_1391051 : Nat := 158728395092787164503373

theorem tailTrace_1391051 : CollatzResearch.WordTrace tailWord_1391051 prefixEnd_1391051 158728395092787164503373 := by
  unfold tailWord_1391051
  simp only [CollatzResearch.WordTrace]
  refine ⟨50735798083467274441789007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33823865388978182961192671 50735798083467274441789007)
  ·
    refine ⟨76103697125200911662683511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50735798083467274441789007 76103697125200911662683511)
    ·
      refine ⟨114155545687801367494025267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76103697125200911662683511 114155545687801367494025267)
      ·
        refine ⟨171233318531702051241037901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114155545687801367494025267 171233318531702051241037901)
        ·
          refine ⟨64212494449388269215389213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171233318531702051241037901 64212494449388269215389213)
          ·
            refine ⟨24079685418520600955770955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64212494449388269215389213 24079685418520600955770955)
            ·
              refine ⟨36119528127780901433656433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24079685418520600955770955 36119528127780901433656433)
              ·
                refine ⟨27089646095835676075242325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36119528127780901433656433 27089646095835676075242325)
                ·
                  refine ⟨158728395092787164503373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27089646095835676075242325 158728395092787164503373)
                  ·
                    rfl

theorem cell22_1391051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_1391051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391051 prefixEnd_1391051 := by exact prefixLift 1391051
  have htrace : WordTrace (prefixWord ++ tailWord_1391051) baseStart_1391051 baseEnd_1391051 := by
    simpa [prefixWord, tailWord_1391051, baseEnd_1391051] using wordTrace_append hprefix tailTrace_1391051
  have hstable : (prefixWord ++ tailWord_1391051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391051).length < 2 ^ (prefixWord ++ tailWord_1391051).sum := by decide
  have hdescent : baseEnd_1391051 < baseStart_1391051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391072 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 1, 3]
def baseStart_1391072 : Nat := 118140960795 + 1391072 * 2 ^ 59
def prefixEnd_1391072 : Nat := 4983230072969 + 3 ^ 40 * 1391072 * 2
def baseEnd_1391072 : Nat := 476192374007524438735055

theorem tailTrace_1391072 : CollatzResearch.WordTrace tailWord_1391072 prefixEnd_1391072 476192374007524438735055 := by
  unfold tailWord_1391072
  simp only [CollatzResearch.WordTrace]
  refine ⟨25368282008195597514151735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33824376010927463352202313 25368282008195597514151735)
  ·
    refine ⟨38052423012293396271227603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25368282008195597514151735 38052423012293396271227603)
    ·
      refine ⟨57078634518440094406841405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38052423012293396271227603 57078634518440094406841405)
      ·
        refine ⟨21404487944415035402565527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57078634518440094406841405 21404487944415035402565527)
        ·
          refine ⟨32106731916622553103848291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21404487944415035402565527 32106731916622553103848291)
          ·
            refine ⟨48160097874933829655772437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32106731916622553103848291 48160097874933829655772437)
            ·
              refine ⟨2257504587887523265114333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48160097874933829655772437 2257504587887523265114333)
              ·
                refine ⟨846564220457821224417875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257504587887523265114333 846564220457821224417875)
                ·
                  refine ⟨1269846330686731836626813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846564220457821224417875 1269846330686731836626813)
                  ·
                    refine ⟨476192374007524438735055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269846330686731836626813 476192374007524438735055)
                    ·
                      rfl

theorem cell22_1391072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_1391072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391072 prefixEnd_1391072 := by exact prefixLift 1391072
  have htrace : WordTrace (prefixWord ++ tailWord_1391072) baseStart_1391072 baseEnd_1391072 := by
    simpa [prefixWord, tailWord_1391072, baseEnd_1391072] using wordTrace_append hprefix tailTrace_1391072
  have hstable : (prefixWord ++ tailWord_1391072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391072).length < 2 ^ (prefixWord ++ tailWord_1391072).sum := by decide
  have hdescent : baseEnd_1391072 < baseStart_1391072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391085 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1391085 : Nat := 118140960795 + 1391085 * 2 ^ 59
def prefixEnd_1391085 : Nat := 4983230072969 + 3 ^ 40 * 1391085 * 2
def baseEnd_1391085 : Nat := 158732274724398912720005

theorem tailTrace_1391085 : CollatzResearch.WordTrace tailWord_1391085 prefixEnd_1391085 158732274724398912720005 := by
  unfold tailWord_1391085
  simp only [CollatzResearch.WordTrace]
  refine ⟨50737038165344098248526709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33824692110229398832351139 50737038165344098248526709)
  ·
    refine ⟨4756597328001009210799379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50737038165344098248526709 4756597328001009210799379)
    ·
      refine ⟨7134895992001513816199069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756597328001009210799379 7134895992001513816199069)
      ·
        refine ⟨2675585997000567681074651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7134895992001513816199069 2675585997000567681074651)
        ·
          refine ⟨4013378995500851521611977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675585997000567681074651 4013378995500851521611977)
          ·
            refine ⟨3010034246625638641208983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4013378995500851521611977 3010034246625638641208983)
            ·
              refine ⟨4515051369938457961813475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010034246625638641208983 4515051369938457961813475)
              ·
                refine ⟨6772577054907686942720213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515051369938457961813475 6772577054907686942720213)
                ·
                  refine ⟨158732274724398912720005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6772577054907686942720213 158732274724398912720005)
                  ·
                    rfl

theorem cell22_1391085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1391085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391085 prefixEnd_1391085 := by exact prefixLift 1391085
  have htrace : WordTrace (prefixWord ++ tailWord_1391085) baseStart_1391085 baseEnd_1391085 := by
    simpa [prefixWord, tailWord_1391085, baseEnd_1391085] using wordTrace_append hprefix tailTrace_1391085
  have hstable : (prefixWord ++ tailWord_1391085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391085).length < 2 ^ (prefixWord ++ tailWord_1391085).sum := by decide
  have hdescent : baseEnd_1391085 < baseStart_1391085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391098 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_1391098 : Nat := 118140960795 + 1391098 * 2 ^ 59
def prefixEnd_1391098 : Nat := 4983230072969 + 3 ^ 40 * 1391098 * 2
def baseEnd_1391098 : Nat := 476201274338869037584975

theorem tailTrace_1391098 : CollatzResearch.WordTrace tailWord_1391098 prefixEnd_1391098 476201274338869037584975 := by
  unfold tailWord_1391098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12684378078574250367187487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33825008209531334312499965 12684378078574250367187487)
  ·
    refine ⟨19026567117861375550781231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12684378078574250367187487 19026567117861375550781231)
    ·
      refine ⟨28539850676792063326171847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19026567117861375550781231 28539850676792063326171847)
      ·
        refine ⟨42809776015188094989257771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28539850676792063326171847 42809776015188094989257771)
        ·
          refine ⟨64214664022782142483886657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42809776015188094989257771 64214664022782142483886657)
          ·
            refine ⟨48160998017086606862914993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64214664022782142483886657 48160998017086606862914993)
            ·
              refine ⟨36120748512814955147186245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48160998017086606862914993 36120748512814955147186245)
              ·
                refine ⟨6772640346152804090097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36120748512814955147186245 6772640346152804090097421)
                ·
                  refine ⟨2539740129807301533786533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6772640346152804090097421 2539740129807301533786533)
                  ·
                    refine ⟨476201274338869037584975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539740129807301533786533 476201274338869037584975)
                    ·
                      rfl

theorem cell22_1391098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_1391098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391098 prefixEnd_1391098 := by exact prefixLift 1391098
  have htrace : WordTrace (prefixWord ++ tailWord_1391098) baseStart_1391098 baseEnd_1391098 := by
    simpa [prefixWord, tailWord_1391098, baseEnd_1391098] using wordTrace_append hprefix tailTrace_1391098
  have hstable : (prefixWord ++ tailWord_1391098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391098).length < 2 ^ (prefixWord ++ tailWord_1391098).sum := by decide
  have hdescent : baseEnd_1391098 < baseStart_1391098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391115 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 1, 4]
def baseStart_1391115 : Nat := 118140960795 + 1391115 * 2 ^ 59
def prefixEnd_1391115 : Nat := 4983230072969 + 3 ^ 40 * 1391115 * 2
def baseEnd_1391115 : Nat := 476207093786286659909923

theorem tailTrace_1391115 : CollatzResearch.WordTrace tailWord_1391115 prefixEnd_1391115 476207093786286659909923 := by
  unfold tailWord_1391115
  simp only [CollatzResearch.WordTrace]
  refine ⟨50738132355235413372118799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33825421570156942248079199 50738132355235413372118799)
  ·
    refine ⟨76107198532853120058178199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50738132355235413372118799 76107198532853120058178199)
    ·
      refine ⟨114160797799279680087267299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76107198532853120058178199 114160797799279680087267299)
      ·
        refine ⟨171241196698919520130900949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114160797799279680087267299 171241196698919520130900949)
        ·
          refine ⟨4013465547630926253067991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 171241196698919520130900949 4013465547630926253067991)
          ·
            refine ⟨6020198321446389379601987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013465547630926253067991 6020198321446389379601987)
            ·
              refine ⟨9030297482169584069402981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020198321446389379601987 9030297482169584069402981)
              ·
                refine ⟨1693180777906797013013059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9030297482169584069402981 1693180777906797013013059)
                ·
                  refine ⟨2539771166860195519519589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693180777906797013013059 2539771166860195519519589)
                  ·
                    refine ⟨476207093786286659909923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539771166860195519519589 476207093786286659909923)
                    ·
                      rfl

theorem cell22_1391115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 4].length) (baseStart_1391115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391115 prefixEnd_1391115 := by exact prefixLift 1391115
  have htrace : WordTrace (prefixWord ++ tailWord_1391115) baseStart_1391115 baseEnd_1391115 := by
    simpa [prefixWord, tailWord_1391115, baseEnd_1391115] using wordTrace_append hprefix tailTrace_1391115
  have hstable : (prefixWord ++ tailWord_1391115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391115).length < 2 ^ (prefixWord ++ tailWord_1391115).sum := by decide
  have hdescent : baseEnd_1391115 < baseStart_1391115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391162 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_1391162 : Nat := 118140960795 + 1391162 * 2 ^ 59
def prefixEnd_1391162 : Nat := 4983230072969 + 3 ^ 40 * 1391162 * 2
def baseEnd_1391162 : Nat := 476223182846794203984779

theorem tailTrace_1391162 : CollatzResearch.WordTrace tailWord_1391162 prefixEnd_1391162 476223182846794203984779 := by
  unfold tailWord_1391162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12684961646516285099769935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33826564390710093599386493 12684961646516285099769935)
  ·
    refine ⟨19027442469774427649654903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12684961646516285099769935 19027442469774427649654903)
    ·
      refine ⟨28541163704661641474482355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19027442469774427649654903 28541163704661641474482355)
      ·
        refine ⟨42811745556992462211723533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28541163704661641474482355 42811745556992462211723533)
        ·
          refine ⟨16054404583872173329396325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42811745556992462211723533 16054404583872173329396325)
          ·
            refine ⟨3010200859476032499261811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16054404583872173329396325 3010200859476032499261811)
            ·
              refine ⟨4515301289214048748892717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010200859476032499261811 4515301289214048748892717)
              ·
                refine ⟨1693237983455268280834769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4515301289214048748892717 1693237983455268280834769)
                ·
                  refine ⟨1269928487591451210626077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693237983455268280834769 1269928487591451210626077)
                  ·
                    refine ⟨476223182846794203984779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269928487591451210626077 476223182846794203984779)
                    ·
                      rfl

theorem cell22_1391162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_1391162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391162 prefixEnd_1391162 := by exact prefixLift 1391162
  have htrace : WordTrace (prefixWord ++ tailWord_1391162) baseStart_1391162 baseEnd_1391162 := by
    simpa [prefixWord, tailWord_1391162, baseEnd_1391162] using wordTrace_append hprefix tailTrace_1391162
  have hstable : (prefixWord ++ tailWord_1391162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391162).length < 2 ^ (prefixWord ++ tailWord_1391162).sum := by decide
  have hdescent : baseEnd_1391162 < baseStart_1391162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391166 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1391166 : Nat := 118140960795 + 1391166 * 2 ^ 59
def prefixEnd_1391166 : Nat := 4983230072969 + 3 ^ 40 * 1391166 * 2
def baseEnd_1391166 : Nat := 476224552128539526884767

theorem tailTrace_1391166 : CollatzResearch.WordTrace tailWord_1391166 prefixEnd_1391166 476224552128539526884767 := by
  unfold tailWord_1391166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342499059756331135278169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33826661652033766054816901 6342499059756331135278169)
  ·
    refine ⟨4756874294817248351458627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6342499059756331135278169 4756874294817248351458627)
    ·
      refine ⟨7135311442225872527187941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756874294817248351458627 7135311442225872527187941)
      ·
        refine ⟨1337870895417351098847739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7135311442225872527187941 1337870895417351098847739)
        ·
          refine ⟨2006806343126026648271609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337870895417351098847739 2006806343126026648271609)
          ·
            refine ⟨1505104757344519986203707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006806343126026648271609 1505104757344519986203707)
            ·
              refine ⟨2257657136016779979305561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505104757344519986203707 2257657136016779979305561)
              ·
                refine ⟨1693242852012584984479171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257657136016779979305561 1693242852012584984479171)
                ·
                  refine ⟨2539864278018877476718757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693242852012584984479171 2539864278018877476718757)
                  ·
                    refine ⟨476224552128539526884767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539864278018877476718757 476224552128539526884767)
                    ·
                      rfl

theorem cell22_1391166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1391166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391166 prefixEnd_1391166 := by exact prefixLift 1391166
  have htrace : WordTrace (prefixWord ++ tailWord_1391166) baseStart_1391166 baseEnd_1391166 := by
    simpa [prefixWord, tailWord_1391166, baseEnd_1391166] using wordTrace_append hprefix tailTrace_1391166
  have hstable : (prefixWord ++ tailWord_1391166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391166).length < 2 ^ (prefixWord ++ tailWord_1391166).sum := by decide
  have hdescent : baseEnd_1391166 < baseStart_1391166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391198 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1391198 : Nat := 118140960795 + 1391198 * 2 ^ 59
def prefixEnd_1391198 : Nat := 4983230072969 + 3 ^ 40 * 1391198 * 2
def baseEnd_1391198 : Nat := 158745168794167370028223

theorem tailTrace_1391198 : CollatzResearch.WordTrace tailWord_1391198 prefixEnd_1391198 158745168794167370028223 := by
  unfold tailWord_1391198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342644951741839818423781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33827439742623145698260165 6342644951741839818423781)
  ·
    refine ⟨1189245928451594965954459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6342644951741839818423781 1189245928451594965954459)
    ·
      refine ⟨1783868892677392448931689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189245928451594965954459 1783868892677392448931689)
      ·
        refine ⟨1337901669508044336698767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1783868892677392448931689 1337901669508044336698767)
        ·
          refine ⟨2006852504262066505048151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337901669508044336698767 2006852504262066505048151)
          ·
            refine ⟨3010278756393099757572227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006852504262066505048151 3010278756393099757572227)
            ·
              refine ⟨4515418134589649636358341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010278756393099757572227 4515418134589649636358341)
              ·
                refine ⟨846640900235559306817189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4515418134589649636358341 846640900235559306817189)
                ·
                  refine ⟨158745168794167370028223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846640900235559306817189 158745168794167370028223)
                  ·
                    rfl

theorem cell22_1391198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1391198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391198 prefixEnd_1391198 := by exact prefixLift 1391198
  have htrace : WordTrace (prefixWord ++ tailWord_1391198) baseStart_1391198 baseEnd_1391198 := by
    simpa [prefixWord, tailWord_1391198, baseEnd_1391198] using wordTrace_append hprefix tailTrace_1391198
  have hstable : (prefixWord ++ tailWord_1391198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391198).length < 2 ^ (prefixWord ++ tailWord_1391198).sum := by decide
  have hdescent : baseEnd_1391198 < baseStart_1391198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391252 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1391252 : Nat := 118140960795 + 1391252 * 2 ^ 59
def prefixEnd_1391252 : Nat := 4983230072969 + 3 ^ 40 * 1391252 * 2
def baseEnd_1391252 : Nat := 476253991686063969234503

theorem tailTrace_1391252 : CollatzResearch.WordTrace tailWord_1391252 prefixEnd_1391252 476253991686063969234503 := by
  unfold tailWord_1391252
  simp only [CollatzResearch.WordTrace]
  refine ⟨25371564577869542884928005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33828752770492723846570673 25371564577869542884928005)
  ·
    refine ⟨4757168358350539290924001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25371564577869542884928005 4757168358350539290924001)
    ·
      refine ⟨3567876268762904468193001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4757168358350539290924001 3567876268762904468193001)
      ·
        refine ⟨2675907201572178351144751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3567876268762904468193001 2675907201572178351144751)
        ·
          refine ⟨4013860802358267526717127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675907201572178351144751 4013860802358267526717127)
          ·
            refine ⟨6020791203537401290075691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013860802358267526717127 6020791203537401290075691)
            ·
              refine ⟨9031186805306101935113537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020791203537401290075691 9031186805306101935113537)
              ·
                refine ⟨6773390103979576451335153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9031186805306101935113537 6773390103979576451335153)
                ·
                  refine ⟨5080042577984682338501365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773390103979576451335153 5080042577984682338501365)
                  ·
                    refine ⟨476253991686063969234503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5080042577984682338501365 476253991686063969234503)
                    ·
                      rfl

theorem cell22_1391252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1391252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391252 prefixEnd_1391252 := by exact prefixLift 1391252
  have htrace : WordTrace (prefixWord ++ tailWord_1391252) baseStart_1391252 baseEnd_1391252 := by
    simpa [prefixWord, tailWord_1391252, baseEnd_1391252] using wordTrace_append hprefix tailTrace_1391252
  have hstable : (prefixWord ++ tailWord_1391252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391252).length < 2 ^ (prefixWord ++ tailWord_1391252).sum := by decide
  have hdescent : baseEnd_1391252 < baseStart_1391252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391271 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 5]
def baseStart_1391271 : Nat := 118140960795 + 1391271 * 2 ^ 59
def prefixEnd_1391271 : Nat := 4983230072969 + 3 ^ 40 * 1391271 * 2
def baseEnd_1391271 : Nat := 158753498591451417669815

theorem tailTrace_1391271 : CollatzResearch.WordTrace tailWord_1391271 prefixEnd_1391271 158753498591451417669815 := by
  unfold tailWord_1391271
  simp only [CollatzResearch.WordTrace]
  refine ⟨50743822142670252014797667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33829214761780168009865111 50743822142670252014797667)
  ·
    refine ⟨76115733214005378022196501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50743822142670252014797667 76115733214005378022196501)
    ·
      refine ⟨3567924994406502094790461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76115733214005378022196501 3567924994406502094790461)
      ·
        refine ⟨1337971872902438285546423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3567924994406502094790461 1337971872902438285546423)
        ·
          refine ⟨2006957809353657428319635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337971872902438285546423 2006957809353657428319635)
          ·
            refine ⟨3010436714030486142479453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006957809353657428319635 3010436714030486142479453)
            ·
              refine ⟨1128913767761432303429795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3010436714030486142479453 1128913767761432303429795)
              ·
                refine ⟨1693370651642148455144693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128913767761432303429795 1693370651642148455144693)
                ·
                  refine ⟨158753498591451417669815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693370651642148455144693 158753498591451417669815)
                  ·
                    rfl

theorem cell22_1391271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 5].length) (baseStart_1391271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391271 prefixEnd_1391271 := by exact prefixLift 1391271
  have htrace : WordTrace (prefixWord ++ tailWord_1391271) baseStart_1391271 baseEnd_1391271 := by
    simpa [prefixWord, tailWord_1391271, baseEnd_1391271] using wordTrace_append hprefix tailTrace_1391271
  have hstable : (prefixWord ++ tailWord_1391271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391271).length < 2 ^ (prefixWord ++ tailWord_1391271).sum := by decide
  have hdescent : baseEnd_1391271 < baseStart_1391271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391295 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 1, 6]
def baseStart_1391295 : Nat := 118140960795 + 1391295 * 2 ^ 59
def prefixEnd_1391295 : Nat := 4983230072969 + 3 ^ 40 * 1391295 * 2
def baseEnd_1391295 : Nat := 476268711464826190409371

theorem tailTrace_1391295 : CollatzResearch.WordTrace tailWord_1391295 prefixEnd_1391295 476268711464826190409371 := by
  unfold tailWord_1391295
  simp only [CollatzResearch.WordTrace]
  refine ⟨50744697494583304113671339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33829798329722202742447559 50744697494583304113671339)
  ·
    refine ⟨76117046241874956170507009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50744697494583304113671339 76117046241874956170507009)
    ·
      refine ⟨57087784681406217127880257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76117046241874956170507009 57087784681406217127880257)
      ·
        refine ⟨42815838511054662845910193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57087784681406217127880257 42815838511054662845910193)
        ·
          refine ⟨32111878883290997134432645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42815838511054662845910193 32111878883290997134432645)
          ·
            refine ⟨6020977290617061962706121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32111878883290997134432645 6020977290617061962706121)
            ·
              refine ⟨4515732967962796472029591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6020977290617061962706121 4515732967962796472029591)
              ·
                refine ⟨6773599451944194708044387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515732967962796472029591 6773599451944194708044387)
                ·
                  refine ⟨10160399177916292062066581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6773599451944194708044387 10160399177916292062066581)
                  ·
                    refine ⟨476268711464826190409371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10160399177916292062066581 476268711464826190409371)
                    ·
                      rfl

theorem cell22_1391295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_1391295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391295 prefixEnd_1391295 := by exact prefixLift 1391295
  have htrace : WordTrace (prefixWord ++ tailWord_1391295) baseStart_1391295 baseEnd_1391295 := by
    simpa [prefixWord, tailWord_1391295, baseEnd_1391295] using wordTrace_append hprefix tailTrace_1391295
  have hstable : (prefixWord ++ tailWord_1391295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391295).length < 2 ^ (prefixWord ++ tailWord_1391295).sum := by decide
  have hdescent : baseEnd_1391295 < baseStart_1391295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391310 : List Nat := [4, 1, 1, 1, 3, 2, 10]
def baseStart_1391310 : Nat := 118140960795 + 1391310 * 2 ^ 59
def prefixEnd_1391310 : Nat := 4983230072969 + 3 ^ 40 * 1391310 * 2
def baseEnd_1391310 : Nat := 17639772084124857454975

theorem tailTrace_1391310 : CollatzResearch.WordTrace tailWord_1391310 prefixEnd_1391310 17639772084124857454975 := by
  unfold tailWord_1391310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343155573691120209433423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33830163059685974450311589 6343155573691120209433423)
  ·
    refine ⟨9514733360536680314150135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343155573691120209433423 9514733360536680314150135)
    ·
      refine ⟨14272100040805020471225203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9514733360536680314150135 14272100040805020471225203)
      ·
        refine ⟨21408150061207530706837805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14272100040805020471225203 21408150061207530706837805)
        ·
          refine ⟨8028056272952824015064177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21408150061207530706837805 8028056272952824015064177)
          ·
            refine ⟨6021042204714618011298133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8028056272952824015064177 6021042204714618011298133)
            ·
              refine ⟨17639772084124857454975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6021042204714618011298133 17639772084124857454975)
              ·
                rfl

theorem cell22_1391310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 10].length) (baseStart_1391310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391310 prefixEnd_1391310 := by exact prefixLift 1391310
  have htrace : WordTrace (prefixWord ++ tailWord_1391310) baseStart_1391310 baseEnd_1391310 := by
    simpa [prefixWord, tailWord_1391310, baseEnd_1391310] using wordTrace_append hprefix tailTrace_1391310
  have hstable : (prefixWord ++ tailWord_1391310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391310).length < 2 ^ (prefixWord ++ tailWord_1391310).sum := by decide
  have hdescent : baseEnd_1391310 < baseStart_1391310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391316 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1391316 : Nat := 118140960795 + 1391316 * 2 ^ 59
def prefixEnd_1391316 : Nat := 4983230072969 + 3 ^ 40 * 1391316 * 2
def baseEnd_1391316 : Nat := 158758633397996378544769

theorem tailTrace_1391316 : CollatzResearch.WordTrace tailWord_1391316 prefixEnd_1391316 158758633397996378544769 := by
  unfold tailWord_1391316
  simp only [CollatzResearch.WordTrace]
  refine ⟨25372731713753612350092901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33830308951671483133457201 25372731713753612350092901)
  ·
    refine ⟨4757387196328802315642419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25372731713753612350092901 4757387196328802315642419)
    ·
      refine ⟨7136080794493203473463629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757387196328802315642419 7136080794493203473463629)
      ·
        refine ⟨2676030297934951302548861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7136080794493203473463629 2676030297934951302548861)
        ·
          refine ⟨1003511361725606738455823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2676030297934951302548861 1003511361725606738455823)
          ·
            refine ⟨1505267042588410107683735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003511361725606738455823 1505267042588410107683735)
            ·
              refine ⟨2257900563882615161525603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505267042588410107683735 2257900563882615161525603)
              ·
                refine ⟨3386850845823922742288405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257900563882615161525603 3386850845823922742288405)
                ·
                  refine ⟨158758633397996378544769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3386850845823922742288405 158758633397996378544769)
                  ·
                    rfl

theorem cell22_1391316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1391316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391316 prefixEnd_1391316 := by exact prefixLift 1391316
  have htrace : WordTrace (prefixWord ++ tailWord_1391316) baseStart_1391316 baseEnd_1391316 := by
    simpa [prefixWord, tailWord_1391316, baseEnd_1391316] using wordTrace_append hprefix tailTrace_1391316
  have hstable : (prefixWord ++ tailWord_1391316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391316).length < 2 ^ (prefixWord ++ tailWord_1391316).sum := by decide
  have hdescent : baseEnd_1391316 < baseStart_1391316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391331 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 2, 3]
def baseStart_1391331 : Nat := 118140960795 + 1391331 * 2 ^ 59
def prefixEnd_1391331 : Nat := 4983230072969 + 3 ^ 40 * 1391331 * 2
def baseEnd_1391331 : Nat := 476281035000534096509261

theorem tailTrace_1391331 : CollatzResearch.WordTrace tailWord_1391331 prefixEnd_1391331 476281035000534096509261 := by
  unfold tailWord_1391331
  simp only [CollatzResearch.WordTrace]
  refine ⟨50746010522452882261981847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33830673681635254841321231 50746010522452882261981847)
  ·
    refine ⟨76119015783679323392972771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50746010522452882261981847 76119015783679323392972771)
    ·
      refine ⟨114178523675518985089459157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76119015783679323392972771 114178523675518985089459157)
      ·
        refine ⟨2676059148644976213034199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 114178523675518985089459157 2676059148644976213034199)
        ·
          refine ⟨4014088722967464319551299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676059148644976213034199 4014088722967464319551299)
          ·
            refine ⟨6021133084451196479326949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014088722967464319551299 6021133084451196479326949)
            ·
              refine ⟨1128962453334599339873803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6021133084451196479326949 1128962453334599339873803)
              ·
                refine ⟨1693443680001899009810705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128962453334599339873803 1693443680001899009810705)
                ·
                  refine ⟨1270082760001424257358029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693443680001899009810705 1270082760001424257358029)
                  ·
                    refine ⟨476281035000534096509261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270082760001424257358029 476281035000534096509261)
                    ·
                      rfl

theorem cell22_1391331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 3].length) (baseStart_1391331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391331 prefixEnd_1391331 := by exact prefixLift 1391331
  have htrace : WordTrace (prefixWord ++ tailWord_1391331) baseStart_1391331 baseEnd_1391331 := by
    simpa [prefixWord, tailWord_1391331, baseEnd_1391331] using wordTrace_append hprefix tailTrace_1391331
  have hstable : (prefixWord ++ tailWord_1391331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391331).length < 2 ^ (prefixWord ++ tailWord_1391331).sum := by decide
  have hdescent : baseEnd_1391331 < baseStart_1391331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391359 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 1, 3]
def baseStart_1391359 : Nat := 118140960795 + 1391359 * 2 ^ 59
def prefixEnd_1391359 : Nat := 4983230072969 + 3 ^ 40 * 1391359 * 2
def baseEnd_1391359 : Nat := 476290619972751356809175

theorem tailTrace_1391359 : CollatzResearch.WordTrace tailWord_1391359 prefixEnd_1391359 476290619972751356809175 := by
  unfold tailWord_1391359
  simp only [CollatzResearch.WordTrace]
  refine ⟨50747031766351443044001131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33831354510900962029334087 50747031766351443044001131)
  ·
    refine ⟨76120547649527164566001697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50747031766351443044001131 76120547649527164566001697)
    ·
      refine ⟨57090410737145373424501273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76120547649527164566001697 57090410737145373424501273)
      ·
        refine ⟨42817808052859030068375955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57090410737145373424501273 42817808052859030068375955)
        ·
          refine ⟨64226712079288545102563933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42817808052859030068375955 64226712079288545102563933)
          ·
            refine ⟨24085017029733204413461475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64226712079288545102563933 24085017029733204413461475)
            ·
              refine ⟨36127525544599806620192213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24085017029733204413461475 36127525544599806620192213)
              ·
                refine ⟨846738879951557967660755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36127525544599806620192213 846738879951557967660755)
                ·
                  refine ⟨1270108319927336951491133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846738879951557967660755 1270108319927336951491133)
                  ·
                    refine ⟨476290619972751356809175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270108319927336951491133 476290619972751356809175)
                    ·
                      rfl

theorem cell22_1391359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_1391359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391359 prefixEnd_1391359 := by exact prefixLift 1391359
  have htrace : WordTrace (prefixWord ++ tailWord_1391359) baseStart_1391359 baseEnd_1391359 := by
    simpa [prefixWord, tailWord_1391359, baseEnd_1391359] using wordTrace_append hprefix tailTrace_1391359
  have hstable : (prefixWord ++ tailWord_1391359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391359).length < 2 ^ (prefixWord ++ tailWord_1391359).sum := by decide
  have hdescent : baseEnd_1391359 < baseStart_1391359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391447 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 1, 6]
def baseStart_1391447 : Nat := 118140960795 + 1391447 * 2 ^ 59
def prefixEnd_1391447 : Nat := 4983230072969 + 3 ^ 40 * 1391447 * 2
def baseEnd_1391447 : Nat := 476320744171148460608905

theorem tailTrace_1391447 : CollatzResearch.WordTrace tailWord_1391447 prefixEnd_1391447 476320744171148460608905 := by
  unfold tailWord_1391447
  simp only [CollatzResearch.WordTrace]
  refine ⟨50750241390032634073204595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33833494260021756048803063 50750241390032634073204595)
  ·
    refine ⟨76125362085048951109806893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50750241390032634073204595 76125362085048951109806893)
    ·
      refine ⟨28547010781893356666177585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76125362085048951109806893 28547010781893356666177585)
      ·
        refine ⟨21410258086420017499633189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28547010781893356666177585 21410258086420017499633189)
        ·
          refine ⟨4014423391203753281181223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21410258086420017499633189 4014423391203753281181223)
          ·
            refine ⟨6021635086805629921771835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014423391203753281181223 6021635086805629921771835)
            ·
              refine ⟨9032452630208444882657753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021635086805629921771835 9032452630208444882657753)
              ·
                refine ⟨6774339472656333661993315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9032452630208444882657753 6774339472656333661993315)
                ·
                  refine ⟨10161509208984500492989973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6774339472656333661993315 10161509208984500492989973)
                  ·
                    refine ⟨476320744171148460608905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10161509208984500492989973 476320744171148460608905)
                    ·
                      rfl

theorem cell22_1391447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_1391447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391447 prefixEnd_1391447 := by exact prefixLift 1391447
  have htrace : WordTrace (prefixWord ++ tailWord_1391447) baseStart_1391447 baseEnd_1391447 := by
    simpa [prefixWord, tailWord_1391447, baseEnd_1391447] using wordTrace_append hprefix tailTrace_1391447
  have hstable : (prefixWord ++ tailWord_1391447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391447).length < 2 ^ (prefixWord ++ tailWord_1391447).sum := by decide
  have hdescent : baseEnd_1391447 < baseStart_1391447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391449 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_1391449 : Nat := 118140960795 + 1391449 * 2 ^ 59
def prefixEnd_1391449 : Nat := 4983230072969 + 3 ^ 40 * 1391449 * 2
def baseEnd_1391449 : Nat := 476321428812021122058899

theorem tailTrace_1391449 : CollatzResearch.WordTrace tailWord_1391449 prefixEnd_1391449 476321428812021122058899 := by
  unfold tailWord_1391449
  simp only [CollatzResearch.WordTrace]
  refine ⟨50750314336025388414777401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33833542890683592276518267 50750314336025388414777401)
  ·
    refine ⟨38062735752019041311083051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50750314336025388414777401 38062735752019041311083051)
    ·
      refine ⟨57094103628028561966624577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38062735752019041311083051 57094103628028561966624577)
      ·
        refine ⟨42820577721021421474968433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57094103628028561966624577 42820577721021421474968433)
        ·
          refine ⟨32115433290766066106226325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42820577721021421474968433 32115433290766066106226325)
          ·
            refine ⟨1505410935504659348729359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32115433290766066106226325 1505410935504659348729359)
            ·
              refine ⟨2258116403256989023094039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505410935504659348729359 2258116403256989023094039)
              ·
                refine ⟨3387174604885483534641059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258116403256989023094039 3387174604885483534641059)
                ·
                  refine ⟨5080761907328225301961589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387174604885483534641059 5080761907328225301961589)
                  ·
                    refine ⟨476321428812021122058899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5080761907328225301961589 476321428812021122058899)
                    ·
                      rfl

theorem cell22_1391449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_1391449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391449 prefixEnd_1391449 := by exact prefixLift 1391449
  have htrace : WordTrace (prefixWord ++ tailWord_1391449) baseStart_1391449 baseEnd_1391449 := by
    simpa [prefixWord, tailWord_1391449, baseEnd_1391449] using wordTrace_append hprefix tailTrace_1391449
  have hstable : (prefixWord ++ tailWord_1391449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391449).length < 2 ^ (prefixWord ++ tailWord_1391449).sum := by decide
  have hdescent : baseEnd_1391449 < baseStart_1391449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391492 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1391492 : Nat := 118140960795 + 1391492 * 2 ^ 59
def prefixEnd_1391492 : Nat := 4983230072969 + 3 ^ 40 * 1391492 * 2
def baseEnd_1391492 : Nat := 476336148590783343233767

theorem tailTrace_1391492 : CollatzResearch.WordTrace tailWord_1391492 prefixEnd_1391492 476336148590783343233767 := by
  unfold tailWord_1391492
  simp only [CollatzResearch.WordTrace]
  refine ⟨25375941337434803379296365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33834588449913071172395153 25375941337434803379296365)
  ·
    refine ⟨9515978001538051267236137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25375941337434803379296365 9515978001538051267236137)
    ·
      refine ⟨7136983501153538450427103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9515978001538051267236137 7136983501153538450427103)
      ·
        refine ⟨10705475251730307675640655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136983501153538450427103 10705475251730307675640655)
        ·
          refine ⟨16058212877595461513460983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10705475251730307675640655 16058212877595461513460983)
          ·
            refine ⟨24087319316393192270191475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16058212877595461513460983 24087319316393192270191475)
            ·
              refine ⟨36130978974589788405287213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24087319316393192270191475 36130978974589788405287213)
              ·
                refine ⟨13549117115471170651982705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36130978974589788405287213 13549117115471170651982705)
                ·
                  refine ⟨10161837836603377988987029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13549117115471170651982705 10161837836603377988987029)
                  ·
                    refine ⟨476336148590783343233767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10161837836603377988987029 476336148590783343233767)
                    ·
                      rfl

theorem cell22_1391492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1391492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391492 prefixEnd_1391492 := by exact prefixLift 1391492
  have htrace : WordTrace (prefixWord ++ tailWord_1391492) baseStart_1391492 baseEnd_1391492 := by
    simpa [prefixWord, tailWord_1391492, baseEnd_1391492] using wordTrace_append hprefix tailTrace_1391492
  have hstable : (prefixWord ++ tailWord_1391492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391492).length < 2 ^ (prefixWord ++ tailWord_1391492).sum := by decide
  have hdescent : baseEnd_1391492 < baseStart_1391492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391545 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 1, 3]
def baseStart_1391545 : Nat := 118140960795 + 1391545 * 2 ^ 59
def prefixEnd_1391545 : Nat := 4983230072969 + 3 ^ 40 * 1391545 * 2
def baseEnd_1391545 : Nat := 476354291573908871658605

theorem tailTrace_1391545 : CollatzResearch.WordTrace tailWord_1391545 prefixEnd_1391545 476354291573908871658605 := by
  unfold tailWord_1391545
  simp only [CollatzResearch.WordTrace]
  refine ⟨50753815743677596810272089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33835877162451731206848059 50753815743677596810272089)
  ·
    refine ⟨38065361807758197607704067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50753815743677596810272089 38065361807758197607704067)
    ·
      refine ⟨57098042711637296411556101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38065361807758197607704067 57098042711637296411556101)
      ·
        refine ⟨10705883008431993077166769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57098042711637296411556101 10705883008431993077166769)
        ·
          refine ⟨8029412256323994807875077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10705883008431993077166769 8029412256323994807875077)
          ·
            refine ⟨1505514798060749026476577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8029412256323994807875077 1505514798060749026476577)
            ·
              refine ⟨1129136098545561769857433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505514798060749026476577 1129136098545561769857433)
              ·
                refine ⟨846852073909171327393075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129136098545561769857433 846852073909171327393075)
                ·
                  refine ⟨1270278110863756991089613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846852073909171327393075 1270278110863756991089613)
                  ·
                    refine ⟨476354291573908871658605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270278110863756991089613 476354291573908871658605)
                    ·
                      rfl

theorem cell22_1391545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_1391545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391545 prefixEnd_1391545 := by exact prefixLift 1391545
  have htrace : WordTrace (prefixWord ++ tailWord_1391545) baseStart_1391545 baseEnd_1391545 := by
    simpa [prefixWord, tailWord_1391545, baseEnd_1391545] using wordTrace_append hprefix tailTrace_1391545
  have hstable : (prefixWord ++ tailWord_1391545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391545).length < 2 ^ (prefixWord ++ tailWord_1391545).sum := by decide
  have hdescent : baseEnd_1391545 < baseStart_1391545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391601 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_1391601 : Nat := 118140960795 + 1391601 * 2 ^ 59
def prefixEnd_1391601 : Nat := 4983230072969 + 3 ^ 40 * 1391601 * 2
def baseEnd_1391601 : Nat := 476373461518343392258433

theorem tailTrace_1391601 : CollatzResearch.WordTrace tailWord_1391601 prefixEnd_1391601 476373461518343392258433 := by
  unfold tailWord_1391601
  simp only [CollatzResearch.WordTrace]
  refine ⟨50755858231474718374310657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33837238820983145582873771 50755858231474718374310657)
  ·
    refine ⟨38066893673606038780732993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50755858231474718374310657 38066893673606038780732993)
    ·
      refine ⟨28550170255204529085549745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38066893673606038780732993 28550170255204529085549745)
      ·
        refine ⟨21412627691403396814162309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28550170255204529085549745 21412627691403396814162309)
        ·
          refine ⟨4014867692138136902655433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21412627691403396814162309 4014867692138136902655433)
          ·
            refine ⟨3011150769103602676991575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4014867692138136902655433 3011150769103602676991575)
            ·
              refine ⟨4516726153655404015487363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011150769103602676991575 4516726153655404015487363)
              ·
                refine ⟨6775089230483106023231045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4516726153655404015487363 6775089230483106023231045)
                ·
                  refine ⟨1270329230715582379355821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6775089230483106023231045 1270329230715582379355821)
                  ·
                    refine ⟨476373461518343392258433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270329230715582379355821 476373461518343392258433)
                    ·
                      rfl

theorem cell22_1391601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_1391601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391601 prefixEnd_1391601 := by exact prefixLift 1391601
  have htrace : WordTrace (prefixWord ++ tailWord_1391601) baseStart_1391601 baseEnd_1391601 := by
    simpa [prefixWord, tailWord_1391601, baseEnd_1391601] using wordTrace_append hprefix tailTrace_1391601
  have hstable : (prefixWord ++ tailWord_1391601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391601).length < 2 ^ (prefixWord ++ tailWord_1391601).sum := by decide
  have hdescent : baseEnd_1391601 < baseStart_1391601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391648 : List Nat := [2, 1, 1, 7, 2, 1, 8]
def baseStart_1391648 : Nat := 118140960795 + 1391648 * 2 ^ 59
def prefixEnd_1391648 : Nat := 4983230072969 + 3 ^ 40 * 1391648 * 2
def baseEnd_1391648 : Nat := 17644057428846330975307

theorem tailTrace_1391648 : CollatzResearch.WordTrace tailWord_1391648 prefixEnd_1391648 17644057428846330975307 := by
  unfold tailWord_1391648
  simp only [CollatzResearch.WordTrace]
  refine ⟨25378786231152222700635799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33838381641536296934181065 25378786231152222700635799)
  ·
    refine ⟨38068179346728334050953699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25378786231152222700635799 38068179346728334050953699)
    ·
      refine ⟨57102269020092501076430549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38068179346728334050953699 57102269020092501076430549)
      ·
        refine ⟨1338334430158417993978841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 57102269020092501076430549 1338334430158417993978841)
        ·
          refine ⟨1003750822618813495484131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338334430158417993978841 1003750822618813495484131)
          ·
            refine ⟨1505626233928220243226197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003750822618813495484131 1505626233928220243226197)
            ·
              refine ⟨17644057428846330975307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1505626233928220243226197 17644057428846330975307)
              ·
                rfl

theorem cell22_1391648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 8].length) (baseStart_1391648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391648 prefixEnd_1391648 := by exact prefixLift 1391648
  have htrace : WordTrace (prefixWord ++ tailWord_1391648) baseStart_1391648 baseEnd_1391648 := by
    simpa [prefixWord, tailWord_1391648, baseEnd_1391648] using wordTrace_append hprefix tailTrace_1391648
  have hstable : (prefixWord ++ tailWord_1391648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391648).length < 2 ^ (prefixWord ++ tailWord_1391648).sum := by decide
  have hdescent : baseEnd_1391648 < baseStart_1391648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391659 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 5]
def baseStart_1391659 : Nat := 118140960795 + 1391659 * 2 ^ 59
def prefixEnd_1391659 : Nat := 4983230072969 + 3 ^ 40 * 1391659 * 2
def baseEnd_1391659 : Nat := 158797772034550191436085

theorem tailTrace_1391659 : CollatzResearch.WordTrace tailWord_1391659 prefixEnd_1391659 158797772034550191436085 := by
  unfold tailWord_1391659
  simp only [CollatzResearch.WordTrace]
  refine ⟨50757973665264594279922031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33838649110176396186614687 50757973665264594279922031)
  ·
    refine ⟨76136960497896891419883047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50757973665264594279922031 76136960497896891419883047)
    ·
      refine ⟨114205440746845337129824571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76136960497896891419883047 114205440746845337129824571)
      ·
        refine ⟨171308161120268005694736857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114205440746845337129824571 171308161120268005694736857)
        ·
          refine ⟨128481120840201004271052643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171308161120268005694736857 128481120840201004271052643)
          ·
            refine ⟨192721681260301506406578965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128481120840201004271052643 192721681260301506406578965)
            ·
              refine ⟨9033828809076633112808389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192721681260301506406578965 9033828809076633112808389)
              ·
                refine ⟨1693842901701868708651573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9033828809076633112808389 1693842901701868708651573)
                ·
                  refine ⟨158797772034550191436085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693842901701868708651573 158797772034550191436085)
                  ·
                    rfl

theorem cell22_1391659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 5].length) (baseStart_1391659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391659 prefixEnd_1391659 := by exact prefixLift 1391659
  have htrace : WordTrace (prefixWord ++ tailWord_1391659) baseStart_1391659 baseEnd_1391659 := by
    simpa [prefixWord, tailWord_1391659, baseEnd_1391659] using wordTrace_append hprefix tailTrace_1391659
  have hstable : (prefixWord ++ tailWord_1391659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391659).length < 2 ^ (prefixWord ++ tailWord_1391659).sum := by decide
  have hdescent : baseEnd_1391659 < baseStart_1391659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391674 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1391674 : Nat := 118140960795 + 1391674 * 2 ^ 59
def prefixEnd_1391674 : Nat := 4983230072969 + 3 ^ 40 * 1391674 * 2
def baseEnd_1391674 : Nat := 476398450910195535183209

theorem tailTrace_1391674 : CollatzResearch.WordTrace tailWord_1391674 prefixEnd_1391674 476398450910195535183209 := by
  unfold tailWord_1391674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12689630190052562960429519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33839013840140167894478717 12689630190052562960429519)
  ·
    refine ⟨19034445285078844440644279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12689630190052562960429519 19034445285078844440644279)
    ·
      refine ⟨28551667927618266660966419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19034445285078844440644279 28551667927618266660966419)
      ·
        refine ⟨42827501891427399991449629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28551667927618266660966419 42827501891427399991449629)
        ·
          refine ⟨16060313209285274996793611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42827501891427399991449629 16060313209285274996793611)
          ·
            refine ⟨24090469813927912495190417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16060313209285274996793611 24090469813927912495190417)
            ·
              refine ⟨18067852360445934371392813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24090469813927912495190417 18067852360445934371392813)
              ·
                refine ⟨6775444635167225389272305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18067852360445934371392813 6775444635167225389272305)
                ·
                  refine ⟨5081583476375419041954229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6775444635167225389272305 5081583476375419041954229)
                  ·
                    refine ⟨476398450910195535183209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5081583476375419041954229 476398450910195535183209)
                    ·
                      rfl

theorem cell22_1391674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1391674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391674 prefixEnd_1391674 := by exact prefixLift 1391674
  have htrace : WordTrace (prefixWord ++ tailWord_1391674) baseStart_1391674 baseEnd_1391674 := by
    simpa [prefixWord, tailWord_1391674, baseEnd_1391674] using wordTrace_append hprefix tailTrace_1391674
  have hstable : (prefixWord ++ tailWord_1391674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391674).length < 2 ^ (prefixWord ++ tailWord_1391674).sum := by decide
  have hdescent : baseEnd_1391674 < baseStart_1391674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391676 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_1391676 : Nat := 118140960795 + 1391676 * 2 ^ 59
def prefixEnd_1391676 : Nat := 4983230072969 + 3 ^ 40 * 1391676 * 2
def baseEnd_1391676 : Nat := 158799711850356065544401

theorem tailTrace_1391676 : CollatzResearch.WordTrace tailWord_1391676 prefixEnd_1391676 158799711850356065544401 := by
  unfold tailWord_1391676
  simp only [CollatzResearch.WordTrace]
  refine ⟨25379296853101503091645441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33839062470802004122193921 25379296853101503091645441)
  ·
    refine ⟨19034472639826127318734081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25379296853101503091645441 19034472639826127318734081)
    ·
      refine ⟨14275854479869595489050561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19034472639826127318734081 14275854479869595489050561)
      ·
        refine ⟨10706890859902196616787921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14275854479869595489050561 10706890859902196616787921)
        ·
          refine ⟨8030168144926647462590941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10706890859902196616787921 8030168144926647462590941)
          ·
            refine ⟨3011313054347492798471603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8030168144926647462590941 3011313054347492798471603)
            ·
              refine ⟨4516969581521239197707405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011313054347492798471603 4516969581521239197707405)
              ·
                refine ⟨1693863593070464699140277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4516969581521239197707405 1693863593070464699140277)
                ·
                  refine ⟨158799711850356065544401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693863593070464699140277 158799711850356065544401)
                  ·
                    rfl

theorem cell22_1391676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_1391676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391676 prefixEnd_1391676 := by exact prefixLift 1391676
  have htrace : WordTrace (prefixWord ++ tailWord_1391676) baseStart_1391676 baseEnd_1391676 := by
    simpa [prefixWord, tailWord_1391676, baseEnd_1391676] using wordTrace_append hprefix tailTrace_1391676
  have hstable : (prefixWord ++ tailWord_1391676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391676).length < 2 ^ (prefixWord ++ tailWord_1391676).sum := by decide
  have hdescent : baseEnd_1391676 < baseStart_1391676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391710 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1391710 : Nat := 118140960795 + 1391710 * 2 ^ 59
def prefixEnd_1391710 : Nat := 4983230072969 + 3 ^ 40 * 1391710 * 2
def baseEnd_1391710 : Nat := 158803591481967813761033

theorem tailTrace_1391710 : CollatzResearch.WordTrace tailWord_1391710 prefixEnd_1391710 158803591481967813761033 := by
  unfold tailWord_1391710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344979223509978748753573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33839889192053219993352389 6344979223509978748753573)
  ·
    refine ⟨1189683604408121015391295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6344979223509978748753573 1189683604408121015391295)
    ·
      refine ⟨1784525406612181523086943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189683604408121015391295 1784525406612181523086943)
      ·
        refine ⟨2676788109918272284630415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784525406612181523086943 2676788109918272284630415)
        ·
          refine ⟨4015182164877408426945623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676788109918272284630415 4015182164877408426945623)
          ·
            refine ⟨6022773247316112640418435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015182164877408426945623 6022773247316112640418435)
            ·
              refine ⟨9034159870974168960627653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022773247316112640418435 9034159870974168960627653)
              ·
                refine ⟨1693904975807656680117685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9034159870974168960627653 1693904975807656680117685)
                ·
                  refine ⟨158803591481967813761033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693904975807656680117685 158803591481967813761033)
                  ·
                    rfl

theorem cell22_1391710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1391710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391710 prefixEnd_1391710 := by exact prefixLift 1391710
  have htrace : WordTrace (prefixWord ++ tailWord_1391710) baseStart_1391710 baseEnd_1391710 := by
    simpa [prefixWord, tailWord_1391710, baseEnd_1391710] using wordTrace_append hprefix tailTrace_1391710
  have hstable : (prefixWord ++ tailWord_1391710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391710).length < 2 ^ (prefixWord ++ tailWord_1391710).sum := by decide
  have hdescent : baseEnd_1391710 < baseStart_1391710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391714 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1391714 : Nat := 118140960795 + 1391714 * 2 ^ 59
def prefixEnd_1391714 : Nat := 4983230072969 + 3 ^ 40 * 1391714 * 2
def baseEnd_1391714 : Nat := 476412143727648764183087

theorem tailTrace_1391714 : CollatzResearch.WordTrace tailWord_1391714 prefixEnd_1391714 476412143727648764183087 := by
  unfold tailWord_1391714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12689994920016334668293549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33839986453376892448782797 12689994920016334668293549)
  ·
    refine ⟨4758748095006125500610081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12689994920016334668293549 4758748095006125500610081)
    ·
      refine ⟨3569061071254594125457561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4758748095006125500610081 3569061071254594125457561)
      ·
        refine ⟨2676795803440945594093171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3569061071254594125457561 2676795803440945594093171)
        ·
          refine ⟨4015193705161418391139757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676795803440945594093171 4015193705161418391139757)
          ·
            refine ⟨1505697639435531896677409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4015193705161418391139757 1505697639435531896677409)
            ·
              refine ⟨1129273229576648922508057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505697639435531896677409 1129273229576648922508057)
              ·
                refine ⟨846954922182486691881043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129273229576648922508057 846954922182486691881043)
                ·
                  refine ⟨1270432383273730037821565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846954922182486691881043 1270432383273730037821565)
                  ·
                    refine ⟨476412143727648764183087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270432383273730037821565 476412143727648764183087)
                    ·
                      rfl

theorem cell22_1391714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1391714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391714 prefixEnd_1391714 := by exact prefixLift 1391714
  have htrace : WordTrace (prefixWord ++ tailWord_1391714) baseStart_1391714 baseEnd_1391714 := by
    simpa [prefixWord, tailWord_1391714, baseEnd_1391714] using wordTrace_append hprefix tailTrace_1391714
  have hstable : (prefixWord ++ tailWord_1391714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391714).length < 2 ^ (prefixWord ++ tailWord_1391714).sum := by decide
  have hdescent : baseEnd_1391714 < baseStart_1391714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391770 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_1391770 : Nat := 118140960795 + 1391770 * 2 ^ 59
def prefixEnd_1391770 : Nat := 4983230072969 + 3 ^ 40 * 1391770 * 2
def baseEnd_1391770 : Nat := 476431313672083284782915

theorem tailTrace_1391770 : CollatzResearch.WordTrace tailWord_1391770 prefixEnd_1391770 476431313672083284782915 := by
  unfold tailWord_1391770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690505541965615059303191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33841348111908306824808509 12690505541965615059303191)
  ·
    refine ⟨19035758312948422588954787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12690505541965615059303191 19035758312948422588954787)
    ·
      refine ⟨28553637469422633883432181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19035758312948422588954787 28553637469422633883432181)
      ·
        refine ⟨2676903512758371926571767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28553637469422633883432181 2676903512758371926571767)
        ·
          refine ⟨4015355269137557889857651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676903512758371926571767 4015355269137557889857651)
          ·
            refine ⟨6023032903706336834786477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015355269137557889857651 6023032903706336834786477)
            ·
              refine ⟨2258637338889876313044929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6023032903706336834786477 2258637338889876313044929)
              ·
                refine ⟨1693978004167407234783697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258637338889876313044929 1693978004167407234783697)
                ·
                  refine ⟨1270483503125555426087773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693978004167407234783697 1270483503125555426087773)
                  ·
                    refine ⟨476431313672083284782915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270483503125555426087773 476431313672083284782915)
                    ·
                      rfl

theorem cell22_1391770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_1391770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391770 prefixEnd_1391770 := by exact prefixLift 1391770
  have htrace : WordTrace (prefixWord ++ tailWord_1391770) baseStart_1391770 baseEnd_1391770 := by
    simpa [prefixWord, tailWord_1391770, baseEnd_1391770] using wordTrace_append hprefix tailTrace_1391770
  have hstable : (prefixWord ++ tailWord_1391770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391770).length < 2 ^ (prefixWord ++ tailWord_1391770).sum := by decide
  have hdescent : baseEnd_1391770 < baseStart_1391770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391779 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_1391779 : Nat := 118140960795 + 1391779 * 2 ^ 59
def prefixEnd_1391779 : Nat := 4983230072969 + 3 ^ 40 * 1391779 * 2
def baseEnd_1391779 : Nat := 476434394556010261307887

theorem tailTrace_1391779 : CollatzResearch.WordTrace tailWord_1391779 prefixEnd_1391779 476434394556010261307887 := by
  unfold tailWord_1391779
  simp only [CollatzResearch.WordTrace]
  refine ⟨50762350424829854774290391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33841566949886569849526927 50762350424829854774290391)
  ·
    refine ⟨76143525637244782161435587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50762350424829854774290391 76143525637244782161435587)
    ·
      refine ⟨114215288455867173242153381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76143525637244782161435587 114215288455867173242153381)
      ·
        refine ⟨21415366585475094982903759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114215288455867173242153381 21415366585475094982903759)
        ·
          refine ⟨32123049878212642474355639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21415366585475094982903759 32123049878212642474355639)
          ·
            refine ⟨48184574817318963711533459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32123049878212642474355639 48184574817318963711533459)
            ·
              refine ⟨72276862225978445567300189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48184574817318963711533459 72276862225978445567300189)
              ·
                refine ⟨27103823334741917087737571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72276862225978445567300189 27103823334741917087737571)
                ·
                  refine ⟨40655735002112875631606357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27103823334741917087737571 40655735002112875631606357)
                  ·
                    refine ⟨476434394556010261307887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40655735002112875631606357 476434394556010261307887)
                    ·
                      rfl

theorem cell22_1391779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_1391779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391779 prefixEnd_1391779 := by exact prefixLift 1391779
  have htrace : WordTrace (prefixWord ++ tailWord_1391779) baseStart_1391779 baseEnd_1391779 := by
    simpa [prefixWord, tailWord_1391779, baseEnd_1391779] using wordTrace_append hprefix tailTrace_1391779
  have hstable : (prefixWord ++ tailWord_1391779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391779).length < 2 ^ (prefixWord ++ tailWord_1391779).sum := by decide
  have hdescent : baseEnd_1391779 < baseStart_1391779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391832 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 3, 3]
def baseStart_1391832 : Nat := 118140960795 + 1391832 * 2 ^ 59
def prefixEnd_1391832 : Nat := 4983230072969 + 3 ^ 40 * 1391832 * 2
def baseEnd_1391832 : Nat := 476452537539135789732725

theorem tailTrace_1391832 : CollatzResearch.WordTrace tailWord_1391832 prefixEnd_1391832 476452537539135789732725 := by
  unfold tailWord_1391832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25382141746818922412984875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33842855662425229883979833 25382141746818922412984875)
  ·
    refine ⟨38073212620228383619477313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25382141746818922412984875 38073212620228383619477313)
    ·
      refine ⟨28554909465171287714607985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38073212620228383619477313 28554909465171287714607985)
      ·
        refine ⟨21416182098878465785955989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28554909465171287714607985 21416182098878465785955989)
        ·
          refine ⟨1003883535884928083716687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21416182098878465785955989 1003883535884928083716687)
          ·
            refine ⟨1505825303827392125575031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003883535884928083716687 1505825303827392125575031)
            ·
              refine ⟨2258737955741088188362547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505825303827392125575031 2258737955741088188362547)
              ·
                refine ⟨3388106933611632282543821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258737955741088188362547 3388106933611632282543821)
                ·
                  refine ⟨1270540100104362105953933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3388106933611632282543821 1270540100104362105953933)
                  ·
                    refine ⟨476452537539135789732725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270540100104362105953933 476452537539135789732725)
                    ·
                      rfl

theorem cell22_1391832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_1391832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391832 prefixEnd_1391832 := by exact prefixLift 1391832
  have htrace : WordTrace (prefixWord ++ tailWord_1391832) baseStart_1391832 baseEnd_1391832 := by
    simpa [prefixWord, tailWord_1391832, baseEnd_1391832] using wordTrace_append hprefix tailTrace_1391832
  have hstable : (prefixWord ++ tailWord_1391832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391832).length < 2 ^ (prefixWord ++ tailWord_1391832).sum := by decide
  have hdescent : baseEnd_1391832 < baseStart_1391832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391871 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_1391871 : Nat := 118140960795 + 1391871 * 2 ^ 59
def prefixEnd_1391871 : Nat := 4983230072969 + 3 ^ 40 * 1391871 * 2
def baseEnd_1391871 : Nat := 476465888036152688007605

theorem tailTrace_1391871 : CollatzResearch.WordTrace tailWord_1391871 prefixEnd_1391871 476465888036152688007605 := by
  unfold tailWord_1391871
  simp only [CollatzResearch.WordTrace]
  refine ⟨50765705940496554486639467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33843803960331036324426311 50765705940496554486639467)
  ·
    refine ⟨76148558910744831729959201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50765705940496554486639467 76148558910744831729959201)
    ·
      refine ⟨57111419183058623797469401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76148558910744831729959201 57111419183058623797469401)
      ·
        refine ⟨42833564387293967848102051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57111419183058623797469401 42833564387293967848102051)
        ·
          refine ⟨64250346580940951772153077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42833564387293967848102051 64250346580940951772153077)
          ·
            refine ⟨6023469991963214228639351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64250346580940951772153077 6023469991963214228639351)
            ·
              refine ⟨9035204987944821342959027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023469991963214228639351 9035204987944821342959027)
              ·
                refine ⟨13552807481917232014438541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9035204987944821342959027 13552807481917232014438541)
                ·
                  refine ⟨5082302805718962005414453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13552807481917232014438541 5082302805718962005414453)
                  ·
                    refine ⟨476465888036152688007605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5082302805718962005414453 476465888036152688007605)
                    ·
                      rfl

theorem cell22_1391871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_1391871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391871 prefixEnd_1391871 := by exact prefixLift 1391871
  have htrace : WordTrace (prefixWord ++ tailWord_1391871) baseStart_1391871 baseEnd_1391871 := by
    simpa [prefixWord, tailWord_1391871, baseEnd_1391871] using wordTrace_append hprefix tailTrace_1391871
  have hstable : (prefixWord ++ tailWord_1391871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391871).length < 2 ^ (prefixWord ++ tailWord_1391871).sum := by decide
  have hdescent : baseEnd_1391871 < baseStart_1391871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391875 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 1, 4]
def baseStart_1391875 : Nat := 118140960795 + 1391875 * 2 ^ 59
def prefixEnd_1391875 : Nat := 4983230072969 + 3 ^ 40 * 1391875 * 2
def baseEnd_1391875 : Nat := 476467257317898010907593

theorem tailTrace_1391875 : CollatzResearch.WordTrace tailWord_1391875 prefixEnd_1391875 476467257317898010907593 := by
  unfold tailWord_1391875
  simp only [CollatzResearch.WordTrace]
  refine ⟨50765851832482063169785079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33843901221654708779856719 50765851832482063169785079)
  ·
    refine ⟨76148777748723094754677619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50765851832482063169785079 76148777748723094754677619)
    ·
      refine ⟨114223166623084642132016429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76148777748723094754677619 114223166623084642132016429)
      ·
        refine ⟨42833687483656740799506161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114223166623084642132016429 42833687483656740799506161)
        ·
          refine ⟨32125265612742555599629621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42833687483656740799506161 32125265612742555599629621)
          ·
            refine ⟨3011743651194614587465277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32125265612742555599629621 3011743651194614587465277)
            ·
              refine ⟨1129403869197980470299479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3011743651194614587465277 1129403869197980470299479)
              ·
                refine ⟨1694105803796970705449219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129403869197980470299479 1694105803796970705449219)
                ·
                  refine ⟨2541158705695456058173829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694105803796970705449219 2541158705695456058173829)
                  ·
                    refine ⟨476467257317898010907593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541158705695456058173829 476467257317898010907593)
                    ·
                      rfl

theorem cell22_1391875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 4].length) (baseStart_1391875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391875 prefixEnd_1391875 := by exact prefixLift 1391875
  have htrace : WordTrace (prefixWord ++ tailWord_1391875) baseStart_1391875 baseEnd_1391875 := by
    simpa [prefixWord, tailWord_1391875, baseEnd_1391875] using wordTrace_append hprefix tailTrace_1391875
  have hstable : (prefixWord ++ tailWord_1391875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391875).length < 2 ^ (prefixWord ++ tailWord_1391875).sum := by decide
  have hdescent : baseEnd_1391875 < baseStart_1391875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391926 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1391926 : Nat := 118140960795 + 1391926 * 2 ^ 59
def prefixEnd_1391926 : Nat := 4983230072969 + 3 ^ 40 * 1391926 * 2
def baseEnd_1391926 : Nat := 476484715660150877882437

theorem tailTrace_1391926 : CollatzResearch.WordTrace tailWord_1391926 prefixEnd_1391926 476484715660150877882437 := by
  unfold tailWord_1391926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172981997206081179993227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33845141303531532586594421 3172981997206081179993227)
  ·
    refine ⟨4759472995809121769989841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3172981997206081179993227 4759472995809121769989841)
    ·
      refine ⟨3569604746856841327492381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4759472995809121769989841 3569604746856841327492381)
      ·
        refine ⟨1338601780071315497809643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3569604746856841327492381 1338601780071315497809643)
        ·
          refine ⟨2007902670106973246714465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1338601780071315497809643 2007902670106973246714465)
          ·
            refine ⟨1505927002580229935035849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2007902670106973246714465 1505927002580229935035849)
            ·
              refine ⟨1129445251935172451276887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505927002580229935035849 1129445251935172451276887)
              ·
                refine ⟨1694167877902758676915331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129445251935172451276887 1694167877902758676915331)
                ·
                  refine ⟨2541251816854138015372997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694167877902758676915331 2541251816854138015372997)
                  ·
                    refine ⟨476484715660150877882437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541251816854138015372997 476484715660150877882437)
                    ·
                      rfl

theorem cell22_1391926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1391926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391926 prefixEnd_1391926 := by exact prefixLift 1391926
  have htrace : WordTrace (prefixWord ++ tailWord_1391926) baseStart_1391926 baseEnd_1391926 := by
    simpa [prefixWord, tailWord_1391926, baseEnd_1391926] using wordTrace_append hprefix tailTrace_1391926
  have hstable : (prefixWord ++ tailWord_1391926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391926).length < 2 ^ (prefixWord ++ tailWord_1391926).sum := by decide
  have hdescent : baseEnd_1391926 < baseStart_1391926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391950 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1391950 : Nat := 118140960795 + 1391950 * 2 ^ 59
def prefixEnd_1391950 : Nat := 4983230072969 + 3 ^ 40 * 1391950 * 2
def baseEnd_1391950 : Nat := 476492931350622815282363

theorem tailTrace_1391950 : CollatzResearch.WordTrace tailWord_1391950 prefixEnd_1391950 476492931350622815282363 := by
  unfold tailWord_1391950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6346073413401293872345663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33845724871473567319176869 6346073413401293872345663)
  ·
    refine ⟨9519110120101940808518495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6346073413401293872345663 9519110120101940808518495)
    ·
      refine ⟨14278665180152911212777743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9519110120101940808518495 14278665180152911212777743)
      ·
        refine ⟨21417997770229366819166615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14278665180152911212777743 21417997770229366819166615)
        ·
          refine ⟨32126996655344050228749923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21417997770229366819166615 32126996655344050228749923)
          ·
            refine ⟨48190494983016075343124885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32126996655344050228749923 48190494983016075343124885)
            ·
              refine ⟨2258929452328878531708979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48190494983016075343124885 2258929452328878531708979)
              ·
                refine ⟨3388394178493317797563469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258929452328878531708979 3388394178493317797563469)
                ·
                  refine ⟨1270647816934994174086301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3388394178493317797563469 1270647816934994174086301)
                  ·
                    refine ⟨476492931350622815282363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270647816934994174086301 476492931350622815282363)
                    ·
                      rfl

theorem cell22_1391950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1391950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1391950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1391950 prefixEnd_1391950 := by exact prefixLift 1391950
  have htrace : WordTrace (prefixWord ++ tailWord_1391950) baseStart_1391950 baseEnd_1391950 := by
    simpa [prefixWord, tailWord_1391950, baseEnd_1391950] using wordTrace_append hprefix tailTrace_1391950
  have hstable : (prefixWord ++ tailWord_1391950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391950).length < 2 ^ (prefixWord ++ tailWord_1391950).sum := by decide
  have hdescent : baseEnd_1391950 < baseStart_1391950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392001 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1392001 : Nat := 118140960795 + 1392001 * 2 ^ 59
def prefixEnd_1392001 : Nat := 4983230072969 + 3 ^ 40 * 1392001 * 2
def baseEnd_1392001 : Nat := 476510389692875682257207

theorem tailTrace_1392001 : CollatzResearch.WordTrace tailWord_1392001 prefixEnd_1392001 476510389692875682257207 := by
  unfold tailWord_1392001
  simp only [CollatzResearch.WordTrace]
  refine ⟨50770447430025586688871857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33846964953350391125914571 50770447430025586688871857)
  ·
    refine ⟨38077835572519190016653893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50770447430025586688871857 38077835572519190016653893)
    ·
      refine ⟨7139594169847348128122605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38077835572519190016653893 7139594169847348128122605)
      ·
        refine ⟨2677347813692755548045977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7139594169847348128122605 2677347813692755548045977)
        ·
          refine ⟨2008010860269566661034483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677347813692755548045977 2008010860269566661034483)
          ·
            refine ⟨3012016290404349991551725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008010860269566661034483 3012016290404349991551725)
            ·
              refine ⟨1129506108901631246831897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3012016290404349991551725 1129506108901631246831897)
              ·
                refine ⟨847129581676223435123923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129506108901631246831897 847129581676223435123923)
                ·
                  refine ⟨1270694372514335152685885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847129581676223435123923 1270694372514335152685885)
                  ·
                    refine ⟨476510389692875682257207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270694372514335152685885 476510389692875682257207)
                    ·
                      rfl

theorem cell22_1392001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1392001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392001 prefixEnd_1392001 := by exact prefixLift 1392001
  have htrace : WordTrace (prefixWord ++ tailWord_1392001) baseStart_1392001 baseEnd_1392001 := by
    simpa [prefixWord, tailWord_1392001, baseEnd_1392001] using wordTrace_append hprefix tailTrace_1392001
  have hstable : (prefixWord ++ tailWord_1392001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392001).length < 2 ^ (prefixWord ++ tailWord_1392001).sum := by decide
  have hdescent : baseEnd_1392001 < baseStart_1392001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392014 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_1392014 : Nat := 118140960795 + 1392014 * 2 ^ 59
def prefixEnd_1392014 : Nat := 4983230072969 + 3 ^ 40 * 1392014 * 2
def baseEnd_1392014 : Nat := 158838279952849327227389

theorem tailTrace_1392014 : CollatzResearch.WordTrace tailWord_1392014 prefixEnd_1392014 158838279952849327227389 := by
  unfold tailWord_1392014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6346365197372311238636887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33847281052652326606063397 6346365197372311238636887)
  ·
    refine ⟨9519547796058466857955331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6346365197372311238636887 9519547796058466857955331)
    ·
      refine ⟨14279321694087700286932997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9519547796058466857955331 14279321694087700286932997)
      ·
        refine ⟨2677372817641443803799937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14279321694087700286932997 2677372817641443803799937)
        ·
          refine ⟨2008029613231082852849953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677372817641443803799937 2008029613231082852849953)
          ·
            refine ⟨1506022209923312139637465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2008029613231082852849953 1506022209923312139637465)
            ·
              refine ⟨1129516657442484104728099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506022209923312139637465 1129516657442484104728099)
              ·
                refine ⟨1694274986163726157092149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129516657442484104728099 1694274986163726157092149)
                ·
                  refine ⟨158838279952849327227389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694274986163726157092149 158838279952849327227389)
                  ·
                    rfl

theorem cell22_1392014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_1392014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392014 prefixEnd_1392014 := by exact prefixLift 1392014
  have htrace : WordTrace (prefixWord ++ tailWord_1392014) baseStart_1392014 baseEnd_1392014 := by
    simpa [prefixWord, tailWord_1392014, baseEnd_1392014] using wordTrace_append hprefix tailTrace_1392014
  have hstable : (prefixWord ++ tailWord_1392014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392014).length < 2 ^ (prefixWord ++ tailWord_1392014).sum := by decide
  have hdescent : baseEnd_1392014 < baseStart_1392014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392023 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 1, 5]
def baseStart_1392023 : Nat := 118140960795 + 1392023 * 2 ^ 59
def prefixEnd_1392023 : Nat := 4983230072969 + 3 ^ 40 * 1392023 * 2
def baseEnd_1392023 : Nat := 476517920742474958207139

theorem tailTrace_1392023 : CollatzResearch.WordTrace tailWord_1392023 prefixEnd_1392023 476517920742474958207139 := by
  unfold tailWord_1392023
  simp only [CollatzResearch.WordTrace]
  refine ⟨50771249835945884446172723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33847499890630589630781815 50771249835945884446172723)
  ·
    refine ⟨76156874753918826669259085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50771249835945884446172723 76156874753918826669259085)
    ·
      refine ⟨28558828032719560000972157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76156874753918826669259085 28558828032719560000972157)
      ·
        refine ⟨10709560512269835000364559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28558828032719560000972157 10709560512269835000364559)
        ·
          refine ⟨16064340768404752500546839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10709560512269835000364559 16064340768404752500546839)
          ·
            refine ⟨24096511152607128750820259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16064340768404752500546839 24096511152607128750820259)
            ·
              refine ⟨36144766728910693126230389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24096511152607128750820259 36144766728910693126230389)
              ·
                refine ⟨3388571880835377480584099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36144766728910693126230389 3388571880835377480584099)
                ·
                  refine ⟨5082857821253066220876149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388571880835377480584099 5082857821253066220876149)
                  ·
                    refine ⟨476517920742474958207139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5082857821253066220876149 476517920742474958207139)
                    ·
                      rfl

theorem cell22_1392023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_1392023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392023 prefixEnd_1392023 := by exact prefixLift 1392023
  have htrace : WordTrace (prefixWord ++ tailWord_1392023) baseStart_1392023 baseEnd_1392023 := by
    simpa [prefixWord, tailWord_1392023, baseEnd_1392023] using wordTrace_append hprefix tailTrace_1392023
  have hstable : (prefixWord ++ tailWord_1392023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392023).length < 2 ^ (prefixWord ++ tailWord_1392023).sum := by decide
  have hdescent : baseEnd_1392023 < baseStart_1392023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392053 : List Nat := [1, 3, 3, 2, 2, 11]
def baseStart_1392053 : Nat := 118140960795 + 1392053 * 2 ^ 59
def prefixEnd_1392053 : Nat := 4983230072969 + 3 ^ 40 * 1392053 * 2
def baseEnd_1392053 : Nat := 5883064078463763950087

theorem tailTrace_1392053 : CollatzResearch.WordTrace tailWord_1392053 prefixEnd_1392053 5883064078463763950087 := by
  unfold tailWord_1392053
  simp only [CollatzResearch.WordTrace]
  refine ⟨50772344025837199569764813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33848229350558133046509875 50772344025837199569764813)
  ·
    refine ⟨19039629009688949838661805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50772344025837199569764813 19039629009688949838661805)
    ·
      refine ⟨7139860878633356189498177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19039629009688949838661805 7139860878633356189498177)
      ·
        refine ⟨5354895658975017142123633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7139860878633356189498177 5354895658975017142123633)
        ·
          refine ⟨4016171744231262856592725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5354895658975017142123633 4016171744231262856592725)
          ·
            refine ⟨5883064078463763950087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4016171744231262856592725 5883064078463763950087)
            ·
              rfl

theorem cell22_1392053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 11].length) (baseStart_1392053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392053 prefixEnd_1392053 := by exact prefixLift 1392053
  have htrace : WordTrace (prefixWord ++ tailWord_1392053) baseStart_1392053 baseEnd_1392053 := by
    simpa [prefixWord, tailWord_1392053, baseEnd_1392053] using wordTrace_append hprefix tailTrace_1392053
  have hstable : (prefixWord ++ tailWord_1392053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392053).length < 2 ^ (prefixWord ++ tailWord_1392053).sum := by decide
  have hdescent : baseEnd_1392053 < baseStart_1392053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392162 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1392162 : Nat := 118140960795 + 1392162 * 2 ^ 59
def prefixEnd_1392162 : Nat := 4983230072969 + 3 ^ 40 * 1392162 * 2
def baseEnd_1392162 : Nat := 476565503283124928981713

theorem tailTrace_1392162 : CollatzResearch.WordTrace tailWord_1392162 prefixEnd_1392162 476565503283124928981713 := by
  unfold tailWord_1392162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12694079895610577796370685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33850879721628207456988493 12694079895610577796370685)
  ·
    refine ⟨4760279960853966673639007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12694079895610577796370685 4760279960853966673639007)
    ·
      refine ⟨7140419941280950010458511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760279960853966673639007 7140419941280950010458511)
      ·
        refine ⟨10710629911921425015687767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7140419941280950010458511 10710629911921425015687767)
        ·
          refine ⟨16065944867882137523531651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710629911921425015687767 16065944867882137523531651)
          ·
            refine ⟨24098917301823206285297477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16065944867882137523531651 24098917301823206285297477)
            ·
              refine ⟨4518546994091851178493277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24098917301823206285297477 4518546994091851178493277)
              ·
                refine ⟨1694455122784444191934979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4518546994091851178493277 1694455122784444191934979)
                ·
                  refine ⟨2541682684176666287902469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694455122784444191934979 2541682684176666287902469)
                  ·
                    refine ⟨476565503283124928981713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541682684176666287902469 476565503283124928981713)
                    ·
                      rfl

theorem cell22_1392162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1392162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392162 prefixEnd_1392162 := by exact prefixLift 1392162
  have htrace : WordTrace (prefixWord ++ tailWord_1392162) baseStart_1392162 baseEnd_1392162 := by
    simpa [prefixWord, tailWord_1392162, baseEnd_1392162] using wordTrace_append hprefix tailTrace_1392162
  have hstable : (prefixWord ++ tailWord_1392162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392162).length < 2 ^ (prefixWord ++ tailWord_1392162).sum := by decide
  have hdescent : baseEnd_1392162 < baseStart_1392162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392222 : List Nat := [4, 4, 1, 13]
def baseStart_1392222 : Nat := 118140960795 + 1392222 * 2 ^ 59
def prefixEnd_1392222 : Nat := 4983230072969 + 3 ^ 40 * 1392222 * 2
def baseEnd_1392222 : Nat := 653753144731556615201

theorem tailTrace_1392222 : CollatzResearch.WordTrace tailWord_1392222 prefixEnd_1392222 653753144731556615201 := by
  unfold tailWord_1392222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347313495278117679083365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33852338641483294288444613 6347313495278117679083365)
  ·
    refine ⟨1190121280364647064828131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6347313495278117679083365 1190121280364647064828131)
    ·
      refine ⟨1785181920546970597242197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190121280364647064828131 1785181920546970597242197)
      ·
        refine ⟨653753144731556615201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1785181920546970597242197 653753144731556615201)
        ·
          rfl

theorem cell22_1392222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 13].length) (baseStart_1392222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392222 prefixEnd_1392222 := by exact prefixLift 1392222
  have htrace : WordTrace (prefixWord ++ tailWord_1392222) baseStart_1392222 baseEnd_1392222 := by
    simpa [prefixWord, tailWord_1392222, baseEnd_1392222] using wordTrace_append hprefix tailTrace_1392222
  have hstable : (prefixWord ++ tailWord_1392222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392222).length < 2 ^ (prefixWord ++ tailWord_1392222).sum := by decide
  have hdescent : baseEnd_1392222 < baseStart_1392222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392314 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_1392314 : Nat := 118140960795 + 1392314 * 2 ^ 59
def prefixEnd_1392314 : Nat := 4983230072969 + 3 ^ 40 * 1392314 * 2
def baseEnd_1392314 : Nat := 476617535989447199181247

theorem tailTrace_1392314 : CollatzResearch.WordTrace tailWord_1392314 prefixEnd_1392314 476617535989447199181247 := by
  unfold tailWord_1392314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12695465869472910286253999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33854575651927760763343997 12695465869472910286253999)
  ·
    refine ⟨19043198804209365429380999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12695465869472910286253999 19043198804209365429380999)
    ·
      refine ⟨28564798206314048144071499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19043198804209365429380999 28564798206314048144071499)
      ·
        refine ⟨42847197309471072216107249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28564798206314048144071499 42847197309471072216107249)
        ·
          refine ⟨32135397982103304162080437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42847197309471072216107249 32135397982103304162080437)
          ·
            refine ⟨3012693560822184765195041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32135397982103304162080437 3012693560822184765195041)
            ·
              refine ⟨2259520170616638573896281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012693560822184765195041 2259520170616638573896281)
              ·
                refine ⟨1694640127962478930422211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259520170616638573896281 1694640127962478930422211)
                ·
                  refine ⟨2541960191943718395633317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694640127962478930422211 2541960191943718395633317)
                  ·
                    refine ⟨476617535989447199181247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541960191943718395633317 476617535989447199181247)
                    ·
                      rfl

theorem cell22_1392314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_1392314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392314 prefixEnd_1392314 := by exact prefixLift 1392314
  have htrace : WordTrace (prefixWord ++ tailWord_1392314) baseStart_1392314 baseEnd_1392314 := by
    simpa [prefixWord, tailWord_1392314, baseEnd_1392314] using wordTrace_append hprefix tailTrace_1392314
  have hstable : (prefixWord ++ tailWord_1392314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392314).length < 2 ^ (prefixWord ++ tailWord_1392314).sum := by decide
  have hdescent : baseEnd_1392314 < baseStart_1392314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392327 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 6, 3]
def baseStart_1392327 : Nat := 118140960795 + 1392327 * 2 ^ 59
def prefixEnd_1392327 : Nat := 4983230072969 + 3 ^ 40 * 1392327 * 2
def baseEnd_1392327 : Nat := 476621986155119498606207

theorem tailTrace_1392327 : CollatzResearch.WordTrace tailWord_1392327 prefixEnd_1392327 476621986155119498606207 := by
  unfold tailWord_1392327
  simp only [CollatzResearch.WordTrace]
  refine ⟨50782337626844544365239235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33854891751229696243492823 50782337626844544365239235)
  ·
    refine ⟨76173506440266816547858853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50782337626844544365239235 76173506440266816547858853)
    ·
      refine ⟨14282532457550028102723535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76173506440266816547858853 14282532457550028102723535)
      ·
        refine ⟨21423798686325042154085303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14282532457550028102723535 21423798686325042154085303)
        ·
          refine ⟨32135698029487563231127955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21423798686325042154085303 32135698029487563231127955)
          ·
            refine ⟨48203547044231344846691933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32135698029487563231127955 48203547044231344846691933)
            ·
              refine ⟨18076330141586754317509475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48203547044231344846691933 18076330141586754317509475)
              ·
                refine ⟨27114495212380131476264213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18076330141586754317509475 27114495212380131476264213)
                ·
                  refine ⟨1270991963080318662949885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27114495212380131476264213 1270991963080318662949885)
                  ·
                    refine ⟨476621986155119498606207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1270991963080318662949885 476621986155119498606207)
                    ·
                      rfl

theorem cell22_1392327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_1392327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392327 prefixEnd_1392327 := by exact prefixLift 1392327
  have htrace : WordTrace (prefixWord ++ tailWord_1392327) baseStart_1392327 baseEnd_1392327 := by
    simpa [prefixWord, tailWord_1392327, baseEnd_1392327] using wordTrace_append hprefix tailTrace_1392327
  have hstable : (prefixWord ++ tailWord_1392327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392327).length < 2 ^ (prefixWord ++ tailWord_1392327).sum := by decide
  have hdescent : baseEnd_1392327 < baseStart_1392327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392344 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1392344 : Nat := 118140960795 + 1392344 * 2 ^ 59
def prefixEnd_1392344 : Nat := 4983230072969 + 3 ^ 40 * 1392344 * 2
def baseEnd_1392344 : Nat := 476627805602537120931155

theorem tailTrace_1392344 : CollatzResearch.WordTrace tailWord_1392344 prefixEnd_1392344 476627805602537120931155 := by
  unfold tailWord_1392344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25391478833891478134304043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33855305111855304179072057 25391478833891478134304043)
  ·
    refine ⟨38087218250837217201456065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25391478833891478134304043 38087218250837217201456065)
    ·
      refine ⟨28565413688127912901092049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38087218250837217201456065 28565413688127912901092049)
      ·
        refine ⟨21424060266095934675819037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28565413688127912901092049 21424060266095934675819037)
        ·
          refine ⟨8034022599785975503432139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21424060266095934675819037 8034022599785975503432139)
          ·
            refine ⟨12051033899678963255148209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8034022599785975503432139 12051033899678963255148209)
            ·
              refine ⟨9038275424759222441361157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12051033899678963255148209 9038275424759222441361157)
              ·
                refine ⟨1694676642142354207755217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9038275424759222441361157 1694676642142354207755217)
                ·
                  refine ⟨1271007481606765655816413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1694676642142354207755217 1271007481606765655816413)
                  ·
                    refine ⟨476627805602537120931155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271007481606765655816413 476627805602537120931155)
                    ·
                      rfl

theorem cell22_1392344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1392344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392344 prefixEnd_1392344 := by exact prefixLift 1392344
  have htrace : WordTrace (prefixWord ++ tailWord_1392344) baseStart_1392344 baseEnd_1392344 := by
    simpa [prefixWord, tailWord_1392344, baseEnd_1392344] using wordTrace_append hprefix tailTrace_1392344
  have hstable : (prefixWord ++ tailWord_1392344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392344).length < 2 ^ (prefixWord ++ tailWord_1392344).sum := by decide
  have hdescent : baseEnd_1392344 < baseStart_1392344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392346 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_1392346 : Nat := 118140960795 + 1392346 * 2 ^ 59
def prefixEnd_1392346 : Nat := 4983230072969 + 3 ^ 40 * 1392346 * 2
def baseEnd_1392346 : Nat := 158876163414469927460383

theorem tailTrace_1392346 : CollatzResearch.WordTrace tailWord_1392346 prefixEnd_1392346 158876163414469927460383 := by
  unfold tailWord_1392346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12695757653443927652545223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33855353742517140406787261 12695757653443927652545223)
  ·
    refine ⟨19043636480165891478817835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12695757653443927652545223 19043636480165891478817835)
    ·
      refine ⟨28565454720248837218226753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19043636480165891478817835 28565454720248837218226753)
      ·
        refine ⟨21424091040186627913670065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28565454720248837218226753 21424091040186627913670065)
        ·
          refine ⟨16068068280139970935252549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21424091040186627913670065 16068068280139970935252549)
          ·
            refine ⟨3012762802526244550359853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16068068280139970935252549 3012762802526244550359853)
            ·
              refine ⟨1129786050947341706384945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3012762802526244550359853 1129786050947341706384945)
              ·
                refine ⟨847339538210506279788709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129786050947341706384945 847339538210506279788709)
                ·
                  refine ⟨158876163414469927460383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 847339538210506279788709 158876163414469927460383)
                  ·
                    rfl

theorem cell22_1392346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_1392346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392346 prefixEnd_1392346 := by exact prefixLift 1392346
  have htrace : WordTrace (prefixWord ++ tailWord_1392346) baseStart_1392346 baseEnd_1392346 := by
    simpa [prefixWord, tailWord_1392346, baseEnd_1392346] using wordTrace_append hprefix tailTrace_1392346
  have hstable : (prefixWord ++ tailWord_1392346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392346).length < 2 ^ (prefixWord ++ tailWord_1392346).sum := by decide
  have hdescent : baseEnd_1392346 < baseStart_1392346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392357 : List Nat := [1, 3, 1, 4, 1, 1, 4, 7]
def baseStart_1392357 : Nat := 118140960795 + 1392357 * 2 ^ 59
def prefixEnd_1392357 : Nat := 4983230072969 + 3 ^ 40 * 1392357 * 2
def baseEnd_1392357 : Nat := 52959139529801046706235

theorem tailTrace_1392357 : CollatzResearch.WordTrace tailWord_1392357 prefixEnd_1392357 52959139529801046706235 := by
  unfold tailWord_1392357
  simp only [CollatzResearch.WordTrace]
  refine ⟨50783431816735859488831325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33855621211157239659220883 50783431816735859488831325)
  ·
    refine ⟨19043786931275947308311747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50783431816735859488831325 19043786931275947308311747)
    ·
      refine ⟨28565680396913920962467621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19043786931275947308311747 28565680396913920962467621)
      ·
        refine ⟨5356065074421360180462679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28565680396913920962467621 5356065074421360180462679)
        ·
          refine ⟨8034097611632040270694019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5356065074421360180462679 8034097611632040270694019)
          ·
            refine ⟨12051146417448060406041029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8034097611632040270694019 12051146417448060406041029)
            ·
              refine ⟨2259589953271511326132693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12051146417448060406041029 2259589953271511326132693)
              ·
                refine ⟨52959139529801046706235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2259589953271511326132693 52959139529801046706235)
                ·
                  rfl

theorem cell22_1392357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 7].length) (baseStart_1392357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392357 prefixEnd_1392357 := by exact prefixLift 1392357
  have htrace : WordTrace (prefixWord ++ tailWord_1392357) baseStart_1392357 baseEnd_1392357 := by
    simpa [prefixWord, tailWord_1392357, baseEnd_1392357] using wordTrace_append hprefix tailTrace_1392357
  have hstable : (prefixWord ++ tailWord_1392357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392357).length < 2 ^ (prefixWord ++ tailWord_1392357).sum := by decide
  have hdescent : baseEnd_1392357 < baseStart_1392357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392397 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1392397 : Nat := 118140960795 + 1392397 * 2 ^ 59
def prefixEnd_1392397 : Nat := 4983230072969 + 3 ^ 40 * 1392397 * 2
def baseEnd_1392397 : Nat := 158881982861887549785331

theorem tailTrace_1392397 : CollatzResearch.WordTrace tailWord_1392397 prefixEnd_1392397 158881982861887549785331 := by
  unfold tailWord_1392397
  simp only [CollatzResearch.WordTrace]
  refine ⟨50784890736590946320287445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33856593824393964213524963 50784890736590946320287445)
  ·
    refine ⟨1190270876638850304381737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50784890736590946320287445 1190270876638850304381737)
    ·
      refine ⟨892703157479137728286303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190270876638850304381737 892703157479137728286303)
      ·
        refine ⟨1339054736218706592429455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892703157479137728286303 1339054736218706592429455)
        ·
          refine ⟨2008582104328059888644183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339054736218706592429455 2008582104328059888644183)
          ·
            refine ⟨3012873156492089832966275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008582104328059888644183 3012873156492089832966275)
            ·
              refine ⟨4519309734738134749449413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012873156492089832966275 4519309734738134749449413)
              ·
                refine ⟨847370575263400265521765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4519309734738134749449413 847370575263400265521765)
                ·
                  refine ⟨158881982861887549785331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 847370575263400265521765 158881982861887549785331)
                  ·
                    rfl

theorem cell22_1392397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1392397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392397 prefixEnd_1392397 := by exact prefixLift 1392397
  have htrace : WordTrace (prefixWord ++ tailWord_1392397) baseStart_1392397 baseEnd_1392397 := by
    simpa [prefixWord, tailWord_1392397, baseEnd_1392397] using wordTrace_append hprefix tailTrace_1392397
  have hstable : (prefixWord ++ tailWord_1392397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392397).length < 2 ^ (prefixWord ++ tailWord_1392397).sum := by decide
  have hdescent : baseEnd_1392397 < baseStart_1392397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392417 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1392417 : Nat := 118140960795 + 1392417 * 2 ^ 59
def prefixEnd_1392417 : Nat := 4983230072969 + 3 ^ 40 * 1392417 * 2
def baseEnd_1392417 : Nat := 476652794994389263855931

theorem tailTrace_1392417 : CollatzResearch.WordTrace tailWord_1392417 prefixEnd_1392417 476652794994389263855931 := by
  unfold tailWord_1392417
  simp only [CollatzResearch.WordTrace]
  refine ⟨50785620196518489736015505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33857080131012326490677003 50785620196518489736015505)
  ·
    refine ⟨38089215147388867302011629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50785620196518489736015505 38089215147388867302011629)
    ·
      refine ⟨14283455680270825238254361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38089215147388867302011629 14283455680270825238254361)
      ·
        refine ⟨10712591760203118928690771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14283455680270825238254361 10712591760203118928690771)
        ·
          refine ⟨16068887640304678393036157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10712591760203118928690771 16068887640304678393036157)
          ·
            refine ⟨6025832865114254397388559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16068887640304678393036157 6025832865114254397388559)
            ·
              refine ⟨9038749297671381596082839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6025832865114254397388559 9038749297671381596082839)
              ·
                refine ⟨13558123946507072394124259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9038749297671381596082839 13558123946507072394124259)
                ·
                  refine ⟨20337185919760608591186389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13558123946507072394124259 20337185919760608591186389)
                  ·
                    refine ⟨476652794994389263855931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20337185919760608591186389 476652794994389263855931)
                    ·
                      rfl

theorem cell22_1392417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1392417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392417 prefixEnd_1392417 := by exact prefixLift 1392417
  have htrace : WordTrace (prefixWord ++ tailWord_1392417) baseStart_1392417 baseEnd_1392417 := by
    simpa [prefixWord, tailWord_1392417, baseEnd_1392417] using wordTrace_append hprefix tailTrace_1392417
  have hstable : (prefixWord ++ tailWord_1392417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392417).length < 2 ^ (prefixWord ++ tailWord_1392417).sum := by decide
  have hdescent : baseEnd_1392417 < baseStart_1392417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392462 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1392462 : Nat := 118140960795 + 1392462 * 2 ^ 59
def prefixEnd_1392462 : Nat := 4983230072969 + 3 ^ 40 * 1392462 * 2
def baseEnd_1392462 : Nat := 476668199414024146480793

theorem tailTrace_1392462 : CollatzResearch.WordTrace tailWord_1392462 prefixEnd_1392462 476668199414024146480793 := by
  unfold tailWord_1392462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348407685169432802675455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33858174320903641614269093 6348407685169432802675455)
  ·
    refine ⟨9522611527754149204013183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6348407685169432802675455 9522611527754149204013183)
    ·
      refine ⟨14283917291631223806019775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9522611527754149204013183 14283917291631223806019775)
      ·
        refine ⟨21425875937446835709029663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14283917291631223806019775 21425875937446835709029663)
        ·
          refine ⟨32138813906170253563544495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21425875937446835709029663 32138813906170253563544495)
          ·
            refine ⟨48208220859255380345316743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32138813906170253563544495 48208220859255380345316743)
            ·
              refine ⟨72312331288883070517975115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48208220859255380345316743 72312331288883070517975115)
              ·
                refine ⟨108468496933324605776962673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72312331288883070517975115 108468496933324605776962673)
                ·
                  refine ⟨81351372699993454332722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108468496933324605776962673 81351372699993454332722005)
                  ·
                    refine ⟨476668199414024146480793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81351372699993454332722005 476668199414024146480793)
                    ·
                      rfl

theorem cell22_1392462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1392462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392462 prefixEnd_1392462 := by exact prefixLift 1392462
  have htrace : WordTrace (prefixWord ++ tailWord_1392462) baseStart_1392462 baseEnd_1392462 := by
    simpa [prefixWord, tailWord_1392462, baseEnd_1392462] using wordTrace_append hprefix tailTrace_1392462
  have hstable : (prefixWord ++ tailWord_1392462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392462).length < 2 ^ (prefixWord ++ tailWord_1392462).sum := by decide
  have hdescent : baseEnd_1392462 < baseStart_1392462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392479 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 1, 5]
def baseStart_1392479 : Nat := 118140960795 + 1392479 * 2 ^ 59
def prefixEnd_1392479 : Nat := 4983230072969 + 3 ^ 40 * 1392479 * 2
def baseEnd_1392479 : Nat := 476674018861441768805741

theorem tailTrace_1392479 : CollatzResearch.WordTrace tailWord_1392479 prefixEnd_1392479 476674018861441768805741 := by
  unfold tailWord_1392479
  simp only [CollatzResearch.WordTrace]
  refine ⟨50787881522293874324772491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33858587681529249549848327 50787881522293874324772491)
  ·
    refine ⟨76181822283440811487158737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50787881522293874324772491 76181822283440811487158737)
    ·
      refine ⟨57136366712580608615369053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76181822283440811487158737 57136366712580608615369053)
      ·
        refine ⟨21426137517217728230763395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57136366712580608615369053 21426137517217728230763395)
        ·
          refine ⟨32139206275826592346145093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21426137517217728230763395 32139206275826592346145093)
          ·
            refine ⟨6026101176717486064902205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32139206275826592346145093 6026101176717486064902205)
            ·
              refine ⟨2259787941269057274338327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6026101176717486064902205 2259787941269057274338327)
              ·
                refine ⟨3389681911903585911507491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259787941269057274338327 3389681911903585911507491)
                ·
                  refine ⟨5084522867855378867261237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389681911903585911507491 5084522867855378867261237)
                  ·
                    refine ⟨476674018861441768805741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5084522867855378867261237 476674018861441768805741)
                    ·
                      rfl

theorem cell22_1392479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_1392479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392479 prefixEnd_1392479 := by exact prefixLift 1392479
  have htrace : WordTrace (prefixWord ++ tailWord_1392479) baseStart_1392479 baseEnd_1392479 := by
    simpa [prefixWord, tailWord_1392479, baseEnd_1392479] using wordTrace_append hprefix tailTrace_1392479
  have hstable : (prefixWord ++ tailWord_1392479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392479).length < 2 ^ (prefixWord ++ tailWord_1392479).sum := by decide
  have hdescent : baseEnd_1392479 < baseStart_1392479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392530 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1392530 : Nat := 118140960795 + 1392530 * 2 ^ 59
def prefixEnd_1392530 : Nat := 4983230072969 + 3 ^ 40 * 1392530 * 2
def baseEnd_1392530 : Nat := 476691477203694635780585

theorem tailTrace_1392530 : CollatzResearch.WordTrace tailWord_1392530 prefixEnd_1392530 476691477203694635780585 := by
  unfold tailWord_1392530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697435411277277508719761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33859827763406073356586029 12697435411277277508719761)
  ·
    refine ⟨9523076558457958131539821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12697435411277277508719761 9523076558457958131539821)
    ·
      refine ⟨3571153709421734299327433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9523076558457958131539821 3571153709421734299327433)
      ·
        refine ⟨2678365282066300724495575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3571153709421734299327433 2678365282066300724495575)
        ·
          refine ⟨4017547923099451086743363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678365282066300724495575 4017547923099451086743363)
          ·
            refine ⟨6026321884649176630115045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017547923099451086743363 6026321884649176630115045)
            ·
              refine ⟨1129935353371720618146571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6026321884649176630115045 1129935353371720618146571)
              ·
                refine ⟨1694903030057580927219857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129935353371720618146571 1694903030057580927219857)
                ·
                  refine ⟨1271177272543185695414893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1694903030057580927219857 1271177272543185695414893)
                  ·
                    refine ⟨476691477203694635780585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271177272543185695414893 476691477203694635780585)
                    ·
                      rfl

theorem cell22_1392530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1392530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392530 prefixEnd_1392530 := by exact prefixLift 1392530
  have htrace : WordTrace (prefixWord ++ tailWord_1392530) baseStart_1392530 baseEnd_1392530 := by
    simpa [prefixWord, tailWord_1392530, baseEnd_1392530] using wordTrace_append hprefix tailTrace_1392530
  have hstable : (prefixWord ++ tailWord_1392530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392530).length < 2 ^ (prefixWord ++ tailWord_1392530).sum := by decide
  have hdescent : baseEnd_1392530 < baseStart_1392530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392534 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1392534 : Nat := 118140960795 + 1392534 * 2 ^ 59
def prefixEnd_1392534 : Nat := 4983230072969 + 3 ^ 40 * 1392534 * 2
def baseEnd_1392534 : Nat := 476692846485439958680573

theorem tailTrace_1392534 : CollatzResearch.WordTrace tailWord_1392534 prefixEnd_1392534 476692846485439958680573 := by
  unfold tailWord_1392534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174367971068413669876541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33859925024729745812016437 3174367971068413669876541)
  ·
    refine ⟨1190387989150655126203703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3174367971068413669876541 1190387989150655126203703)
    ·
      refine ⟨1785581983725982689305555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190387989150655126203703 1785581983725982689305555)
      ·
        refine ⟨2678372975588974033958333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785581983725982689305555 2678372975588974033958333)
        ·
          refine ⟨1004389865845865262734375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2678372975588974033958333 1004389865845865262734375)
          ·
            refine ⟨1506584798768797894101563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004389865845865262734375 1506584798768797894101563)
            ·
              refine ⟨2259877198153196841152345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506584798768797894101563 2259877198153196841152345)
              ·
                refine ⟨1694907898614897630864259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259877198153196841152345 1694907898614897630864259)
                ·
                  refine ⟨2542361847922346446296389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694907898614897630864259 2542361847922346446296389)
                  ·
                    refine ⟨476692846485439958680573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2542361847922346446296389 476692846485439958680573)
                    ·
                      rfl

theorem cell22_1392534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1392534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392534 prefixEnd_1392534 := by exact prefixLift 1392534
  have htrace : WordTrace (prefixWord ++ tailWord_1392534) baseStart_1392534 baseEnd_1392534 := by
    simpa [prefixWord, tailWord_1392534, baseEnd_1392534] using wordTrace_append hprefix tailTrace_1392534
  have hstable : (prefixWord ++ tailWord_1392534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392534).length < 2 ^ (prefixWord ++ tailWord_1392534).sum := by decide
  have hdescent : baseEnd_1392534 < baseStart_1392534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392569 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_1392569 : Nat := 118140960795 + 1392569 * 2 ^ 59
def prefixEnd_1392569 : Nat := 4983230072969 + 3 ^ 40 * 1392569 * 2
def baseEnd_1392569 : Nat := 476704827700711534055465

theorem tailTrace_1392569 : CollatzResearch.WordTrace tailWord_1392569 prefixEnd_1392569 476704827700711534055465 := by
  unfold tailWord_1392569
  simp only [CollatzResearch.WordTrace]
  refine ⟨50791164091967819695548761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33860776061311879797032507 50791164091967819695548761)
  ·
    refine ⟨38093373068975864771661571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50791164091967819695548761 38093373068975864771661571)
    ·
      refine ⟨57140059603463797157492357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38093373068975864771661571 57140059603463797157492357)
      ·
        refine ⟨10713761175649461967029817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57140059603463797157492357 10713761175649461967029817)
        ·
          refine ⟨8035320881737096475272363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10713761175649461967029817 8035320881737096475272363)
          ·
            refine ⟨12052981322605644712908545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035320881737096475272363 12052981322605644712908545)
            ·
              refine ⟨9039735991954233534681409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12052981322605644712908545 9039735991954233534681409)
              ·
                refine ⟨6779801993965675151011057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9039735991954233534681409 6779801993965675151011057)
                ·
                  refine ⟨5084851495474256363258293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6779801993965675151011057 5084851495474256363258293)
                  ·
                    refine ⟨476704827700711534055465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5084851495474256363258293 476704827700711534055465)
                    ·
                      rfl

theorem cell22_1392569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_1392569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392569 prefixEnd_1392569 := by exact prefixLift 1392569
  have htrace : WordTrace (prefixWord ++ tailWord_1392569) baseStart_1392569 baseEnd_1392569 := by
    simpa [prefixWord, tailWord_1392569, baseEnd_1392569] using wordTrace_append hprefix tailTrace_1392569
  have hstable : (prefixWord ++ tailWord_1392569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392569).length < 2 ^ (prefixWord ++ tailWord_1392569).sum := by decide
  have hdescent : baseEnd_1392569 < baseStart_1392569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392599 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 6]
def baseStart_1392599 : Nat := 118140960795 + 1392599 * 2 ^ 59
def prefixEnd_1392599 : Nat := 4983230072969 + 3 ^ 40 * 1392599 * 2
def baseEnd_1392599 : Nat := 158905032437933818601791

theorem tailTrace_1392599 : CollatzResearch.WordTrace tailWord_1392599 prefixEnd_1392599 158905032437933818601791 := by
  unfold tailWord_1392599
  simp only [CollatzResearch.WordTrace]
  refine ⟨50792258281859134819140851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33861505521239423212760567 50792258281859134819140851)
  ·
    refine ⟨76188387422788702228711277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50792258281859134819140851 76188387422788702228711277)
    ·
      refine ⟨28570645283545763335766729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76188387422788702228711277 28570645283545763335766729)
      ·
        refine ⟨21427983962659322501825047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28570645283545763335766729 21427983962659322501825047)
        ·
          refine ⟨32141975943988983752737571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21427983962659322501825047 32141975943988983752737571)
          ·
            refine ⟨48212963915983475629106357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32141975943988983752737571 48212963915983475629106357)
            ·
              refine ⟨4519965367123450840228721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48212963915983475629106357 4519965367123450840228721)
              ·
                refine ⟨3389974025342588130171541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4519965367123450840228721 3389974025342588130171541)
                ·
                  refine ⟨158905032437933818601791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3389974025342588130171541 158905032437933818601791)
                  ·
                    rfl

theorem cell22_1392599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 6].length) (baseStart_1392599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392599 prefixEnd_1392599 := by exact prefixLift 1392599
  have htrace : WordTrace (prefixWord ++ tailWord_1392599) baseStart_1392599 baseEnd_1392599 := by
    simpa [prefixWord, tailWord_1392599, baseEnd_1392599] using wordTrace_append hprefix tailTrace_1392599
  have hstable : (prefixWord ++ tailWord_1392599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392599).length < 2 ^ (prefixWord ++ tailWord_1392599).sum := by decide
  have hdescent : baseEnd_1392599 < baseStart_1392599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392661 : List Nat := [1, 3, 2, 1, 5, 1, 1, 8]
def baseStart_1392661 : Nat := 118140960795 + 1392661 * 2 ^ 59
def prefixEnd_1392661 : Nat := 4983230072969 + 3 ^ 40 * 1392661 * 2
def baseEnd_1392661 : Nat := 52970702353428217861687

theorem tailTrace_1392661 : CollatzResearch.WordTrace tailWord_1392661 prefixEnd_1392661 52970702353428217861687 := by
  unfold tailWord_1392661
  simp only [CollatzResearch.WordTrace]
  refine ⟨50794519607634519407897837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33863013071756346271931891 50794519607634519407897837)
  ·
    refine ⟨19047944852862944777961689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50794519607634519407897837 19047944852862944777961689)
    ·
      refine ⟨14285958639647208583471267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19047944852862944777961689 14285958639647208583471267)
      ·
        refine ⟨21428937959470812875206901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285958639647208583471267 21428937959470812875206901)
        ·
          refine ⟨2008962933700388707050647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21428937959470812875206901 2008962933700388707050647)
          ·
            refine ⟨3013444400550583060575971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008962933700388707050647 3013444400550583060575971)
            ·
              refine ⟨4520166600825874590863957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013444400550583060575971 4520166600825874590863957)
              ·
                refine ⟨52970702353428217861687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4520166600825874590863957 52970702353428217861687)
                ·
                  rfl

theorem cell22_1392661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 8].length) (baseStart_1392661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392661 prefixEnd_1392661 := by exact prefixLift 1392661
  have htrace : WordTrace (prefixWord ++ tailWord_1392661) baseStart_1392661 baseEnd_1392661 := by
    simpa [prefixWord, tailWord_1392661, baseEnd_1392661] using wordTrace_append hprefix tailTrace_1392661
  have hstable : (prefixWord ++ tailWord_1392661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392661).length < 2 ^ (prefixWord ++ tailWord_1392661).sum := by decide
  have hdescent : baseEnd_1392661 < baseStart_1392661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392680 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1392680 : Nat := 118140960795 + 1392680 * 2 ^ 59
def prefixEnd_1392680 : Nat := 4983230072969 + 3 ^ 40 * 1392680 * 2
def baseEnd_1392680 : Nat := 476742825269144244530125

theorem tailTrace_1392680 : CollatzResearch.WordTrace tailWord_1392680 prefixEnd_1392680 476742825269144244530125 := by
  unfold tailWord_1392680
  simp only [CollatzResearch.WordTrace]
  refine ⟨25397606297282842826419747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33863475063043790435226329 25397606297282842826419747)
  ·
    refine ⟨38096409445924264239629621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25397606297282842826419747 38096409445924264239629621)
    ·
      refine ⟨3571538385555399772465277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38096409445924264239629621 3571538385555399772465277)
      ·
        refine ⟨1339326894583274914674479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3571538385555399772465277 1339326894583274914674479)
        ·
          refine ⟨2008990341874912372011719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339326894583274914674479 2008990341874912372011719)
          ·
            refine ⟨3013485512812368558017579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008990341874912372011719 3013485512812368558017579)
            ·
              refine ⟨4520228269218552837026369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013485512812368558017579 4520228269218552837026369)
              ·
                refine ⟨3390171201913914627769777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4520228269218552837026369 3390171201913914627769777)
                ·
                  refine ⟨2542628401435435970827333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390171201913914627769777 2542628401435435970827333)
                  ·
                    refine ⟨476742825269144244530125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2542628401435435970827333 476742825269144244530125)
                    ·
                      rfl

theorem cell22_1392680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1392680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392680 prefixEnd_1392680 := by exact prefixLift 1392680
  have htrace : WordTrace (prefixWord ++ tailWord_1392680) baseStart_1392680 baseEnd_1392680 := by
    simpa [prefixWord, tailWord_1392680, baseEnd_1392680] using wordTrace_append hprefix tailTrace_1392680
  have hstable : (prefixWord ++ tailWord_1392680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392680).length < 2 ^ (prefixWord ++ tailWord_1392680).sum := by decide
  have hdescent : baseEnd_1392680 < baseStart_1392680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392693 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1392693 : Nat := 118140960795 + 1392693 * 2 ^ 59
def prefixEnd_1392693 : Nat := 4983230072969 + 3 ^ 40 * 1392693 * 2
def baseEnd_1392693 : Nat := 476747275434816543955085

theorem tailTrace_1392693 : CollatzResearch.WordTrace tailWord_1392693 prefixEnd_1392693 476747275434816543955085 := by
  unfold tailWord_1392693
  simp only [CollatzResearch.WordTrace]
  refine ⟨50795686743518588873062733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33863791162345725915375155 50795686743518588873062733)
  ·
    refine ⟨19048382528819470827398525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50795686743518588873062733 19048382528819470827398525)
    ·
      refine ⟨7143143448307301560274447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19048382528819470827398525 7143143448307301560274447)
      ·
        refine ⟨10714715172460952340411671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143143448307301560274447 10714715172460952340411671)
        ·
          refine ⟨16072072758691428510617507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714715172460952340411671 16072072758691428510617507)
          ·
            refine ⟨24108109138037142765926261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16072072758691428510617507 24108109138037142765926261)
            ·
              refine ⟨2260135231690982134305587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24108109138037142765926261 2260135231690982134305587)
              ·
                refine ⟨3390202847536473201458381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260135231690982134305587 3390202847536473201458381)
                ·
                  refine ⟨1271326067826177450546893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3390202847536473201458381 1271326067826177450546893)
                  ·
                    refine ⟨476747275434816543955085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271326067826177450546893 476747275434816543955085)
                    ·
                      rfl

theorem cell22_1392693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1392693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392693 prefixEnd_1392693 := by exact prefixLift 1392693
  have htrace : WordTrace (prefixWord ++ tailWord_1392693) baseStart_1392693 baseEnd_1392693 := by
    simpa [prefixWord, tailWord_1392693, baseEnd_1392693] using wordTrace_append hprefix tailTrace_1392693
  have hstable : (prefixWord ++ tailWord_1392693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392693).length < 2 ^ (prefixWord ++ tailWord_1392693).sum := by decide
  have hdescent : baseEnd_1392693 < baseStart_1392693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392710 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1392710 : Nat := 118140960795 + 1392710 * 2 ^ 59
def prefixEnd_1392710 : Nat := 4983230072969 + 3 ^ 40 * 1392710 * 2
def baseEnd_1392710 : Nat := 476753094882234166280033

theorem tailTrace_1392710 : CollatzResearch.WordTrace tailWord_1392710 prefixEnd_1392710 476753094882234166280033 := by
  unfold tailWord_1392710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587384587014281274263487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33864204522971333850954389 1587384587014281274263487)
  ·
    refine ⟨2381076880521421911395231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587384587014281274263487 2381076880521421911395231)
    ·
      refine ⟨3571615320782132867092847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381076880521421911395231 3571615320782132867092847)
      ·
        refine ⟨5357422981173199300639271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3571615320782132867092847 5357422981173199300639271)
        ·
          refine ⟨8036134471759798950958907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357422981173199300639271 8036134471759798950958907)
          ·
            refine ⟨12054201707639698426438361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8036134471759798950958907 12054201707639698426438361)
            ·
              refine ⟨9040651280729773819828771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12054201707639698426438361 9040651280729773819828771)
              ·
                refine ⟨13560976921094660729743157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9040651280729773819828771 13560976921094660729743157)
                ·
                  refine ⟨1271341586352624443413421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13560976921094660729743157 1271341586352624443413421)
                  ·
                    refine ⟨476753094882234166280033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271341586352624443413421 476753094882234166280033)
                    ·
                      rfl

theorem cell22_1392710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1392710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392710 prefixEnd_1392710 := by exact prefixLift 1392710
  have htrace : WordTrace (prefixWord ++ tailWord_1392710) baseStart_1392710 baseEnd_1392710 := by
    simpa [prefixWord, tailWord_1392710, baseEnd_1392710] using wordTrace_append hprefix tailTrace_1392710
  have hstable : (prefixWord ++ tailWord_1392710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392710).length < 2 ^ (prefixWord ++ tailWord_1392710).sum := by decide
  have hdescent : baseEnd_1392710 < baseStart_1392710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392719 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_1392719 : Nat := 118140960795 + 1392719 * 2 ^ 59
def prefixEnd_1392719 : Nat := 4983230072969 + 3 ^ 40 * 1392719 * 2
def baseEnd_1392719 : Nat := 476756175766161142805005

theorem tailTrace_1392719 : CollatzResearch.WordTrace tailWord_1392719 prefixEnd_1392719 476756175766161142805005 := by
  unfold tailWord_1392719
  simp only [CollatzResearch.WordTrace]
  refine ⟨50796635041424395313509211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33864423360949596875672807 50796635041424395313509211)
  ·
    refine ⟨76194952562136592970263817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50796635041424395313509211 76194952562136592970263817)
    ·
      refine ⟨57146214421602444727697863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76194952562136592970263817 57146214421602444727697863)
      ·
        refine ⟨85719321632403667091546795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57146214421602444727697863 85719321632403667091546795)
        ·
          refine ⟨128578982448605500637320193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85719321632403667091546795 128578982448605500637320193)
          ·
            refine ⟨96434236836454125477990145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128578982448605500637320193 96434236836454125477990145)
            ·
              refine ⟨72325677627340594108492609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96434236836454125477990145 72325677627340594108492609)
              ·
                refine ⟨54244258220505445581369457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72325677627340594108492609 54244258220505445581369457)
                ·
                  refine ⟨40683193665379084186027093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54244258220505445581369457 40683193665379084186027093)
                  ·
                    refine ⟨476756175766161142805005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40683193665379084186027093 476756175766161142805005)
                    ·
                      rfl

theorem cell22_1392719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_1392719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392719 prefixEnd_1392719 := by exact prefixLift 1392719
  have htrace : WordTrace (prefixWord ++ tailWord_1392719) baseStart_1392719 baseEnd_1392719 := by
    simpa [prefixWord, tailWord_1392719, baseEnd_1392719] using wordTrace_append hprefix tailTrace_1392719
  have hstable : (prefixWord ++ tailWord_1392719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392719).length < 2 ^ (prefixWord ++ tailWord_1392719).sum := by decide
  have hdescent : baseEnd_1392719 < baseStart_1392719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392796 : List Nat := [2, 2, 3, 2, 1, 1, 11]
def baseStart_1392796 : Nat := 118140960795 + 1392796 * 2 ^ 59
def prefixEnd_1392796 : Nat := 4983230072969 + 3 ^ 40 * 1392796 * 2
def baseEnd_1392796 : Nat := 17658612386657726245547

theorem tailTrace_1392796 : CollatzResearch.WordTrace tailWord_1392796 prefixEnd_1392796 17658612386657726245547 := by
  unfold tailWord_1392796
  simp only [CollatzResearch.WordTrace]
  refine ⟨25399721731072718732031121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33866295641430291642708161 25399721731072718732031121)
  ·
    refine ⟨19049791298304539049023341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25399721731072718732031121 19049791298304539049023341)
    ·
      refine ⟨7143671736864202143383753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19049791298304539049023341 7143671736864202143383753)
      ·
        refine ⟨5357753802648151607537815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7143671736864202143383753 5357753802648151607537815)
        ·
          refine ⟨8036630703972227411306723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357753802648151607537815 8036630703972227411306723)
          ·
            refine ⟨12054946055958341116960085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8036630703972227411306723 12054946055958341116960085)
            ·
              refine ⟨17658612386657726245547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12054946055958341116960085 17658612386657726245547)
              ·
                rfl

theorem cell22_1392796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 11].length) (baseStart_1392796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392796 prefixEnd_1392796 := by exact prefixLift 1392796
  have htrace : WordTrace (prefixWord ++ tailWord_1392796) baseStart_1392796 baseEnd_1392796 := by
    simpa [prefixWord, tailWord_1392796, baseEnd_1392796] using wordTrace_append hprefix tailTrace_1392796
  have hstable : (prefixWord ++ tailWord_1392796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392796).length < 2 ^ (prefixWord ++ tailWord_1392796).sum := by decide
  have hdescent : baseEnd_1392796 < baseStart_1392796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392800 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_1392800 : Nat := 118140960795 + 1392800 * 2 ^ 59
def prefixEnd_1392800 : Nat := 4983230072969 + 3 ^ 40 * 1392800 * 2
def baseEnd_1392800 : Nat := 476783903721503931529757

theorem tailTrace_1392800 : CollatzResearch.WordTrace tailWord_1392800 prefixEnd_1392800 476783903721503931529757 := by
  unfold tailWord_1392800
  simp only [CollatzResearch.WordTrace]
  refine ⟨25399794677065473073603927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33866392902753964098138569 25399794677065473073603927)
  ·
    refine ⟨38099692015598209610405891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25399794677065473073603927 38099692015598209610405891)
    ·
      refine ⟨57149538023397314415608837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38099692015598209610405891 57149538023397314415608837)
      ·
        refine ⟨10715538379386996452926657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57149538023397314415608837 10715538379386996452926657)
        ·
          refine ⟨8036653784540247339694993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10715538379386996452926657 8036653784540247339694993)
          ·
            refine ⟨6027490338405185504771245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8036653784540247339694993 6027490338405185504771245)
            ·
              refine ⟨2260308876901944564289217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6027490338405185504771245 2260308876901944564289217)
              ·
                refine ⟨1695231657676458423216913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260308876901944564289217 1695231657676458423216913)
                ·
                  refine ⟨1271423743257343817412685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695231657676458423216913 1271423743257343817412685)
                  ·
                    refine ⟨476783903721503931529757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271423743257343817412685 476783903721503931529757)
                    ·
                      rfl

theorem cell22_1392800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_1392800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392800 prefixEnd_1392800 := by exact prefixLift 1392800
  have htrace : WordTrace (prefixWord ++ tailWord_1392800) baseStart_1392800 baseEnd_1392800 := by
    simpa [prefixWord, tailWord_1392800, baseEnd_1392800] using wordTrace_append hprefix tailTrace_1392800
  have hstable : (prefixWord ++ tailWord_1392800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392800).length < 2 ^ (prefixWord ++ tailWord_1392800).sum := by decide
  have hdescent : baseEnd_1392800 < baseStart_1392800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392817 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 1, 5]
def baseStart_1392817 : Nat := 118140960795 + 1392817 * 2 ^ 59
def prefixEnd_1392817 : Nat := 4983230072969 + 3 ^ 40 * 1392817 * 2
def baseEnd_1392817 : Nat := 476789723168921553854705

theorem tailTrace_1392817 : CollatzResearch.WordTrace tailWord_1392817 prefixEnd_1392817 476789723168921553854705 := by
  unfold tailWord_1392817
  simp only [CollatzResearch.WordTrace]
  refine ⟨50800209395069358050576705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33866806263379572033717803 50800209395069358050576705)
  ·
    refine ⟨38100157046302018537932529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50800209395069358050576705 38100157046302018537932529)
    ·
      refine ⟨28575117784726513903449397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38100157046302018537932529 28575117784726513903449397)
      ·
        refine ⟨2678917292318110678448381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28575117784726513903449397 2678917292318110678448381)
        ·
          refine ⟨1004593984619291504418143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2678917292318110678448381 1004593984619291504418143)
          ·
            refine ⟨1506890976928937256627215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004593984619291504418143 1506890976928937256627215)
            ·
              refine ⟨2260336465393405884940823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506890976928937256627215 2260336465393405884940823)
              ·
                refine ⟨3390504698090108827411235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260336465393405884940823 3390504698090108827411235)
                ·
                  refine ⟨5085757047135163241116853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390504698090108827411235 5085757047135163241116853)
                  ·
                    refine ⟨476789723168921553854705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5085757047135163241116853 476789723168921553854705)
                    ·
                      rfl

theorem cell22_1392817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_1392817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392817 prefixEnd_1392817 := by exact prefixLift 1392817
  have htrace : WordTrace (prefixWord ++ tailWord_1392817) baseStart_1392817 baseEnd_1392817 := by
    simpa [prefixWord, tailWord_1392817, baseEnd_1392817] using wordTrace_append hprefix tailTrace_1392817
  have hstable : (prefixWord ++ tailWord_1392817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392817).length < 2 ^ (prefixWord ++ tailWord_1392817).sum := by decide
  have hdescent : baseEnd_1392817 < baseStart_1392817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392826 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1392826 : Nat := 118140960795 + 1392826 * 2 ^ 59
def prefixEnd_1392826 : Nat := 4983230072969 + 3 ^ 40 * 1392826 * 2
def baseEnd_1392826 : Nat := 476792804052848530379677

theorem tailTrace_1392826 : CollatzResearch.WordTrace tailWord_1392826 prefixEnd_1392826 476792804052848530379677 := by
  unfold tailWord_1392826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700134413009188146913583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33867025101357835058436221 12700134413009188146913583)
  ·
    refine ⟨19050201619513782220370375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12700134413009188146913583 19050201619513782220370375)
    ·
      refine ⟨28575302429270673330555563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050201619513782220370375 28575302429270673330555563)
      ·
        refine ⟨42862953643906009995833345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28575302429270673330555563 42862953643906009995833345)
        ·
          refine ⟨32147215232929507496875009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42862953643906009995833345 32147215232929507496875009)
          ·
            refine ⟨24110411424697130622656257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32147215232929507496875009 24110411424697130622656257)
            ·
              refine ⟨18082808568522847966992193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24110411424697130622656257 18082808568522847966992193)
              ·
                refine ⟨13562106426392135975244145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18082808568522847966992193 13562106426392135975244145)
                ·
                  refine ⟨10171579819794101981433109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13562106426392135975244145 10171579819794101981433109)
                  ·
                    refine ⟨476792804052848530379677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10171579819794101981433109 476792804052848530379677)
                    ·
                      rfl

theorem cell22_1392826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1392826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392826 prefixEnd_1392826 := by exact prefixLift 1392826
  have htrace : WordTrace (prefixWord ++ tailWord_1392826) baseStart_1392826 baseEnd_1392826 := by
    simpa [prefixWord, tailWord_1392826, baseEnd_1392826] using wordTrace_append hprefix tailTrace_1392826
  have hstable : (prefixWord ++ tailWord_1392826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392826).length < 2 ^ (prefixWord ++ tailWord_1392826).sum := by decide
  have hdescent : baseEnd_1392826 < baseStart_1392826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392920 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 4]
def baseStart_1392920 : Nat := 118140960795 + 1392920 * 2 ^ 59
def prefixEnd_1392920 : Nat := 4983230072969 + 3 ^ 40 * 1392920 * 2
def baseEnd_1392920 : Nat := 158941660724621206176463

theorem tailTrace_1392920 : CollatzResearch.WordTrace tailWord_1392920 prefixEnd_1392920 158941660724621206176463 := by
  unfold tailWord_1392920
  simp only [CollatzResearch.WordTrace]
  refine ⟨25401983056848103320788107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33869310742464137761050809 25401983056848103320788107)
  ·
    refine ⟨38102974585272154981182161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25401983056848103320788107 38102974585272154981182161)
    ·
      refine ⟨28577230938954116235886621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38102974585272154981182161 28577230938954116235886621)
      ·
        refine ⟨10716461602107793588457483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28577230938954116235886621 10716461602107793588457483)
        ·
          refine ⟨16074692403161690382686225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10716461602107793588457483 16074692403161690382686225)
          ·
            refine ⟨12056019302371267787014669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16074692403161690382686225 12056019302371267787014669)
            ·
              refine ⟨4521007238389225420130501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12056019302371267787014669 4521007238389225420130501)
              ·
                refine ⟨847688857197979766274469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4521007238389225420130501 847688857197979766274469)
                ·
                  refine ⟨158941660724621206176463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 847688857197979766274469 158941660724621206176463)
                  ·
                    rfl

theorem cell22_1392920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_1392920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392920 prefixEnd_1392920 := by exact prefixLift 1392920
  have htrace : WordTrace (prefixWord ++ tailWord_1392920) baseStart_1392920 baseEnd_1392920 := by
    simpa [prefixWord, tailWord_1392920, baseEnd_1392920] using wordTrace_append hprefix tailTrace_1392920
  have hstable : (prefixWord ++ tailWord_1392920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392920).length < 2 ^ (prefixWord ++ tailWord_1392920).sum := by decide
  have hdescent : baseEnd_1392920 < baseStart_1392920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392978 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1392978 : Nat := 118140960795 + 1392978 * 2 ^ 59
def prefixEnd_1392978 : Nat := 4983230072969 + 3 ^ 40 * 1392978 * 2
def baseEnd_1392978 : Nat := 476844836759170800579211

theorem tailTrace_1392978 : CollatzResearch.WordTrace tailWord_1392978 prefixEnd_1392978 476844836759170800579211 := by
  unfold tailWord_1392978
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701520386871520636796897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33870721031657388364791725 12701520386871520636796897)
  ·
    refine ⟨9526140290153640477597673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12701520386871520636796897 9526140290153640477597673)
    ·
      refine ⟨7144605217615230358198255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9526140290153640477597673 7144605217615230358198255)
      ·
        refine ⟨10716907826422845537297383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7144605217615230358198255 10716907826422845537297383)
        ·
          refine ⟨16075361739634268305946075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10716907826422845537297383 16075361739634268305946075)
          ·
            refine ⟨24113042609451402458919113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16075361739634268305946075 24113042609451402458919113)
            ·
              refine ⟨18084781957088551844189335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24113042609451402458919113 18084781957088551844189335)
              ·
                refine ⟨27127172935632827766284003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18084781957088551844189335 27127172935632827766284003)
                ·
                  refine ⟨40690759403449241649426005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27127172935632827766284003 40690759403449241649426005)
                  ·
                    refine ⟨476844836759170800579211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40690759403449241649426005 476844836759170800579211)
                    ·
                      rfl

theorem cell22_1392978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1392978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1392978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1392978 prefixEnd_1392978 := by exact prefixLift 1392978
  have htrace : WordTrace (prefixWord ++ tailWord_1392978) baseStart_1392978 baseEnd_1392978 := by
    simpa [prefixWord, tailWord_1392978, baseEnd_1392978] using wordTrace_append hprefix tailTrace_1392978
  have hstable : (prefixWord ++ tailWord_1392978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392978).length < 2 ^ (prefixWord ++ tailWord_1392978).sum := by decide
  have hdescent : baseEnd_1392978 < baseStart_1392978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393117 : List Nat := [1, 4, 3, 1, 1, 1, 5, 6]
def baseStart_1393117 : Nat := 118140960795 + 1393117 * 2 ^ 59
def prefixEnd_1393117 : Nat := 4983230072969 + 3 ^ 40 * 1393117 * 2
def baseEnd_1393117 : Nat := 52988046588868974594865

theorem tailTrace_1393117 : CollatzResearch.WordTrace tailWord_1393117 prefixEnd_1393117 52988046588868974594865 := by
  unfold tailWord_1393117
  simp only [CollatzResearch.WordTrace]
  refine ⟨50811151293982509286497605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33874100862655006190998403 50811151293982509286497605)
  ·
    refine ⟨9527090867621720491218301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50811151293982509286497605 9527090867621720491218301)
    ·
      refine ⟨3572659075358145184206863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9527090867621720491218301 3572659075358145184206863)
      ·
        refine ⟨5358988613037217776310295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572659075358145184206863 5358988613037217776310295)
        ·
          refine ⟨8038482919555826664465443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5358988613037217776310295 8038482919555826664465443)
          ·
            refine ⟨12057724379333739996698165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8038482919555826664465443 12057724379333739996698165)
            ·
              refine ⟨1130411660562538124690453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12057724379333739996698165 1130411660562538124690453)
              ·
                refine ⟨52988046588868974594865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1130411660562538124690453 52988046588868974594865)
                ·
                  rfl

theorem cell22_1393117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 6].length) (baseStart_1393117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393117 prefixEnd_1393117 := by exact prefixLift 1393117
  have htrace : WordTrace (prefixWord ++ tailWord_1393117) baseStart_1393117 baseEnd_1393117 := by
    simpa [prefixWord, tailWord_1393117, baseEnd_1393117] using wordTrace_append hprefix tailTrace_1393117
  have hstable : (prefixWord ++ tailWord_1393117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393117).length < 2 ^ (prefixWord ++ tailWord_1393117).sum := by decide
  have hdescent : baseEnd_1393117 < baseStart_1393117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393138 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_1393138 : Nat := 118140960795 + 1393138 * 2 ^ 59
def prefixEnd_1393138 : Nat := 4983230072969 + 3 ^ 40 * 1393138 * 2
def baseEnd_1393138 : Nat := 476899608028983716578721

theorem tailTrace_1393138 : CollatzResearch.WordTrace tailWord_1393138 prefixEnd_1393138 476899608028983716578721 := by
  unfold tailWord_1393138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702979306726607468253017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33874611484604286582008045 12702979306726607468253017)
  ·
    refine ⟨9527234480044955601189763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12702979306726607468253017 9527234480044955601189763)
    ·
      refine ⟨14290851720067433401784645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9527234480044955601189763 14290851720067433401784645)
      ·
        refine ⟨2679534697512643762834621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14290851720067433401784645 2679534697512643762834621)
        ·
          refine ⟨1004825511567241411062983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2679534697512643762834621 1004825511567241411062983)
          ·
            refine ⟨1507238267350862116594475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004825511567241411062983 1507238267350862116594475)
            ·
              refine ⟨2260857401026293174891713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507238267350862116594475 2260857401026293174891713)
              ·
                refine ⟨1695643050769719881168785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260857401026293174891713 1695643050769719881168785)
                ·
                  refine ⟨1271732288077289910876589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695643050769719881168785 1271732288077289910876589)
                  ·
                    refine ⟨476899608028983716578721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271732288077289910876589 476899608028983716578721)
                    ·
                      rfl

theorem cell22_1393138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_1393138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393138 prefixEnd_1393138 := by exact prefixLift 1393138
  have htrace : WordTrace (prefixWord ++ tailWord_1393138) baseStart_1393138 baseEnd_1393138 := by
    simpa [prefixWord, tailWord_1393138, baseEnd_1393138] using wordTrace_append hprefix tailTrace_1393138
  have hstable : (prefixWord ++ tailWord_1393138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393138).length < 2 ^ (prefixWord ++ tailWord_1393138).sum := by decide
  have hdescent : baseEnd_1393138 < baseStart_1393138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393149 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_1393149 : Nat := 118140960795 + 1393149 * 2 ^ 59
def prefixEnd_1393149 : Nat := 4983230072969 + 3 ^ 40 * 1393149 * 2
def baseEnd_1393149 : Nat := 476903373553783354553687

theorem tailTrace_1393149 : CollatzResearch.WordTrace tailWord_1393149 prefixEnd_1393149 476903373553783354553687 := by
  unfold tailWord_1393149
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812318429866578751662501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33874878953244385834441667 50812318429866578751662501)
  ·
    refine ⟨9527309705599983515936719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50812318429866578751662501 9527309705599983515936719)
    ·
      refine ⟨14290964558399975273905079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9527309705599983515936719 14290964558399975273905079)
      ·
        refine ⟨21436446837599962910857619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14290964558399975273905079 21436446837599962910857619)
        ·
          refine ⟨32154670256399944366286429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21436446837599962910857619 32154670256399944366286429)
          ·
            refine ⟨12058001346149979137357411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32154670256399944366286429 12058001346149979137357411)
            ·
              refine ⟨18087002019224968706036117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12058001346149979137357411 18087002019224968706036117)
              ·
                refine ⟨847828219651170408095443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18087002019224968706036117 847828219651170408095443)
                ·
                  refine ⟨1271742329476755612143165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847828219651170408095443 1271742329476755612143165)
                  ·
                    refine ⟨476903373553783354553687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271742329476755612143165 476903373553783354553687)
                    ·
                      rfl

theorem cell22_1393149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_1393149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393149 prefixEnd_1393149 := by exact prefixLift 1393149
  have htrace : WordTrace (prefixWord ++ tailWord_1393149) baseStart_1393149 baseEnd_1393149 := by
    simpa [prefixWord, tailWord_1393149, baseEnd_1393149] using wordTrace_append hprefix tailTrace_1393149
  have hstable : (prefixWord ++ tailWord_1393149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393149).length < 2 ^ (prefixWord ++ tailWord_1393149).sum := by decide
  have hdescent : baseEnd_1393149 < baseStart_1393149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393237 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1393237 : Nat := 118140960795 + 1393237 * 2 ^ 59
def prefixEnd_1393237 : Nat := 4983230072969 + 3 ^ 40 * 1393237 * 2
def baseEnd_1393237 : Nat := 476933497752180458353417

theorem tailTrace_1393237 : CollatzResearch.WordTrace tailWord_1393237 prefixEnd_1393237 476933497752180458353417 := by
  unfold tailWord_1393237
  simp only [CollatzResearch.WordTrace]
  refine ⟨50815528053547769780865965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33877018702365179853910643 50815528053547769780865965)
  ·
    refine ⟨19055823020080413667824737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50815528053547769780865965 19055823020080413667824737)
    ·
      refine ⟨14291867265060310250868553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19055823020080413667824737 14291867265060310250868553)
      ·
        refine ⟨10718900448795232688151415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14291867265060310250868553 10718900448795232688151415)
        ·
          refine ⟨16078350673192849032227123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718900448795232688151415 16078350673192849032227123)
          ·
            refine ⟨24117526009789273548340685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16078350673192849032227123 24117526009789273548340685)
            ·
              refine ⟨9044072253670977580627757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24117526009789273548340685 9044072253670977580627757)
              ·
                refine ⟨3391527095126616592735409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9044072253670977580627757 3391527095126616592735409)
                ·
                  refine ⟨2543645321344962444551557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3391527095126616592735409 2543645321344962444551557)
                  ·
                    refine ⟨476933497752180458353417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543645321344962444551557 476933497752180458353417)
                    ·
                      rfl

theorem cell22_1393237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1393237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393237 prefixEnd_1393237 := by exact prefixLift 1393237
  have htrace : WordTrace (prefixWord ++ tailWord_1393237) baseStart_1393237 baseEnd_1393237 := by
    simpa [prefixWord, tailWord_1393237, baseEnd_1393237] using wordTrace_append hprefix tailTrace_1393237
  have hstable : (prefixWord ++ tailWord_1393237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393237).length < 2 ^ (prefixWord ++ tailWord_1393237).sum := by decide
  have hdescent : baseEnd_1393237 < baseStart_1393237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393284 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_1393284 : Nat := 118140960795 + 1393284 * 2 ^ 59
def prefixEnd_1393284 : Nat := 4983230072969 + 3 ^ 40 * 1393284 * 2
def baseEnd_1393284 : Nat := 476949586812688002428273

theorem tailTrace_1393284 : CollatzResearch.WordTrace tailWord_1393284 prefixEnd_1393284 476949586812688002428273 := by
  unfold tailWord_1393284
  simp only [CollatzResearch.WordTrace]
  refine ⟨25408621142188748403913453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33878161522918331205217937 25408621142188748403913453)
  ·
    refine ⟨9528232928320780651467545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25408621142188748403913453 9528232928320780651467545)
    ·
      refine ⟨7146174696240585488600659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9528232928320780651467545 7146174696240585488600659)
      ·
        refine ⟨10719262044360878232900989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7146174696240585488600659 10719262044360878232900989)
        ·
          refine ⟨4019723266635329337337871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10719262044360878232900989 4019723266635329337337871)
          ·
            refine ⟨6029584899952994006006807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019723266635329337337871 6029584899952994006006807)
            ·
              refine ⟨9044377349929491009010211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029584899952994006006807 9044377349929491009010211)
              ·
                refine ⟨13566566024894236513515317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9044377349929491009010211 13566566024894236513515317)
                ·
                  refine ⟨1271865564833834673142061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13566566024894236513515317 1271865564833834673142061)
                  ·
                    refine ⟨476949586812688002428273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271865564833834673142061 476949586812688002428273)
                    ·
                      rfl

theorem cell22_1393284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_1393284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393284 prefixEnd_1393284 := by exact prefixLift 1393284
  have htrace : WordTrace (prefixWord ++ tailWord_1393284) baseStart_1393284 baseEnd_1393284 := by
    simpa [prefixWord, tailWord_1393284, baseEnd_1393284] using wordTrace_append hprefix tailTrace_1393284
  have hstable : (prefixWord ++ tailWord_1393284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393284).length < 2 ^ (prefixWord ++ tailWord_1393284).sum := by decide
  have hdescent : baseEnd_1393284 < baseStart_1393284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393344 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_1393344 : Nat := 118140960795 + 1393344 * 2 ^ 59
def prefixEnd_1393344 : Nat := 4983230072969 + 3 ^ 40 * 1393344 * 2
def baseEnd_1393344 : Nat := 476970126038867845928089

theorem tailTrace_1393344 : CollatzResearch.WordTrace tailWord_1393344 prefixEnd_1393344 476970126038867845928089 := by
  unfold tailWord_1393344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25409715332080063527505543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33879620442773418036674057 25409715332080063527505543)
  ·
    refine ⟨38114572998120095291258315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25409715332080063527505543 38114572998120095291258315)
    ·
      refine ⟨57171859497180142936887473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38114572998120095291258315 57171859497180142936887473)
      ·
        refine ⟨42878894622885107202665605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57171859497180142936887473 42878894622885107202665605)
        ·
          refine ⟨8039792741790957600499801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42878894622885107202665605 8039792741790957600499801)
          ·
            refine ⟨6029844556343218200374851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8039792741790957600499801 6029844556343218200374851)
            ·
              refine ⟨9044766834514827300562277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029844556343218200374851 9044766834514827300562277)
              ·
                refine ⟨1695893781471530118855427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9044766834514827300562277 1695893781471530118855427)
                ·
                  refine ⟨2543840672207295178283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695893781471530118855427 2543840672207295178283141)
                  ·
                    refine ⟨476970126038867845928089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543840672207295178283141 476970126038867845928089)
                    ·
                      rfl

theorem cell22_1393344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_1393344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393344 prefixEnd_1393344 := by exact prefixLift 1393344
  have htrace : WordTrace (prefixWord ++ tailWord_1393344) baseStart_1393344 baseEnd_1393344 := by
    simpa [prefixWord, tailWord_1393344, baseEnd_1393344] using wordTrace_append hprefix tailTrace_1393344
  have hstable : (prefixWord ++ tailWord_1393344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393344).length < 2 ^ (prefixWord ++ tailWord_1393344).sum := by decide
  have hdescent : baseEnd_1393344 < baseStart_1393344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393389 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1393389 : Nat := 118140960795 + 1393389 * 2 ^ 59
def prefixEnd_1393389 : Nat := 4983230072969 + 3 ^ 40 * 1393389 * 2
def baseEnd_1393389 : Nat := 476985530458502728552951

theorem tailTrace_1393389 : CollatzResearch.WordTrace tailWord_1393389 prefixEnd_1393389 476985530458502728552951 := by
  unfold tailWord_1393389
  simp only [CollatzResearch.WordTrace]
  refine ⟨50821071948997099740399221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33880714632664733160266147 50821071948997099740399221)
  ·
    refine ⟨4764475495218478100662427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50821071948997099740399221 4764475495218478100662427)
    ·
      refine ⟨7146713242827717150993641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4764475495218478100662427 7146713242827717150993641)
      ·
        refine ⟨5360034932120787863245231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7146713242827717150993641 5360034932120787863245231)
        ·
          refine ⟨8040052398181181794867847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360034932120787863245231 8040052398181181794867847)
          ·
            refine ⟨12060078597271772692301771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040052398181181794867847 12060078597271772692301771)
            ·
              refine ⟨18090117895907659038452657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12060078597271772692301771 18090117895907659038452657)
              ·
                refine ⟨13567588421930744278839493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18090117895907659038452657 13567588421930744278839493)
                ·
                  refine ⟨2543922829112014552282405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13567588421930744278839493 2543922829112014552282405)
                  ·
                    refine ⟨476985530458502728552951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543922829112014552282405 476985530458502728552951)
                    ·
                      rfl

theorem cell22_1393389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1393389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393389 prefixEnd_1393389 := by exact prefixLift 1393389
  have htrace : WordTrace (prefixWord ++ tailWord_1393389) baseStart_1393389 baseEnd_1393389 := by
    simpa [prefixWord, tailWord_1393389, baseEnd_1393389] using wordTrace_append hprefix tailTrace_1393389
  have hstable : (prefixWord ++ tailWord_1393389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393389).length < 2 ^ (prefixWord ++ tailWord_1393389).sum := by decide
  have hdescent : baseEnd_1393389 < baseStart_1393389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393391 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 2, 3]
def baseStart_1393391 : Nat := 118140960795 + 1393391 * 2 ^ 59
def prefixEnd_1393391 : Nat := 4983230072969 + 3 ^ 40 * 1393391 * 2
def baseEnd_1393391 : Nat := 476986215099375390002945

theorem tailTrace_1393391 : CollatzResearch.WordTrace tailWord_1393391 prefixEnd_1393391 476986215099375390002945 := by
  unfold tailWord_1393391
  simp only [CollatzResearch.WordTrace]
  refine ⟨50821144894989854081972027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33880763263326569387981351 50821144894989854081972027)
  ·
    refine ⟨76231717342484781122958041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50821144894989854081972027 76231717342484781122958041)
    ·
      refine ⟨57173788006863585842218531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76231717342484781122958041 57173788006863585842218531)
      ·
        refine ⟨85760682010295378763327797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57173788006863585842218531 85760682010295378763327797)
        ·
          refine ⟨8040063938465191759061981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85760682010295378763327797 8040063938465191759061981)
          ·
            refine ⟨3015023976924446909648243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8040063938465191759061981 3015023976924446909648243)
            ·
              refine ⟨4522535965386670364472365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015023976924446909648243 4522535965386670364472365)
              ·
                refine ⟨1695950987020001386677137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4522535965386670364472365 1695950987020001386677137)
                ·
                  refine ⟨1271963240265001040007853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695950987020001386677137 1271963240265001040007853)
                  ·
                    refine ⟨476986215099375390002945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271963240265001040007853 476986215099375390002945)
                    ·
                      rfl

theorem cell22_1393391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_1393391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393391 prefixEnd_1393391 := by exact prefixLift 1393391
  have htrace : WordTrace (prefixWord ++ tailWord_1393391) baseStart_1393391 baseEnd_1393391 := by
    simpa [prefixWord, tailWord_1393391, baseEnd_1393391] using wordTrace_append hprefix tailTrace_1393391
  have hstable : (prefixWord ++ tailWord_1393391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393391).length < 2 ^ (prefixWord ++ tailWord_1393391).sum := by decide
  have hdescent : baseEnd_1393391 < baseStart_1393391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393402 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1393402 : Nat := 118140960795 + 1393402 * 2 ^ 59
def prefixEnd_1393402 : Nat := 4983230072969 + 3 ^ 40 * 1393402 * 2
def baseEnd_1393402 : Nat := 476989980624175027977911

theorem tailTrace_1393402 : CollatzResearch.WordTrace tailWord_1393402 prefixEnd_1393402 476989980624175027977911 := by
  unfold tailWord_1393402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12705386524487500740155615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33881030731966668640414973 12705386524487500740155615)
  ·
    refine ⟨19058079786731251110233423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12705386524487500740155615 19058079786731251110233423)
    ·
      refine ⟨28587119680096876665350135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19058079786731251110233423 28587119680096876665350135)
      ·
        refine ⟨42880679520145314998025203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28587119680096876665350135 42880679520145314998025203)
        ·
          refine ⟨64321019280217972497037805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42880679520145314998025203 64321019280217972497037805)
          ·
            refine ⟨24120382230081739686389177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64321019280217972497037805 24120382230081739686389177)
            ·
              refine ⟨18090286672561304764791883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24120382230081739686389177 18090286672561304764791883)
              ·
                refine ⟨27135430008841957147187825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18090286672561304764791883 27135430008841957147187825)
                ·
                  refine ⟨20351572506631467860390869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27135430008841957147187825 20351572506631467860390869)
                  ·
                    refine ⟨476989980624175027977911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20351572506631467860390869 476989980624175027977911)
                    ·
                      rfl

theorem cell22_1393402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1393402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393402 prefixEnd_1393402 := by exact prefixLift 1393402
  have htrace : WordTrace (prefixWord ++ tailWord_1393402) baseStart_1393402 baseEnd_1393402 := by
    simpa [prefixWord, tailWord_1393402, baseEnd_1393402] using wordTrace_append hprefix tailTrace_1393402
  have hstable : (prefixWord ++ tailWord_1393402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393402).length < 2 ^ (prefixWord ++ tailWord_1393402).sum := by decide
  have hdescent : baseEnd_1393402 < baseStart_1393402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393406 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1393406 : Nat := 118140960795 + 1393406 * 2 ^ 59
def prefixEnd_1393406 : Nat := 4983230072969 + 3 ^ 40 * 1393406 * 2
def baseEnd_1393406 : Nat := 476991349905920350877899

theorem tailTrace_1393406 : CollatzResearch.WordTrace tailWord_1393406 prefixEnd_1393406 476991349905920350877899 := by
  unfold tailWord_1393406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6352711498741938955471009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33881127993290341095845381 6352711498741938955471009)
  ·
    refine ⟨4764533624056454216603257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6352711498741938955471009 4764533624056454216603257)
    ·
      refine ⟨3573400218042340662452443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4764533624056454216603257 3573400218042340662452443)
      ·
        refine ⟨5360100327063510993678665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573400218042340662452443 5360100327063510993678665)
        ·
          refine ⟨4020075245297633245258999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5360100327063510993678665 4020075245297633245258999)
          ·
            refine ⟨6030112867946449867888499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020075245297633245258999 6030112867946449867888499)
            ·
              refine ⟨9045169301919674801832749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030112867946449867888499 9045169301919674801832749)
              ·
                refine ⟨3391938488219878050687281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9045169301919674801832749 3391938488219878050687281)
                ·
                  refine ⟨2543953866164908538015461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3391938488219878050687281 2543953866164908538015461)
                  ·
                    refine ⟨476991349905920350877899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543953866164908538015461 476991349905920350877899)
                    ·
                      rfl

theorem cell22_1393406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1393406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393406 prefixEnd_1393406 := by exact prefixLift 1393406
  have htrace : WordTrace (prefixWord ++ tailWord_1393406) baseStart_1393406 baseEnd_1393406 := by
    simpa [prefixWord, tailWord_1393406, baseEnd_1393406] using wordTrace_append hprefix tailTrace_1393406
  have hstable : (prefixWord ++ tailWord_1393406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393406).length < 2 ^ (prefixWord ++ tailWord_1393406).sum := by decide
  have hdescent : baseEnd_1393406 < baseStart_1393406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393421 : List Nat := [1, 7, 2, 12]
def baseStart_1393421 : Nat := 118140960795 + 1393421 * 2 ^ 59
def prefixEnd_1393421 : Nat := 4983230072969 + 3 ^ 40 * 1393421 * 2
def baseEnd_1393421 : Nat := 654316165586372169757

theorem tailTrace_1393421 : CollatzResearch.WordTrace tailWord_1393421 prefixEnd_1393421 654316165586372169757 := by
  unfold tailWord_1393421
  simp only [CollatzResearch.WordTrace]
  refine ⟨50822239084881169205564117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33881492723254112803709411 50822239084881169205564117)
  ·
    refine ⟨1191146228551902403255409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50822239084881169205564117 1191146228551902403255409)
    ·
      refine ⟨893359671413926802441557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1191146228551902403255409 893359671413926802441557)
      ·
        refine ⟨654316165586372169757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 893359671413926802441557 654316165586372169757)
        ·
          rfl

theorem cell22_1393421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 12].length) (baseStart_1393421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393421 prefixEnd_1393421 := by exact prefixLift 1393421
  have htrace : WordTrace (prefixWord ++ tailWord_1393421) baseStart_1393421 baseEnd_1393421 := by
    simpa [prefixWord, tailWord_1393421, baseEnd_1393421] using wordTrace_append hprefix tailTrace_1393421
  have hstable : (prefixWord ++ tailWord_1393421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393421).length < 2 ^ (prefixWord ++ tailWord_1393421).sum := by decide
  have hdescent : baseEnd_1393421 < baseStart_1393421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393541 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_1393541 : Nat := 118140960795 + 1393541 * 2 ^ 59
def prefixEnd_1393541 : Nat := 4983230072969 + 3 ^ 40 * 1393541 * 2
def baseEnd_1393541 : Nat := 477037563164824998752485

theorem tailTrace_1393541 : CollatzResearch.WordTrace tailWord_1393541 prefixEnd_1393541 477037563164824998752485 := by
  unfold tailWord_1393541
  simp only [CollatzResearch.WordTrace]
  refine ⟨50826615844446429699932477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33884410562964286466621651 50826615844446429699932477)
  ·
    refine ⟨19059980941667411137474679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50826615844446429699932477 19059980941667411137474679)
    ·
      refine ⟨28589971412501116706212019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19059980941667411137474679 28589971412501116706212019)
      ·
        refine ⟨42884957118751675059318029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28589971412501116706212019 42884957118751675059318029)
        ·
          refine ⟨16081858919531878147244261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42884957118751675059318029 16081858919531878147244261)
          ·
            refine ⟨3015348547412227152608299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16081858919531878147244261 3015348547412227152608299)
            ·
              refine ⟨4523022821118340728912449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015348547412227152608299 4523022821118340728912449)
              ·
                refine ⟨3392267115838755546684337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523022821118340728912449 3392267115838755546684337)
                ·
                  refine ⟨2544200336879066660013253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392267115838755546684337 2544200336879066660013253)
                  ·
                    refine ⟨477037563164824998752485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544200336879066660013253 477037563164824998752485)
                    ·
                      rfl

theorem cell22_1393541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_1393541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393541 prefixEnd_1393541 := by exact prefixLift 1393541
  have htrace : WordTrace (prefixWord ++ tailWord_1393541) baseStart_1393541 baseEnd_1393541 := by
    simpa [prefixWord, tailWord_1393541, baseEnd_1393541] using wordTrace_append hprefix tailTrace_1393541
  have hstable : (prefixWord ++ tailWord_1393541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393541).length < 2 ^ (prefixWord ++ tailWord_1393541).sum := by decide
  have hdescent : baseEnd_1393541 < baseStart_1393541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393556 : List Nat := [2, 4, 2, 1, 1, 1, 4, 7]
def baseStart_1393556 : Nat := 118140960795 + 1393556 * 2 ^ 59
def prefixEnd_1393556 : Nat := 4983230072969 + 3 ^ 40 * 1393556 * 2
def baseEnd_1393556 : Nat := 53004744219041106625271

theorem tailTrace_1393556 : CollatzResearch.WordTrace tailWord_1393556 prefixEnd_1393556 53004744219041106625271 := by
  unfold tailWord_1393556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25413581469696043630864261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33884775292928058174485681 25413581469696043630864261)
  ·
    refine ⟨4765046525568008180787049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25413581469696043630864261 4765046525568008180787049)
    ·
      refine ⟨3573784894176006135590287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4765046525568008180787049 3573784894176006135590287)
      ·
        refine ⟨5360677341264009203385431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573784894176006135590287 5360677341264009203385431)
        ·
          refine ⟨8041016011896013805078147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360677341264009203385431 8041016011896013805078147)
          ·
            refine ⟨12061524017844020707617221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041016011896013805078147 12061524017844020707617221)
            ·
              refine ⟨2261535753345753882678229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12061524017844020707617221 2261535753345753882678229)
              ·
                refine ⟨53004744219041106625271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2261535753345753882678229 53004744219041106625271)
                ·
                  rfl

theorem cell22_1393556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_1393556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393556 prefixEnd_1393556 := by exact prefixLift 1393556
  have htrace : WordTrace (prefixWord ++ tailWord_1393556) baseStart_1393556 baseEnd_1393556 := by
    simpa [prefixWord, tailWord_1393556, baseEnd_1393556] using wordTrace_append hprefix tailTrace_1393556
  have hstable : (prefixWord ++ tailWord_1393556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393556).length < 2 ^ (prefixWord ++ tailWord_1393556).sum := by decide
  have hdescent : baseEnd_1393556 < baseStart_1393556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
