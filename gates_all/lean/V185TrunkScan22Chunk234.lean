import V185TrunkScan22Chunk233

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2087116 : List Nat := [2, 2, 1, 6, 2, 1, 1, 7]
def baseStart_2087116 : Nat := 118140960795 + 2087116 * 2 ^ 59
def prefixEnd_2087116 : Nat := 4983230072969 + 3 ^ 40 * 2087116 * 2
def baseEnd_2087116 : Nat := 79384717754767509833447

theorem tailTrace_2087116 : CollatzResearch.WordTrace tailWord_2087116 prefixEnd_2087116 79384717754767509833447 := by
  unfold tailWord_2087116
  simp only [CollatzResearch.WordTrace]
  refine ⟨38061687153371328939696601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50748916204495105252928801 38061687153371328939696601)
  ·
    refine ⟨28546265365028496704772451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38061687153371328939696601 28546265365028496704772451)
    ·
      refine ⟨42819398047542745057158677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28546265365028496704772451 42819398047542745057158677)
      ·
        refine ⟨2007159283478566174554313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42819398047542745057158677 2007159283478566174554313)
        ·
          refine ⟨1505369462608924630915735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2007159283478566174554313 1505369462608924630915735)
          ·
            refine ⟨2258054193913386946373603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505369462608924630915735 2258054193913386946373603)
            ·
              refine ⟨3387081290870080419560405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258054193913386946373603 3387081290870080419560405)
              ·
                refine ⟨79384717754767509833447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3387081290870080419560405 79384717754767509833447)
                ·
                  rfl

theorem cell22_2087116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 7].length) (baseStart_2087116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087116 prefixEnd_2087116 := by exact prefixLift 2087116
  have htrace : WordTrace (prefixWord ++ tailWord_2087116) baseStart_2087116 baseEnd_2087116 := by
    simpa [prefixWord, tailWord_2087116, baseEnd_2087116] using wordTrace_append hprefix tailTrace_2087116
  have hstable : (prefixWord ++ tailWord_2087116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087116).length < 2 ^ (prefixWord ++ tailWord_2087116).sum := by decide
  have hdescent : baseEnd_2087116 < baseStart_2087116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087155 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 8]
def baseStart_2087155 : Nat := 118140960795 + 2087155 * 2 ^ 59
def prefixEnd_2087155 : Nat := 4983230072969 + 3 ^ 40 * 2087155 * 2
def baseEnd_2087155 : Nat := 238158603429974828925301

theorem tailTrace_2087155 : CollatzResearch.WordTrace tailWord_2087155 prefixEnd_2087155 238158603429974828925301 := by
  unfold tailWord_2087155
  simp only [CollatzResearch.WordTrace]
  refine ⟨76124796753601367540062919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50749864502400911693375279 76124796753601367540062919)
  ·
    refine ⟨114187195130402051310094379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76124796753601367540062919 114187195130402051310094379)
    ·
      refine ⟨171280792695603076965141569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114187195130402051310094379 171280792695603076965141569)
      ·
        refine ⟨128460594521702307723856177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171280792695603076965141569 128460594521702307723856177)
        ·
          refine ⟨96345445891276730792892133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128460594521702307723856177 96345445891276730792892133)
          ·
            refine ⟨18064771104614387023667275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96345445891276730792892133 18064771104614387023667275)
            ·
              refine ⟨27097156656921580535500913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18064771104614387023667275 27097156656921580535500913)
              ·
                refine ⟨20322867492691185401625685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27097156656921580535500913 20322867492691185401625685)
                ·
                  refine ⟨238158603429974828925301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20322867492691185401625685 238158603429974828925301)
                  ·
                    rfl

theorem cell22_2087155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_2087155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087155 prefixEnd_2087155 := by exact prefixLift 2087155
  have htrace : WordTrace (prefixWord ++ tailWord_2087155) baseStart_2087155 baseEnd_2087155 := by
    simpa [prefixWord, tailWord_2087155, baseEnd_2087155] using wordTrace_append hprefix tailTrace_2087155
  have hstable : (prefixWord ++ tailWord_2087155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087155).length < 2 ^ (prefixWord ++ tailWord_2087155).sum := by decide
  have hdescent : baseEnd_2087155 < baseStart_2087155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087204 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_2087204 : Nat := 118140960795 + 2087204 * 2 ^ 59
def prefixEnd_2087204 : Nat := 4983230072969 + 3 ^ 40 * 2087204 * 2
def baseEnd_2087204 : Nat := 714492583991304692300753

theorem tailTrace_2087204 : CollatzResearch.WordTrace tailWord_2087204 prefixEnd_2087204 714492583991304692300753 := by
  unfold tailWord_2087204
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063291965211924454298333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50751055953615899272397777 38063291965211924454298333)
  ·
    refine ⟨14273734486954471670361875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38063291965211924454298333 14273734486954471670361875)
    ·
      refine ⟨21410601730431707505542813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273734486954471670361875 21410601730431707505542813)
      ·
        refine ⟨8028975648911890314578555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21410601730431707505542813 8028975648911890314578555)
        ·
          refine ⟨12043463473367835471867833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028975648911890314578555 12043463473367835471867833)
          ·
            refine ⟨9032597605025876603900875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12043463473367835471867833 9032597605025876603900875)
            ·
              refine ⟨13548896407538814905851313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032597605025876603900875 13548896407538814905851313)
              ·
                refine ⟨10161672305654111179388485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13548896407538814905851313 10161672305654111179388485)
                ·
                  refine ⟨1905313557310145846135341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10161672305654111179388485 1905313557310145846135341)
                  ·
                    refine ⟨714492583991304692300753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905313557310145846135341 714492583991304692300753)
                    ·
                      rfl

theorem cell22_2087204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_2087204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087204 prefixEnd_2087204 := by exact prefixLift 2087204
  have htrace : WordTrace (prefixWord ++ tailWord_2087204) baseStart_2087204 baseEnd_2087204 := by
    simpa [prefixWord, tailWord_2087204, baseEnd_2087204] using wordTrace_append hprefix tailTrace_2087204
  have hstable : (prefixWord ++ tailWord_2087204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087204).length < 2 ^ (prefixWord ++ tailWord_2087204).sum := by decide
  have hdescent : baseEnd_2087204 < baseStart_2087204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087307 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 8]
def baseStart_2087307 : Nat := 118140960795 + 2087307 * 2 ^ 59
def prefixEnd_2087307 : Nat := 4983230072969 + 3 ^ 40 * 2087307 * 2
def baseEnd_2087307 : Nat := 238175947665415585658479

theorem tailTrace_2087307 : CollatzResearch.WordTrace tailWord_2087307 prefixEnd_2087307 238175947665415585658479 := by
  unfold tailWord_2087307
  simp only [CollatzResearch.WordTrace]
  refine ⟨76130340649050697499596175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50753560432700464999730783 76130340649050697499596175)
  ·
    refine ⟨114195510973576046249394263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76130340649050697499596175 114195510973576046249394263)
    ·
      refine ⟨171293266460364069374091395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114195510973576046249394263 171293266460364069374091395)
      ·
        refine ⟨256939899690546104061137093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171293266460364069374091395 256939899690546104061137093)
        ·
          refine ⟨48176231191977394511463205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256939899690546104061137093 48176231191977394511463205)
          ·
            refine ⟨9033043348495761470899351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48176231191977394511463205 9033043348495761470899351)
            ·
              refine ⟨13549565022743642206349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033043348495761470899351 13549565022743642206349027)
              ·
                refine ⟨20324347534115463309523541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549565022743642206349027 20324347534115463309523541)
                ·
                  refine ⟨238175947665415585658479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20324347534115463309523541 238175947665415585658479)
                  ·
                    rfl

theorem cell22_2087307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_2087307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087307 prefixEnd_2087307 := by exact prefixLift 2087307
  have htrace : WordTrace (prefixWord ++ tailWord_2087307) baseStart_2087307 baseEnd_2087307 := by
    simpa [prefixWord, tailWord_2087307, baseEnd_2087307] using wordTrace_append hprefix tailTrace_2087307
  have hstable : (prefixWord ++ tailWord_2087307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087307).length < 2 ^ (prefixWord ++ tailWord_2087307).sum := by decide
  have hdescent : baseEnd_2087307 < baseStart_2087307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087352 : List Nat := [2, 1, 2, 1, 2, 2, 1, 11]
def baseStart_2087352 : Nat := 118140960795 + 2087352 * 2 ^ 59
def prefixEnd_2087352 : Nat := 4983230072969 + 3 ^ 40 * 2087352 * 2
def baseEnd_2087352 : Nat := 79393694157320182177811

theorem tailTrace_2087352 : CollatzResearch.WordTrace tailWord_2087352 prefixEnd_2087352 79393694157320182177811 := by
  unfold tailWord_2087352
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065990966943835092492155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50754654622591780123322873 38065990966943835092492155)
  ·
    refine ⟨57098986450415752638738233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38065990966943835092492155 57098986450415752638738233)
    ·
      refine ⟨42824239837811814479053675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57098986450415752638738233 42824239837811814479053675)
      ·
        refine ⟨64236359756717721718580513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42824239837811814479053675 64236359756717721718580513)
        ·
          refine ⟨48177269817538291288935385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64236359756717721718580513 48177269817538291288935385)
          ·
            refine ⟨36132952363153718466701539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48177269817538291288935385 36132952363153718466701539)
            ·
              refine ⟨54199428544730577700052309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36132952363153718466701539 54199428544730577700052309)
              ·
                refine ⟨79393694157320182177811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 54199428544730577700052309 79393694157320182177811)
                ·
                  rfl

theorem cell22_2087352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_2087352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087352 prefixEnd_2087352 := by exact prefixLift 2087352
  have htrace : WordTrace (prefixWord ++ tailWord_2087352) baseStart_2087352 baseEnd_2087352 := by
    simpa [prefixWord, tailWord_2087352, baseEnd_2087352] using wordTrace_append hprefix tailTrace_2087352
  have hstable : (prefixWord ++ tailWord_2087352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087352).length < 2 ^ (prefixWord ++ tailWord_2087352).sum := by decide
  have hdescent : baseEnd_2087352 < baseStart_2087352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087356 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_2087356 : Nat := 118140960795 + 2087356 * 2 ^ 59
def prefixEnd_2087356 : Nat := 4983230072969 + 3 ^ 40 * 2087356 * 2
def baseEnd_2087356 : Nat := 714544616697626962500287

theorem tailTrace_2087356 : CollatzResearch.WordTrace tailWord_2087356 prefixEnd_2087356 714544616697626962500287 := by
  unfold tailWord_2087356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38066063912936589434064961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50754751883915452578753281 38066063912936589434064961)
  ·
    refine ⟨28549547934702442075548721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38066063912936589434064961 28549547934702442075548721)
    ·
      refine ⟨21412160951026831556661541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28549547934702442075548721 21412160951026831556661541)
      ·
        refine ⟨4014780178317530916874039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21412160951026831556661541 4014780178317530916874039)
        ·
          refine ⟨6022170267476296375311059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014780178317530916874039 6022170267476296375311059)
          ·
            refine ⟨9033255401214444562966589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022170267476296375311059 9033255401214444562966589)
            ·
              refine ⟨3387470775455416711112471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9033255401214444562966589 3387470775455416711112471)
              ·
                refine ⟨5081206163183125066668707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387470775455416711112471 5081206163183125066668707)
                ·
                  refine ⟨7621809244774687600003061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081206163183125066668707 7621809244774687600003061)
                  ·
                    refine ⟨714544616697626962500287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7621809244774687600003061 714544616697626962500287)
                    ·
                      rfl

theorem cell22_2087356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_2087356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087356 prefixEnd_2087356 := by exact prefixLift 2087356
  have htrace : WordTrace (prefixWord ++ tailWord_2087356) baseStart_2087356 baseEnd_2087356 := by
    simpa [prefixWord, tailWord_2087356, baseEnd_2087356] using wordTrace_append hprefix tailTrace_2087356
  have hstable : (prefixWord ++ tailWord_2087356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087356).length < 2 ^ (prefixWord ++ tailWord_2087356).sum := by decide
  have hdescent : baseEnd_2087356 < baseStart_2087356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087369 : List Nat := [1, 2, 1, 1, 2, 1, 8, 6]
def baseStart_2087369 : Nat := 118140960795 + 2087369 * 2 ^ 59
def prefixEnd_2087369 : Nat := 4983230072969 + 3 ^ 40 * 2087369 * 2
def baseEnd_2087369 : Nat := 79394340762588806880583

theorem tailTrace_2087369 : CollatzResearch.WordTrace tailWord_2087369 prefixEnd_2087369 79394340762588806880583 := by
  unfold tailWord_2087369
  simp only [CollatzResearch.WordTrace]
  refine ⟨76132601974826082088353161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50755067983217388058902107 76132601974826082088353161)
  ·
    refine ⟨57099451481119561566264871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76132601974826082088353161 57099451481119561566264871)
    ·
      refine ⟨85649177221679342349397307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57099451481119561566264871 85649177221679342349397307)
      ·
        refine ⟨128473765832519013524095961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85649177221679342349397307 128473765832519013524095961)
        ·
          refine ⟨96355324374389260143071971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128473765832519013524095961 96355324374389260143071971)
          ·
            refine ⟨144532986561583890214607957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96355324374389260143071971 144532986561583890214607957)
            ·
              refine ⟨1693745936268561213452437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 144532986561583890214607957 1693745936268561213452437)
              ·
                refine ⟨79394340762588806880583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1693745936268561213452437 79394340762588806880583)
                ·
                  rfl

theorem cell22_2087369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 6].length) (baseStart_2087369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087369 prefixEnd_2087369 := by exact prefixLift 2087369
  have htrace : WordTrace (prefixWord ++ tailWord_2087369) baseStart_2087369 baseEnd_2087369 := by
    simpa [prefixWord, tailWord_2087369, baseEnd_2087369] using wordTrace_append hprefix tailTrace_2087369
  have hstable : (prefixWord ++ tailWord_2087369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087369).length < 2 ^ (prefixWord ++ tailWord_2087369).sum := by decide
  have hdescent : baseEnd_2087369 < baseStart_2087369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087399 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2087399 : Nat := 118140960795 + 2087399 * 2 ^ 59
def prefixEnd_2087399 : Nat := 4983230072969 + 3 ^ 40 * 2087399 * 2
def baseEnd_2087399 : Nat := 714559336476389183675155

theorem tailTrace_2087399 : CollatzResearch.WordTrace tailWord_2087399 prefixEnd_2087399 714559336476389183675155 := by
  unfold tailWord_2087399
  simp only [CollatzResearch.WordTrace]
  refine ⟨76133696164717397211945251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50755797443144931474630167 76133696164717397211945251)
  ·
    refine ⟨114200544247076095817917877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76133696164717397211945251 114200544247076095817917877)
    ·
      refine ⟨10706301023163383982929801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114200544247076095817917877 10706301023163383982929801)
      ·
        refine ⟨8029725767372537987197351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10706301023163383982929801 8029725767372537987197351)
        ·
          refine ⟨12044588651058806980796027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8029725767372537987197351 12044588651058806980796027)
          ·
            refine ⟨18066882976588210471194041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044588651058806980796027 18066882976588210471194041)
            ·
              refine ⟨13550162232441157853395531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18066882976588210471194041 13550162232441157853395531)
              ·
                refine ⟨20325243348661736780093297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550162232441157853395531 20325243348661736780093297)
                ·
                  refine ⟨15243932511496302585069973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20325243348661736780093297 15243932511496302585069973)
                  ·
                    refine ⟨714559336476389183675155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15243932511496302585069973 714559336476389183675155)
                    ·
                      rfl

theorem cell22_2087399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2087399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087399 prefixEnd_2087399 := by exact prefixLift 2087399
  have htrace : WordTrace (prefixWord ++ tailWord_2087399) baseStart_2087399 baseEnd_2087399 := by
    simpa [prefixWord, tailWord_2087399, baseEnd_2087399] using wordTrace_append hprefix tailTrace_2087399
  have hstable : (prefixWord ++ tailWord_2087399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087399).length < 2 ^ (prefixWord ++ tailWord_2087399).sum := by decide
  have hdescent : baseEnd_2087399 < baseStart_2087399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087452 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_2087452 : Nat := 118140960795 + 2087452 * 2 ^ 59
def prefixEnd_2087452 : Nat := 4983230072969 + 3 ^ 40 * 2087452 * 2
def baseEnd_2087452 : Nat := 714577479459514712099993

theorem tailTrace_2087452 : CollatzResearch.WordTrace tailWord_2087452 prefixEnd_2087452 714577479459514712099993 := by
  unfold tailWord_2087452
  simp only [CollatzResearch.WordTrace]
  refine ⟨38067814616762693631812305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50757086155683591509083073 38067814616762693631812305)
  ·
    refine ⟨28550860962572020223859229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38067814616762693631812305 28550860962572020223859229)
    ·
      refine ⟨10706572860964507583947211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28550860962572020223859229 10706572860964507583947211)
      ·
        refine ⟨16059859291446761375920817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10706572860964507583947211 16059859291446761375920817)
        ·
          refine ⟨12044894468585071031940613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16059859291446761375920817 12044894468585071031940613)
          ·
            refine ⟨2258417712859700818488865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12044894468585071031940613 2258417712859700818488865)
            ·
              refine ⟨1693813284644775613866649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258417712859700818488865 1693813284644775613866649)
              ·
                refine ⟨1270359963483581710399987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693813284644775613866649 1270359963483581710399987)
                ·
                  refine ⟨1905539945225372565599981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270359963483581710399987 1905539945225372565599981)
                  ·
                    refine ⟨714577479459514712099993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905539945225372565599981 714577479459514712099993)
                    ·
                      rfl

theorem cell22_2087452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_2087452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087452 prefixEnd_2087452 := by exact prefixLift 2087452
  have htrace : WordTrace (prefixWord ++ tailWord_2087452) baseStart_2087452 baseEnd_2087452 := by
    simpa [prefixWord, tailWord_2087452, baseEnd_2087452] using wordTrace_append hprefix tailTrace_2087452
  have hstable : (prefixWord ++ tailWord_2087452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087452).length < 2 ^ (prefixWord ++ tailWord_2087452).sum := by decide
  have hdescent : baseEnd_2087452 < baseStart_2087452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087478 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2087478 : Nat := 118140960795 + 2087478 * 2 ^ 59
def prefixEnd_2087478 : Nat := 4983230072969 + 3 ^ 40 * 2087478 * 2
def baseEnd_2087478 : Nat := 714586379790859310949913

theorem tailTrace_2087478 : CollatzResearch.WordTrace tailWord_2087478 prefixEnd_2087478 714586379790859310949913 := by
  unfold tailWord_2087478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758536095714449606504443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50757718354287462469380725 4758536095714449606504443)
  ·
    refine ⟨7137804143571674409756665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4758536095714449606504443 7137804143571674409756665)
    ·
      refine ⟨5353353107678755807317499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7137804143571674409756665 5353353107678755807317499)
      ·
        refine ⟨8030029661518133710976249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353353107678755807317499 8030029661518133710976249)
        ·
          refine ⟨6022522246138600283232187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8030029661518133710976249 6022522246138600283232187)
          ·
            refine ⟨9033783369207900424848281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022522246138600283232187 9033783369207900424848281)
            ·
              refine ⟨6775337526905925318636211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9033783369207900424848281 6775337526905925318636211)
              ·
                refine ⟨10163006290358887977954317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775337526905925318636211 10163006290358887977954317)
                ·
                  refine ⟨3811127358884582991732869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10163006290358887977954317 3811127358884582991732869)
                  ·
                    refine ⟨714586379790859310949913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3811127358884582991732869 714586379790859310949913)
                    ·
                      rfl

theorem cell22_2087478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2087478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087478 prefixEnd_2087478 := by exact prefixLift 2087478
  have htrace : WordTrace (prefixWord ++ tailWord_2087478) baseStart_2087478 baseEnd_2087478 := by
    simpa [prefixWord, tailWord_2087478, baseEnd_2087478] using wordTrace_append hprefix tailTrace_2087478
  have hstable : (prefixWord ++ tailWord_2087478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087478).length < 2 ^ (prefixWord ++ tailWord_2087478).sum := by decide
  have hdescent : baseEnd_2087478 < baseStart_2087478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087493 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 4]
def baseStart_2087493 : Nat := 118140960795 + 2087493 * 2 ^ 59
def prefixEnd_2087493 : Nat := 4983230072969 + 3 ^ 40 * 2087493 * 2
def baseEnd_2087493 : Nat := 238197171532468090608289

theorem tailTrace_2087493 : CollatzResearch.WordTrace tailWord_2087493 prefixEnd_2087493 238197171532468090608289 := by
  unfold tailWord_2087493
  simp only [CollatzResearch.WordTrace]
  refine ⟨76137124626376851265867133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50758083084251234177244755 76137124626376851265867133)
  ·
    refine ⟨28551421734891319224700175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76137124626376851265867133 28551421734891319224700175)
    ·
      refine ⟨42827132602336978837050263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28551421734891319224700175 42827132602336978837050263)
      ·
        refine ⟨64240698903505468255575395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42827132602336978837050263 64240698903505468255575395)
        ·
          refine ⟨96361048355258202383363093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64240698903505468255575395 96361048355258202383363093)
          ·
            refine ⟨4516924141652728236720145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96361048355258202383363093 4516924141652728236720145)
            ·
              refine ⟨3387693106239546177540109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516924141652728236720145 3387693106239546177540109)
              ·
                refine ⟨1270384914839829816577541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3387693106239546177540109 1270384914839829816577541)
                ·
                  refine ⟨238197171532468090608289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270384914839829816577541 238197171532468090608289)
                  ·
                    rfl

theorem cell22_2087493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_2087493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087493 prefixEnd_2087493 := by exact prefixLift 2087493
  have htrace : WordTrace (prefixWord ++ tailWord_2087493) baseStart_2087493 baseEnd_2087493 := by
    simpa [prefixWord, tailWord_2087493, baseEnd_2087493] using wordTrace_append hprefix tailTrace_2087493
  have hstable : (prefixWord ++ tailWord_2087493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087493).length < 2 ^ (prefixWord ++ tailWord_2087493).sum := by decide
  have hdescent : baseEnd_2087493 < baseStart_2087493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087495 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 1, 4]
def baseStart_2087495 : Nat := 118140960795 + 2087495 * 2 ^ 59
def prefixEnd_2087495 : Nat := 4983230072969 + 3 ^ 40 * 2087495 * 2
def baseEnd_2087495 : Nat := 714592199238276933274861

theorem tailTrace_2087495 : CollatzResearch.WordTrace tailWord_2087495 prefixEnd_2087495 714592199238276933274861 := by
  unfold tailWord_2087495
  simp only [CollatzResearch.WordTrace]
  refine ⟨76137197572369605607439939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50758131714913070404959959 76137197572369605607439939)
  ·
    refine ⟨114205796358554408411159909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76137197572369605607439939 114205796358554408411159909)
    ·
      refine ⟨21413586817228951577092483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114205796358554408411159909 21413586817228951577092483)
      ·
        refine ⟨32120380225843427365638725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21413586817228951577092483 32120380225843427365638725)
        ·
          refine ⟨6022571292345642631057261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32120380225843427365638725 6022571292345642631057261)
          ·
            refine ⟨2258464234629615986646473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6022571292345642631057261 2258464234629615986646473)
            ·
              refine ⟨1693848175972211989984855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258464234629615986646473 1693848175972211989984855)
              ·
                refine ⟨2540772263958317984977283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693848175972211989984855 2540772263958317984977283)
                ·
                  refine ⟨3811158395937476977465925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540772263958317984977283 3811158395937476977465925)
                  ·
                    refine ⟨714592199238276933274861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3811158395937476977465925 714592199238276933274861)
                    ·
                      rfl

theorem cell22_2087495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_2087495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087495 prefixEnd_2087495 := by exact prefixLift 2087495
  have htrace : WordTrace (prefixWord ++ tailWord_2087495) baseStart_2087495 baseEnd_2087495 := by
    simpa [prefixWord, tailWord_2087495, baseEnd_2087495] using wordTrace_append hprefix tailTrace_2087495
  have hstable : (prefixWord ++ tailWord_2087495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087495).length < 2 ^ (prefixWord ++ tailWord_2087495).sum := by decide
  have hdescent : baseEnd_2087495 < baseStart_2087495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087506 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2087506 : Nat := 118140960795 + 2087506 * 2 ^ 59
def prefixEnd_2087506 : Nat := 4983230072969 + 3 ^ 40 * 2087506 * 2
def baseEnd_2087506 : Nat := 714595964763076571249827

theorem tailTrace_2087506 : CollatzResearch.WordTrace tailWord_2087506 prefixEnd_2087506 714595964763076571249827 := by
  unfold tailWord_2087506
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034399693832438621522593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50758399183553169657393581 19034399693832438621522593)
  ·
    refine ⟨14275799770374328966141945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19034399693832438621522593 14275799770374328966141945)
    ·
      refine ⟨10706849827780746724606459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14275799770374328966141945 10706849827780746724606459)
      ·
        refine ⟨16060274741671120086909689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10706849827780746724606459 16060274741671120086909689)
        ·
          refine ⟨12045206056253340065182267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16060274741671120086909689 12045206056253340065182267)
          ·
            refine ⟨18067809084380010097773401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045206056253340065182267 18067809084380010097773401)
            ·
              refine ⟨13550856813285007573330051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18067809084380010097773401 13550856813285007573330051)
              ·
                refine ⟨20326285219927511359995077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550856813285007573330051 20326285219927511359995077)
                ·
                  refine ⟨3811178478736408379999077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20326285219927511359995077 3811178478736408379999077)
                  ·
                    refine ⟨714595964763076571249827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3811178478736408379999077 714595964763076571249827)
                    ·
                      rfl

theorem cell22_2087506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2087506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087506 prefixEnd_2087506 := by exact prefixLift 2087506
  have htrace : WordTrace (prefixWord ++ tailWord_2087506) baseStart_2087506 baseEnd_2087506 := by
    simpa [prefixWord, tailWord_2087506, baseEnd_2087506] using wordTrace_append hprefix tailTrace_2087506
  have hstable : (prefixWord ++ tailWord_2087506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087506).length < 2 ^ (prefixWord ++ tailWord_2087506).sum := by decide
  have hdescent : baseEnd_2087506 < baseStart_2087506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087508 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2087508 : Nat := 118140960795 + 2087508 * 2 ^ 59
def prefixEnd_2087508 : Nat := 4983230072969 + 3 ^ 40 * 2087508 * 2
def baseEnd_2087508 : Nat := 714596649403949232699821

theorem tailTrace_2087508 : CollatzResearch.WordTrace tailWord_2087508 prefixEnd_2087508 714596649403949232699821 := by
  unfold tailWord_2087508
  simp only [CollatzResearch.WordTrace]
  refine ⟨38068835860661254413831589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50758447814215005885108785 38068835860661254413831589)
  ·
    refine ⟨7137906723873985202593423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38068835860661254413831589 7137906723873985202593423)
    ·
      refine ⟨10706860085810977803890135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7137906723873985202593423 10706860085810977803890135)
      ·
        refine ⟨16060290128716466705835203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10706860085810977803890135 16060290128716466705835203)
        ·
          refine ⟨24090435193074700058752805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16060290128716466705835203 24090435193074700058752805)
          ·
            refine ⟨4516956598701506261016151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24090435193074700058752805 4516956598701506261016151)
            ·
              refine ⟨6775434898052259391524227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516956598701506261016151 6775434898052259391524227)
              ·
                refine ⟨10163152347078389087286341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775434898052259391524227 10163152347078389087286341)
                ·
                  refine ⟨1905591065077197953866189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10163152347078389087286341 1905591065077197953866189)
                  ·
                    refine ⟨714596649403949232699821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905591065077197953866189 714596649403949232699821)
                    ·
                      rfl

theorem cell22_2087508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2087508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087508 prefixEnd_2087508 := by exact prefixLift 2087508
  have htrace : WordTrace (prefixWord ++ tailWord_2087508) baseStart_2087508 baseEnd_2087508 := by
    simpa [prefixWord, tailWord_2087508, baseEnd_2087508] using wordTrace_append hprefix tailTrace_2087508
  have hstable : (prefixWord ++ tailWord_2087508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087508).length < 2 ^ (prefixWord ++ tailWord_2087508).sum := by decide
  have hdescent : baseEnd_2087508 < baseStart_2087508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087525 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_2087525 : Nat := 118140960795 + 2087525 * 2 ^ 59
def prefixEnd_2087525 : Nat := 4983230072969 + 3 ^ 40 * 2087525 * 2
def baseEnd_2087525 : Nat := 714602468851366855024769

theorem tailTrace_2087525 : CollatzResearch.WordTrace tailWord_2087525 prefixEnd_2087525 714602468851366855024769 := by
  unfold tailWord_2087525
  simp only [CollatzResearch.WordTrace]
  refine ⟨76138291762260920731032029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50758861174840613820688019 76138291762260920731032029)
  ·
    refine ⟨28551859410847845274137011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76138291762260920731032029 28551859410847845274137011)
    ·
      refine ⟨42827789116271767911205517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28551859410847845274137011 42827789116271767911205517)
      ·
        refine ⟨16060420918601912966702069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42827789116271767911205517 16060420918601912966702069)
        ·
          refine ⟨1505664461118929340628319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16060420918601912966702069 1505664461118929340628319)
          ·
            refine ⟨2258496691678394010942479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505664461118929340628319 2258496691678394010942479)
            ·
              refine ⟨3387745037517591016413719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258496691678394010942479 3387745037517591016413719)
              ·
                refine ⟨5081617556276386524620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387745037517591016413719 5081617556276386524620579)
                ·
                  refine ⟨7622426334414579786930869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081617556276386524620579 7622426334414579786930869)
                  ·
                    refine ⟨714602468851366855024769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7622426334414579786930869 714602468851366855024769)
                    ·
                      rfl

theorem cell22_2087525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_2087525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087525 prefixEnd_2087525 := by exact prefixLift 2087525
  have htrace : WordTrace (prefixWord ++ tailWord_2087525) baseStart_2087525 baseEnd_2087525 := by
    simpa [prefixWord, tailWord_2087525, baseEnd_2087525] using wordTrace_append hprefix tailTrace_2087525
  have hstable : (prefixWord ++ tailWord_2087525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087525).length < 2 ^ (prefixWord ++ tailWord_2087525).sum := by decide
  have hdescent : baseEnd_2087525 < baseStart_2087525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087566 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2087566 : Nat := 118140960795 + 2087566 * 2 ^ 59
def prefixEnd_2087566 : Nat := 4983230072969 + 3 ^ 40 * 2087566 * 2
def baseEnd_2087566 : Nat := 238205501329752138249881

theorem tailTrace_2087566 : CollatzResearch.WordTrace tailWord_2087566 prefixEnd_2087566 238205501329752138249881 := by
  unfold tailWord_2087566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9517473394389048091659319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50759858103408256488849701 9517473394389048091659319)
  ·
    refine ⟨14276210091583572137488979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9517473394389048091659319 14276210091583572137488979)
    ·
      refine ⟨21414315137375358206233469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14276210091583572137488979 21414315137375358206233469)
      ·
        refine ⟨8030368176515759327337551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21414315137375358206233469 8030368176515759327337551)
        ·
          refine ⟨12045552264773638991006327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030368176515759327337551 12045552264773638991006327)
          ·
            refine ⟨18068328397160458486509491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045552264773638991006327 18068328397160458486509491)
            ·
              refine ⟨27102492595740687729764237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18068328397160458486509491 27102492595740687729764237)
              ·
                refine ⟨10163434723402757898661589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27102492595740687729764237 10163434723402757898661589)
                ·
                  refine ⟨238205501329752138249881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10163434723402757898661589 238205501329752138249881)
                  ·
                    rfl

theorem cell22_2087566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2087566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087566 prefixEnd_2087566 := by exact prefixLift 2087566
  have htrace : WordTrace (prefixWord ++ tailWord_2087566) baseStart_2087566 baseEnd_2087566 := by
    simpa [prefixWord, tailWord_2087566, baseEnd_2087566] using wordTrace_append hprefix tailTrace_2087566
  have hstable : (prefixWord ++ tailWord_2087566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087566).length < 2 ^ (prefixWord ++ tailWord_2087566).sum := by decide
  have hdescent : baseEnd_2087566 < baseStart_2087566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087570 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2087570 : Nat := 118140960795 + 2087570 * 2 ^ 59
def prefixEnd_2087570 : Nat := 4983230072969 + 3 ^ 40 * 2087570 * 2
def baseEnd_2087570 : Nat := 714617873271001737649631

theorem tailTrace_2087570 : CollatzResearch.WordTrace tailWord_2087570 prefixEnd_2087570 714617873271001737649631 := by
  unfold tailWord_2087570
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034983261774473354105041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50759955364731928944280109 19034983261774473354105041)
  ·
    refine ⟨14276237446330855015578781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19034983261774473354105041 14276237446330855015578781)
    ·
      refine ⟨5353589042374070630842043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14276237446330855015578781 5353589042374070630842043)
      ·
        refine ⟨8030383563561105946263065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353589042374070630842043 8030383563561105946263065)
        ·
          refine ⟨6022787672670829459697299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8030383563561105946263065 6022787672670829459697299)
          ·
            refine ⟨9034181509006244189545949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022787672670829459697299 9034181509006244189545949)
            ·
              refine ⟨3387818065877341571079731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9034181509006244189545949 3387818065877341571079731)
              ·
                refine ⟨5081727098816012356619597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387818065877341571079731 5081727098816012356619597)
                ·
                  refine ⟨1905647662056004633732349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5081727098816012356619597 1905647662056004633732349)
                  ·
                    refine ⟨714617873271001737649631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905647662056004633732349 714617873271001737649631)
                    ·
                      rfl

theorem cell22_2087570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2087570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087570 prefixEnd_2087570 := by exact prefixLift 2087570
  have htrace : WordTrace (prefixWord ++ tailWord_2087570) baseStart_2087570 baseEnd_2087570 := by
    simpa [prefixWord, tailWord_2087570, baseEnd_2087570] using wordTrace_append hprefix tailTrace_2087570
  have hstable : (prefixWord ++ tailWord_2087570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087570).length < 2 ^ (prefixWord ++ tailWord_2087570).sum := by decide
  have hdescent : baseEnd_2087570 < baseStart_2087570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087581 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2087581 : Nat := 118140960795 + 2087581 * 2 ^ 59
def prefixEnd_2087581 : Nat := 4983230072969 + 3 ^ 40 * 2087581 * 2
def baseEnd_2087581 : Nat := 714621638795801375624597

theorem tailTrace_2087581 : CollatzResearch.WordTrace tailWord_2087581 prefixEnd_2087581 714621638795801375624597 := by
  unfold tailWord_2087581
  simp only [CollatzResearch.WordTrace]
  refine ⟨76140334250058042295070597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50760222833372028196713731 76140334250058042295070597)
  ·
    refine ⟨14276312671885882930325737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76140334250058042295070597 14276312671885882930325737)
    ·
      refine ⟨10707234503914412197744303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14276312671885882930325737 10707234503914412197744303)
      ·
        refine ⟨16060851755871618296616455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10707234503914412197744303 16060851755871618296616455)
        ·
          refine ⟨24091277633807427444924683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16060851755871618296616455 24091277633807427444924683)
          ·
            refine ⟨36136916450711141167387025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24091277633807427444924683 36136916450711141167387025)
            ·
              refine ⟨27102687338033355875540269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36136916450711141167387025 27102687338033355875540269)
              ·
                refine ⟨10163507751762508453327601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27102687338033355875540269 10163507751762508453327601)
                ·
                  refine ⟨7622630813821881339995701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163507751762508453327601 7622630813821881339995701)
                  ·
                    refine ⟨714621638795801375624597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7622630813821881339995701 714621638795801375624597)
                    ·
                      rfl

theorem cell22_2087581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2087581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087581 prefixEnd_2087581 := by exact prefixLift 2087581
  have htrace : WordTrace (prefixWord ++ tailWord_2087581) baseStart_2087581 baseEnd_2087581 := by
    simpa [prefixWord, tailWord_2087581, baseEnd_2087581] using wordTrace_append hprefix tailTrace_2087581
  have hstable : (prefixWord ++ tailWord_2087581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087581).length < 2 ^ (prefixWord ++ tailWord_2087581).sum := by decide
  have hdescent : baseEnd_2087581 < baseStart_2087581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087617 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 5]
def baseStart_2087617 : Nat := 118140960795 + 2087617 * 2 ^ 59
def prefixEnd_2087617 : Nat := 4983230072969 + 3 ^ 40 * 2087617 * 2
def baseEnd_2087617 : Nat := 238211320777169760574829

theorem tailTrace_2087617 : CollatzResearch.WordTrace tailWord_2087617 prefixEnd_2087617 238211320777169760574829 := by
  unfold tailWord_2087617
  simp only [CollatzResearch.WordTrace]
  refine ⟨76141647277927620443381105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50761098185285080295587403 76141647277927620443381105)
  ·
    refine ⟨57106235458445715332535829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76141647277927620443381105 57106235458445715332535829)
    ·
      refine ⟨2676854787114642906212617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57106235458445715332535829 2676854787114642906212617)
      ·
        refine ⟨2007641090335982179659463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676854787114642906212617 2007641090335982179659463)
        ·
          refine ⟨3011461635503973269489195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007641090335982179659463 3011461635503973269489195)
          ·
            refine ⟨4517192453255959904233793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011461635503973269489195 4517192453255959904233793)
            ·
              refine ⟨3387894339941969928175345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517192453255959904233793 3387894339941969928175345)
              ·
                refine ⟨2540920754956477446131509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3387894339941969928175345 2540920754956477446131509)
                ·
                  refine ⟨238211320777169760574829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540920754956477446131509 238211320777169760574829)
                  ·
                    rfl

theorem cell22_2087617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_2087617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087617 prefixEnd_2087617 := by exact prefixLift 2087617
  have htrace : WordTrace (prefixWord ++ tailWord_2087617) baseStart_2087617 baseEnd_2087617 := by
    simpa [prefixWord, tailWord_2087617, baseEnd_2087617] using wordTrace_append hprefix tailTrace_2087617
  have hstable : (prefixWord ++ tailWord_2087617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087617).length < 2 ^ (prefixWord ++ tailWord_2087617).sum := by decide
  have hdescent : baseEnd_2087617 < baseStart_2087617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087641 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_2087641 : Nat := 118140960795 + 2087641 * 2 ^ 59
def prefixEnd_2087641 : Nat := 4983230072969 + 3 ^ 40 * 2087641 * 2
def baseEnd_2087641 : Nat := 714642178021981219124413

theorem tailTrace_2087641 : CollatzResearch.WordTrace tailWord_2087641 prefixEnd_2087641 714642178021981219124413 := by
  unfold tailWord_2087641
  simp only [CollatzResearch.WordTrace]
  refine ⟨76142522629840672542254777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50761681753227115028169851 76142522629840672542254777)
  ·
    refine ⟨57106891972380504406691083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76142522629840672542254777 57106891972380504406691083)
    ·
      refine ⟨85660337958570756610036625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57106891972380504406691083 85660337958570756610036625)
      ·
        refine ⟨64245253468928067457527469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85660337958570756610036625 64245253468928067457527469)
        ·
          refine ⟨24091970050848025296572801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64245253468928067457527469 24091970050848025296572801)
          ·
            refine ⟨18068977538136018972429601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24091970050848025296572801 18068977538136018972429601)
            ·
              refine ⟨13551733153602014229322201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18068977538136018972429601 13551733153602014229322201)
              ·
                refine ⟨10163799865201510671991651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13551733153602014229322201 10163799865201510671991651)
                ·
                  refine ⟨15245699797802266007987477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10163799865201510671991651 15245699797802266007987477)
                  ·
                    refine ⟨714642178021981219124413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15245699797802266007987477 714642178021981219124413)
                    ·
                      rfl

theorem cell22_2087641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_2087641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087641 prefixEnd_2087641 := by exact prefixLift 2087641
  have htrace : WordTrace (prefixWord ++ tailWord_2087641) baseStart_2087641 baseEnd_2087641 := by
    simpa [prefixWord, tailWord_2087641, baseEnd_2087641] using wordTrace_append hprefix tailTrace_2087641
  have hstable : (prefixWord ++ tailWord_2087641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087641).length < 2 ^ (prefixWord ++ tailWord_2087641).sum := by decide
  have hdescent : baseEnd_2087641 < baseStart_2087641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087795 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 2, 3]
def baseStart_2087795 : Nat := 118140960795 + 2087795 * 2 ^ 59
def prefixEnd_2087795 : Nat := 4983230072969 + 3 ^ 40 * 2087795 * 2
def baseEnd_2087795 : Nat := 714694895369176150773941

theorem tailTrace_2087795 : CollatzResearch.WordTrace tailWord_2087795 prefixEnd_2087795 714694895369176150773941 := by
  unfold tailWord_2087795
  simp only [CollatzResearch.WordTrace]
  refine ⟨76148139471282756843360839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50765426314188504562240559 76148139471282756843360839)
  ·
    refine ⟨114222209206924135265041259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76148139471282756843360839 114222209206924135265041259)
    ·
      refine ⟨171333313810386202897561889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114222209206924135265041259 171333313810386202897561889)
      ·
        refine ⟨128499985357789652173171417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171333313810386202897561889 128499985357789652173171417)
        ·
          refine ⟨96374989018342239129878563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128499985357789652173171417 96374989018342239129878563)
          ·
            refine ⟨144562483527513358694817845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96374989018342239129878563 144562483527513358694817845)
            ·
              refine ⟨13552732830704377377639173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144562483527513358694817845 13552732830704377377639173)
              ·
                refine ⟨2541137405757070758307345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13552732830704377377639173 2541137405757070758307345)
                ·
                  refine ⟨1905853054317803068730509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541137405757070758307345 1905853054317803068730509)
                  ·
                    refine ⟨714694895369176150773941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905853054317803068730509 714694895369176150773941)
                    ·
                      rfl

theorem cell22_2087795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 3].length) (baseStart_2087795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087795 prefixEnd_2087795 := by exact prefixLift 2087795
  have htrace : WordTrace (prefixWord ++ tailWord_2087795) baseStart_2087795 baseEnd_2087795 := by
    simpa [prefixWord, tailWord_2087795, baseEnd_2087795] using wordTrace_append hprefix tailTrace_2087795
  have hstable : (prefixWord ++ tailWord_2087795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087795).length < 2 ^ (prefixWord ++ tailWord_2087795).sum := by decide
  have hdescent : baseEnd_2087795 < baseStart_2087795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087797 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 4]
def baseStart_2087797 : Nat := 118140960795 + 2087797 * 2 ^ 59
def prefixEnd_2087797 : Nat := 4983230072969 + 3 ^ 40 * 2087797 * 2
def baseEnd_2087797 : Nat := 238231860003349604074645

theorem tailTrace_2087797 : CollatzResearch.WordTrace tailWord_2087797 prefixEnd_2087797 238231860003349604074645 := by
  unfold tailWord_2087797
  simp only [CollatzResearch.WordTrace]
  refine ⟨76148212417275511184933645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50765474944850340789955763 76148212417275511184933645)
  ·
    refine ⟨28555579656478316694350117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76148212417275511184933645 28555579656478316694350117)
    ·
      refine ⟨5354171185589684380190647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28555579656478316694350117 5354171185589684380190647)
      ·
        refine ⟨8031256778384526570285971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354171185589684380190647 8031256778384526570285971)
        ·
          refine ⟨12046885167576789855428957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031256778384526570285971 12046885167576789855428957)
          ·
            refine ⟨4517581937841296195785859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12046885167576789855428957 4517581937841296195785859)
            ·
              refine ⟨6776372906761944293678789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517581937841296195785859 6776372906761944293678789)
              ·
                refine ⟨1270569920017864555064773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6776372906761944293678789 1270569920017864555064773)
                ·
                  refine ⟨238231860003349604074645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270569920017864555064773 238231860003349604074645)
                  ·
                    rfl

theorem cell22_2087797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_2087797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087797 prefixEnd_2087797 := by exact prefixLift 2087797
  have htrace : WordTrace (prefixWord ++ tailWord_2087797) baseStart_2087797 baseEnd_2087797 := by
    simpa [prefixWord, tailWord_2087797, baseEnd_2087797] using wordTrace_append hprefix tailTrace_2087797
  have hstable : (prefixWord ++ tailWord_2087797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087797).length < 2 ^ (prefixWord ++ tailWord_2087797).sum := by decide
  have hdescent : baseEnd_2087797 < baseStart_2087797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087876 : List Nat := [2, 3, 3, 3, 2, 1, 2, 6]
def baseStart_2087876 : Nat := 118140960795 + 2087876 * 2 ^ 59
def prefixEnd_2087876 : Nat := 4983230072969 + 3 ^ 40 * 2087876 * 2
def baseEnd_2087876 : Nat := 79413624813835437722077

theorem tailTrace_2087876 : CollatzResearch.WordTrace tailWord_2087876 prefixEnd_2087876 79413624813835437722077 := by
  unfold tailWord_2087876
  simp only [CollatzResearch.WordTrace]
  refine ⟨38075546891994653838529741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50767395855992871784706321 38075546891994653838529741)
  ·
    refine ⟨14278330084497995189448653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38075546891994653838529741 14278330084497995189448653)
    ·
      refine ⟨5354373781686748196043245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14278330084497995189448653 5354373781686748196043245)
      ·
        refine ⟨2007890168132530573516217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5354373781686748196043245 2007890168132530573516217)
        ·
          refine ⟨1505917626099397930137163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2007890168132530573516217 1505917626099397930137163)
          ·
            refine ⟨2258876439149096895205745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505917626099397930137163 2258876439149096895205745)
            ·
              refine ⟨1694157329361822671404309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258876439149096895205745 1694157329361822671404309)
              ·
                refine ⟨79413624813835437722077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1694157329361822671404309 79413624813835437722077)
                ·
                  rfl

theorem cell22_2087876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 6].length) (baseStart_2087876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087876 prefixEnd_2087876 := by exact prefixLift 2087876
  have htrace : WordTrace (prefixWord ++ tailWord_2087876) baseStart_2087876 baseEnd_2087876 := by
    simpa [prefixWord, tailWord_2087876, baseEnd_2087876] using wordTrace_append hprefix tailTrace_2087876
  have hstable : (prefixWord ++ tailWord_2087876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087876).length < 2 ^ (prefixWord ++ tailWord_2087876).sum := by decide
  have hdescent : baseEnd_2087876 < baseStart_2087876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087934 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2087934 : Nat := 118140960795 + 2087934 * 2 ^ 59
def prefixEnd_2087934 : Nat := 4983230072969 + 3 ^ 40 * 2087934 * 2
def baseEnd_2087934 : Nat := 714742477909826121548515

theorem tailTrace_2087934 : CollatzResearch.WordTrace tailWord_2087934 prefixEnd_2087934 714742477909826121548515 := by
  unfold tailWord_2087934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9519151152222397947833857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50768806145186122388447237 9519151152222397947833857)
  ·
    refine ⟨7139363364166798460875393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9519151152222397947833857 7139363364166798460875393)
    ·
      refine ⟨5354522523125098845656545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7139363364166798460875393 5354522523125098845656545)
      ·
        refine ⟨4015891892343824134242409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5354522523125098845656545 4015891892343824134242409)
        ·
          refine ⟨3011918919257868100681807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4015891892343824134242409 3011918919257868100681807)
          ·
            refine ⟨4517878378886802151022711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011918919257868100681807 4517878378886802151022711)
            ·
              refine ⟨6776817568330203226534067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517878378886802151022711 6776817568330203226534067)
              ·
                refine ⟨10165226352495304839801101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776817568330203226534067 10165226352495304839801101)
                ·
                  refine ⟨3811959882185739314925413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10165226352495304839801101 3811959882185739314925413)
                  ·
                    refine ⟨714742477909826121548515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3811959882185739314925413 714742477909826121548515)
                    ·
                      rfl

theorem cell22_2087934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2087934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087934 prefixEnd_2087934 := by exact prefixLift 2087934
  have htrace : WordTrace (prefixWord ++ tailWord_2087934) baseStart_2087934 baseEnd_2087934 := by
    simpa [prefixWord, tailWord_2087934, baseEnd_2087934] using wordTrace_append hprefix tailTrace_2087934
  have hstable : (prefixWord ++ tailWord_2087934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087934).length < 2 ^ (prefixWord ++ tailWord_2087934).sum := by decide
  have hdescent : baseEnd_2087934 < baseStart_2087934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087992 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_2087992 : Nat := 118140960795 + 2087992 * 2 ^ 59
def prefixEnd_2087992 : Nat := 4983230072969 + 3 ^ 40 * 2087992 * 2
def baseEnd_2087992 : Nat := 714762332495133303598337

theorem tailTrace_2087992 : CollatzResearch.WordTrace tailWord_2087992 prefixEnd_2087992 714762332495133303598337 := by
  unfold tailWord_2087992
  simp only [CollatzResearch.WordTrace]
  refine ⟨38077662325784529744141115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50770216434379372992188153 38077662325784529744141115)
  ·
    refine ⟨57116493488676794616211673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38077662325784529744141115 57116493488676794616211673)
    ·
      refine ⟨42837370116507595962158755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57116493488676794616211673 42837370116507595962158755)
      ·
        refine ⟨64256055174761393943238133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42837370116507595962158755 64256055174761393943238133)
        ·
          refine ⟨6024005172633880682178575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64256055174761393943238133 6024005172633880682178575)
          ·
            refine ⟨9036007758950821023267863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024005172633880682178575 9036007758950821023267863)
            ·
              refine ⟨13554011638426231534901795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036007758950821023267863 13554011638426231534901795)
              ·
                refine ⟨20331017457639347302352693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13554011638426231534901795 20331017457639347302352693)
                ·
                  refine ⟨1906032886653688809595565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20331017457639347302352693 1906032886653688809595565)
                  ·
                    refine ⟨714762332495133303598337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906032886653688809595565 714762332495133303598337)
                    ·
                      rfl

theorem cell22_2087992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_2087992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087992 prefixEnd_2087992 := by exact prefixLift 2087992
  have htrace : WordTrace (prefixWord ++ tailWord_2087992) baseStart_2087992 baseEnd_2087992 := by
    simpa [prefixWord, tailWord_2087992, baseEnd_2087992] using wordTrace_append hprefix tailTrace_2087992
  have hstable : (prefixWord ++ tailWord_2087992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087992).length < 2 ^ (prefixWord ++ tailWord_2087992).sum := by decide
  have hdescent : baseEnd_2087992 < baseStart_2087992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088039 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 5]
def baseStart_2088039 : Nat := 118140960795 + 2088039 * 2 ^ 59
def prefixEnd_2088039 : Nat := 4983230072969 + 3 ^ 40 * 2088039 * 2
def baseEnd_2088039 : Nat := 238259473851880282557731

theorem tailTrace_2088039 : CollatzResearch.WordTrace tailWord_2088039 prefixEnd_2088039 238259473851880282557731 := by
  unfold tailWord_2088039
  simp only [CollatzResearch.WordTrace]
  refine ⟨76157038882398786515243171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50771359254932524343495447 76157038882398786515243171)
  ·
    refine ⟨114235558323598179772864757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76157038882398786515243171 114235558323598179772864757)
    ·
      refine ⟨10709583592837329353706071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114235558323598179772864757 10709583592837329353706071)
      ·
        refine ⟨16064375389255994030559107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10709583592837329353706071 16064375389255994030559107)
        ·
          refine ⟨24096563083883991045838661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16064375389255994030559107 24096563083883991045838661)
          ·
            refine ⟨4518105578228248321094749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24096563083883991045838661 4518105578228248321094749)
            ·
              refine ⟨1694289591835593120410531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4518105578228248321094749 1694289591835593120410531)
              ·
                refine ⟨2541434387753389680615797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694289591835593120410531 2541434387753389680615797)
                ·
                  refine ⟨238259473851880282557731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2541434387753389680615797 238259473851880282557731)
                  ·
                    rfl

theorem cell22_2088039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 5].length) (baseStart_2088039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088039 prefixEnd_2088039 := by exact prefixLift 2088039
  have htrace : WordTrace (prefixWord ++ tailWord_2088039) baseStart_2088039 baseEnd_2088039 := by
    simpa [prefixWord, tailWord_2088039, baseEnd_2088039] using wordTrace_append hprefix tailTrace_2088039
  have hstable : (prefixWord ++ tailWord_2088039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088039).length < 2 ^ (prefixWord ++ tailWord_2088039).sum := by decide
  have hdescent : baseEnd_2088039 < baseStart_2088039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088080 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_2088080 : Nat := 118140960795 + 2088080 * 2 ^ 59
def prefixEnd_2088080 : Nat := 4983230072969 + 3 ^ 40 * 2088080 * 2
def baseEnd_2088080 : Nat := 714792456693530407398067

theorem tailTrace_2088080 : CollatzResearch.WordTrace tailWord_2088080 prefixEnd_2088080 714792456693530407398067 := by
  unfold tailWord_2088080
  simp only [CollatzResearch.WordTrace]
  refine ⟨38079267137625125258742847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50772356183500167011657129 38079267137625125258742847)
  ·
    refine ⟨57118900706437687888114271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38079267137625125258742847 57118900706437687888114271)
    ·
      refine ⟨85678351059656531832171407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57118900706437687888114271 85678351059656531832171407)
      ·
        refine ⟨128517526589484797748257111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85678351059656531832171407 128517526589484797748257111)
        ·
          refine ⟨192776289884227196622385667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128517526589484797748257111 192776289884227196622385667)
          ·
            refine ⟨289164434826340794933578501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192776289884227196622385667 289164434826340794933578501)
            ·
              refine ⟨54218331529938899050045969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289164434826340794933578501 54218331529938899050045969)
              ·
                refine ⟨40663748647454174287534477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54218331529938899050045969 40663748647454174287534477)
                ·
                  refine ⟨15248905742795315357825429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40663748647454174287534477 15248905742795315357825429)
                  ·
                    refine ⟨714792456693530407398067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15248905742795315357825429 714792456693530407398067)
                    ·
                      rfl

theorem cell22_2088080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_2088080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088080 prefixEnd_2088080 := by exact prefixLift 2088080
  have htrace : WordTrace (prefixWord ++ tailWord_2088080) baseStart_2088080 baseEnd_2088080 := by
    simpa [prefixWord, tailWord_2088080, baseEnd_2088080] using wordTrace_append hprefix tailTrace_2088080
  have hstable : (prefixWord ++ tailWord_2088080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088080).length < 2 ^ (prefixWord ++ tailWord_2088080).sum := by decide
  have hdescent : baseEnd_2088080 < baseStart_2088080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088097 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2088097 : Nat := 118140960795 + 2088097 * 2 ^ 59
def prefixEnd_2088097 : Nat := 4983230072969 + 3 ^ 40 * 2088097 * 2
def baseEnd_2088097 : Nat := 714798276140948029723015

theorem tailTrace_2088097 : CollatzResearch.WordTrace tailWord_2088097 prefixEnd_2088097 714798276140948029723015 := by
  unfold tailWord_2088097
  simp only [CollatzResearch.WordTrace]
  refine ⟨76159154316188662420854545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50772769544125774947236363 76159154316188662420854545)
  ·
    refine ⟨57119365737141496815640909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76159154316188662420854545 57119365737141496815640909)
    ·
      refine ⟨21419762151428061305865341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57119365737141496815640909 21419762151428061305865341)
      ·
        refine ⟨8032410806785522989699503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21419762151428061305865341 8032410806785522989699503)
        ·
          refine ⟨12048616210178284484549255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032410806785522989699503 12048616210178284484549255)
          ·
            refine ⟨18072924315267426726823883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048616210178284484549255 18072924315267426726823883)
            ·
              refine ⟨27109386472901140090235825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18072924315267426726823883 27109386472901140090235825)
              ·
                refine ⟨20332039854675855067676869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27109386472901140090235825 20332039854675855067676869)
                ·
                  refine ⟨3812257472751722825189413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20332039854675855067676869 3812257472751722825189413)
                  ·
                    refine ⟨714798276140948029723015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3812257472751722825189413 714798276140948029723015)
                    ·
                      rfl

theorem cell22_2088097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2088097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088097 prefixEnd_2088097 := by exact prefixLift 2088097
  have htrace : WordTrace (prefixWord ++ tailWord_2088097) baseStart_2088097 baseEnd_2088097 := by
    simpa [prefixWord, tailWord_2088097, baseEnd_2088097] using wordTrace_append hprefix tailTrace_2088097
  have hstable : (prefixWord ++ tailWord_2088097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088097).length < 2 ^ (prefixWord ++ tailWord_2088097).sum := by decide
  have hdescent : baseEnd_2088097 < baseStart_2088097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088114 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_2088114 : Nat := 118140960795 + 2088114 * 2 ^ 59
def prefixEnd_2088114 : Nat := 4983230072969 + 3 ^ 40 * 2088114 * 2
def baseEnd_2088114 : Nat := 714804095588365652047963

theorem tailTrace_2088114 : CollatzResearch.WordTrace tailWord_2088114 prefixEnd_2088114 714804095588365652047963 := by
  unfold tailWord_2088114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039943589281768581055849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50773182904751382882815597 19039943589281768581055849)
  ·
    refine ⟨14279957691961326435791887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19039943589281768581055849 14279957691961326435791887)
    ·
      refine ⟨21419936537941989653687831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279957691961326435791887 21419936537941989653687831)
      ·
        refine ⟨32129904806912984480531747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21419936537941989653687831 32129904806912984480531747)
        ·
          refine ⟨48194857210369476720797621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32129904806912984480531747 48194857210369476720797621)
          ·
            refine ⟨4518267863472138442574777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48194857210369476720797621 4518267863472138442574777)
            ·
              refine ⟨3388700897604103831931083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4518267863472138442574777 3388700897604103831931083)
              ·
                refine ⟨5083051346406155747896625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388700897604103831931083 5083051346406155747896625)
                ·
                  refine ⟨3812288509804616810922469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083051346406155747896625 3812288509804616810922469)
                  ·
                    refine ⟨714804095588365652047963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3812288509804616810922469 714804095588365652047963)
                    ·
                      rfl

theorem cell22_2088114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_2088114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088114 prefixEnd_2088114 := by exact prefixLift 2088114
  have htrace : WordTrace (prefixWord ++ tailWord_2088114) baseStart_2088114 baseEnd_2088114 := by
    simpa [prefixWord, tailWord_2088114, baseEnd_2088114] using wordTrace_append hprefix tailTrace_2088114
  have hstable : (prefixWord ++ tailWord_2088114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088114).length < 2 ^ (prefixWord ++ tailWord_2088114).sum := by decide
  have hdescent : baseEnd_2088114 < baseStart_2088114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088221 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2088221 : Nat := 118140960795 + 2088221 * 2 ^ 59
def prefixEnd_2088221 : Nat := 4983230072969 + 3 ^ 40 * 2088221 * 2
def baseEnd_2088221 : Nat := 714840723875053039622635

theorem tailTrace_2088221 : CollatzResearch.WordTrace tailWord_2088221 prefixEnd_2088221 714840723875053039622635 := by
  unfold tailWord_2088221
  simp only [CollatzResearch.WordTrace]
  refine ⟨76163676967739431598368517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50775784645159621065579011 76163676967739431598368517)
  ·
    refine ⟨14280689431451143424694097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76163676967739431598368517 14280689431451143424694097)
    ·
      refine ⟨10710517073588357568520573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14280689431451143424694097 10710517073588357568520573)
      ·
        refine ⟨4016443902595634088195215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10710517073588357568520573 4016443902595634088195215)
        ·
          refine ⟨6024665853893451132292823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016443902595634088195215 6024665853893451132292823)
          ·
            refine ⟨9036998780840176698439235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024665853893451132292823 9036998780840176698439235)
            ·
              refine ⟨13555498171260265047658853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036998780840176698439235 13555498171260265047658853)
              ·
                refine ⟨2541655907111299696436035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13555498171260265047658853 2541655907111299696436035)
                ·
                  refine ⟨3812483860666949544654053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541655907111299696436035 3812483860666949544654053)
                  ·
                    refine ⟨714840723875053039622635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3812483860666949544654053 714840723875053039622635)
                    ·
                      rfl

theorem cell22_2088221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2088221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088221 prefixEnd_2088221 := by exact prefixLift 2088221
  have htrace : WordTrace (prefixWord ++ tailWord_2088221) baseStart_2088221 baseEnd_2088221 := by
    simpa [prefixWord, tailWord_2088221, baseEnd_2088221] using wordTrace_append hprefix tailTrace_2088221
  have hstable : (prefixWord ++ tailWord_2088221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088221).length < 2 ^ (prefixWord ++ tailWord_2088221).sum := by decide
  have hdescent : baseEnd_2088221 < baseStart_2088221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088253 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 6]
def baseStart_2088253 : Nat := 118140960795 + 2088253 * 2 ^ 59
def prefixEnd_2088253 : Nat := 4983230072969 + 3 ^ 40 * 2088253 * 2
def baseEnd_2088253 : Nat := 238283892709671874274179

theorem tailTrace_2088253 : CollatzResearch.WordTrace tailWord_2088253 prefixEnd_2088253 238283892709671874274179 := by
  unfold tailWord_2088253
  simp only [CollatzResearch.WordTrace]
  refine ⟨76164844103623501063533413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50776562735749000709022275 76164844103623501063533413)
  ·
    refine ⟨14280908269429406449412515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76164844103623501063533413 14280908269429406449412515)
    ·
      refine ⟨21421362404144109674118773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14280908269429406449412515 21421362404144109674118773)
      ·
        refine ⟨2008252725388510281948635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21421362404144109674118773 2008252725388510281948635)
        ·
          refine ⟨3012379088082765422922953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008252725388510281948635 3012379088082765422922953)
          ·
            refine ⟨2259284316062074067192215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012379088082765422922953 2259284316062074067192215)
            ·
              refine ⟨3388926474093111100788323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259284316062074067192215 3388926474093111100788323)
              ·
                refine ⟨5083389711139666651182485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388926474093111100788323 5083389711139666651182485)
                ·
                  refine ⟨238283892709671874274179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5083389711139666651182485 238283892709671874274179)
                  ·
                    rfl

theorem cell22_2088253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_2088253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088253 prefixEnd_2088253 := by exact prefixLift 2088253
  have htrace : WordTrace (prefixWord ++ tailWord_2088253) baseStart_2088253 baseEnd_2088253 := by
    simpa [prefixWord, tailWord_2088253, baseEnd_2088253] using wordTrace_append hprefix tailTrace_2088253
  have hstable : (prefixWord ++ tailWord_2088253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088253).length < 2 ^ (prefixWord ++ tailWord_2088253).sum := by decide
  have hdescent : baseEnd_2088253 < baseStart_2088253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088268 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_2088268 : Nat := 118140960795 + 2088268 * 2 ^ 59
def prefixEnd_2088268 : Nat := 4983230072969 + 3 ^ 40 * 2088268 * 2
def baseEnd_2088268 : Nat := 714856812935560583697491

theorem tailTrace_2088268 : CollatzResearch.WordTrace tailWord_2088268 prefixEnd_2088268 714856812935560583697491 := by
  unfold tailWord_2088268
  simp only [CollatzResearch.WordTrace]
  refine ⟨38082695599284579312664729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50776927465712772416886305 38082695599284579312664729)
  ·
    refine ⟨28562021699463434484498547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38082695599284579312664729 28562021699463434484498547)
    ·
      refine ⟨42843032549195151726747821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28562021699463434484498547 42843032549195151726747821)
      ·
        refine ⟨16066137205948181897530433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42843032549195151726747821 16066137205948181897530433)
        ·
          refine ⟨12049602904461136423147825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16066137205948181897530433 12049602904461136423147825)
          ·
            refine ⟨9037202178345852317360869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12049602904461136423147825 9037202178345852317360869)
            ·
              refine ⟨1694475408439847309505163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9037202178345852317360869 1694475408439847309505163)
              ·
                refine ⟨2541713112659770964257745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694475408439847309505163 2541713112659770964257745)
                ·
                  refine ⟨1906284834494828223193309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541713112659770964257745 1906284834494828223193309)
                  ·
                    refine ⟨714856812935560583697491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906284834494828223193309 714856812935560583697491)
                    ·
                      rfl

theorem cell22_2088268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_2088268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088268 prefixEnd_2088268 := by exact prefixLift 2088268
  have htrace : WordTrace (prefixWord ++ tailWord_2088268) baseStart_2088268 baseEnd_2088268 := by
    simpa [prefixWord, tailWord_2088268, baseEnd_2088268] using wordTrace_append hprefix tailTrace_2088268
  have hstable : (prefixWord ++ tailWord_2088268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088268).length < 2 ^ (prefixWord ++ tailWord_2088268).sum := by decide
  have hdescent : baseEnd_2088268 < baseStart_2088268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088285 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2088285 : Nat := 118140960795 + 2088285 * 2 ^ 59
def prefixEnd_2088285 : Nat := 4983230072969 + 3 ^ 40 * 2088285 * 2
def baseEnd_2088285 : Nat := 714862632382978206022439

theorem tailTrace_2088285 : CollatzResearch.WordTrace tailWord_2088285 prefixEnd_2088285 714862632382978206022439 := by
  unfold tailWord_2088285
  simp only [CollatzResearch.WordTrace]
  refine ⟨76166011239507570528698309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50777340826338380352465539 76166011239507570528698309)
  ·
    refine ⟨14281127107407669474130933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76166011239507570528698309 14281127107407669474130933)
    ·
      refine ⟨1338855666319469013199775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14281127107407669474130933 1338855666319469013199775)
      ·
        refine ⟨2008283499479203519799663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338855666319469013199775 2008283499479203519799663)
        ·
          refine ⟨3012425249218805279699495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008283499479203519799663 3012425249218805279699495)
          ·
            refine ⟨4518637873828207919549243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012425249218805279699495 4518637873828207919549243)
            ·
              refine ⟨6777956810742311879323865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518637873828207919549243 6777956810742311879323865)
              ·
                refine ⟨5083467608056733909492899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6777956810742311879323865 5083467608056733909492899)
                ·
                  refine ⟨7625201412085100864239349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083467608056733909492899 7625201412085100864239349)
                  ·
                    refine ⟨714862632382978206022439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7625201412085100864239349 714862632382978206022439)
                    ·
                      rfl

theorem cell22_2088285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2088285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088285 prefixEnd_2088285 := by exact prefixLift 2088285
  have htrace : WordTrace (prefixWord ++ tailWord_2088285) baseStart_2088285 baseEnd_2088285 := by
    simpa [prefixWord, tailWord_2088285, baseEnd_2088285] using wordTrace_append hprefix tailTrace_2088285
  have hstable : (prefixWord ++ tailWord_2088285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088285).length < 2 ^ (prefixWord ++ tailWord_2088285).sum := by decide
  have hdescent : baseEnd_2088285 < baseStart_2088285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088324 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2088324 : Nat := 118140960795 + 2088324 * 2 ^ 59
def prefixEnd_2088324 : Nat := 4983230072969 + 3 ^ 40 * 2088324 * 2
def baseEnd_2088324 : Nat := 714875982879995104297319

theorem tailTrace_2088324 : CollatzResearch.WordTrace tailWord_2088324 prefixEnd_2088324 714875982879995104297319 := by
  unfold tailWord_2088324
  simp only [CollatzResearch.WordTrace]
  refine ⟨38083716843183140094684013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50778289124244186792912017 38083716843183140094684013)
  ·
    refine ⟨14281393816193677535506505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38083716843183140094684013 14281393816193677535506505)
    ·
      refine ⟨10711045362145258151629879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14281393816193677535506505 10711045362145258151629879)
      ·
        refine ⟨16066568043217887227444819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711045362145258151629879 16066568043217887227444819)
        ·
          refine ⟨24099852064826830841167229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066568043217887227444819 24099852064826830841167229)
          ·
            refine ⟨9037444524310061565437711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24099852064826830841167229 9037444524310061565437711)
            ·
              refine ⟨13556166786465092348156567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037444524310061565437711 13556166786465092348156567)
              ·
                refine ⟨20334250179697638522234851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13556166786465092348156567 20334250179697638522234851)
                ·
                  refine ⟨30501375269546457783352277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20334250179697638522234851 30501375269546457783352277)
                  ·
                    refine ⟨714875982879995104297319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30501375269546457783352277 714875982879995104297319)
                    ·
                      rfl

theorem cell22_2088324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2088324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088324 prefixEnd_2088324 := by exact prefixLift 2088324
  have htrace : WordTrace (prefixWord ++ tailWord_2088324) baseStart_2088324 baseEnd_2088324 := by
    simpa [prefixWord, tailWord_2088324, baseEnd_2088324] using wordTrace_append hprefix tailTrace_2088324
  have hstable : (prefixWord ++ tailWord_2088324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088324).length < 2 ^ (prefixWord ++ tailWord_2088324).sum := by decide
  have hdescent : baseEnd_2088324 < baseStart_2088324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088360 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 5]
def baseStart_2088360 : Nat := 118140960795 + 2088360 * 2 ^ 59
def prefixEnd_2088360 : Nat := 4983230072969 + 3 ^ 40 * 2088360 * 2
def baseEnd_2088360 : Nat := 238296102138567670132403

theorem tailTrace_2088360 : CollatzResearch.WordTrace tailWord_2088360 prefixEnd_2088360 238296102138567670132403 := by
  unfold tailWord_2088360
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084373357117929168839267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50779164476157238891785689 38084373357117929168839267)
  ·
    refine ⟨57126560035676893753258901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38084373357117929168839267 57126560035676893753258901)
    ·
      refine ⟨2677807501672354394684011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57126560035676893753258901 2677807501672354394684011)
      ·
        refine ⟨4016711252508531592026017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677807501672354394684011 4016711252508531592026017)
        ·
          refine ⟨3012533439381398694019513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4016711252508531592026017 3012533439381398694019513)
          ·
            refine ⟨2259400079536049020514635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012533439381398694019513 2259400079536049020514635)
            ·
              refine ⟨3389100119304073530771953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259400079536049020514635 3389100119304073530771953)
              ·
                refine ⟨2541825089478055148078965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3389100119304073530771953 2541825089478055148078965)
                ·
                  refine ⟨238296102138567670132403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2541825089478055148078965 238296102138567670132403)
                  ·
                    rfl

theorem cell22_2088360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_2088360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088360 prefixEnd_2088360 := by exact prefixLift 2088360
  have htrace : WordTrace (prefixWord ++ tailWord_2088360) baseStart_2088360 baseEnd_2088360 := by
    simpa [prefixWord, tailWord_2088360, baseEnd_2088360] using wordTrace_append hprefix tailTrace_2088360
  have hstable : (prefixWord ++ tailWord_2088360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088360).length < 2 ^ (prefixWord ++ tailWord_2088360).sum := by decide
  have hdescent : baseEnd_2088360 < baseStart_2088360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088384 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_2088384 : Nat := 118140960795 + 2088384 * 2 ^ 59
def prefixEnd_2088384 : Nat := 4983230072969 + 3 ^ 40 * 2088384 * 2
def baseEnd_2088384 : Nat := 714896522106174947797135

theorem tailTrace_2088384 : CollatzResearch.WordTrace tailWord_2088384 prefixEnd_2088384 714896522106174947797135 := by
  unfold tailWord_2088384
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084811033074455218276103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50779748044099273624368137 38084811033074455218276103)
  ·
    refine ⟨57127216549611682827414155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38084811033074455218276103 57127216549611682827414155)
    ·
      refine ⟨85690824824417524241121233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57127216549611682827414155 85690824824417524241121233)
      ·
        refine ⟨64268118618313143180840925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85690824824417524241121233 64268118618313143180840925)
        ·
          refine ⟨24100544481867428692815347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64268118618313143180840925 24100544481867428692815347)
          ·
            refine ⟨36150816722801143039223021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24100544481867428692815347 36150816722801143039223021)
            ·
              refine ⟨13556556271050428639708633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36150816722801143039223021 13556556271050428639708633)
              ·
                refine ⟨10167417203287821479781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13556556271050428639708633 10167417203287821479781475)
                ·
                  refine ⟨15251125804931732219672213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10167417203287821479781475 15251125804931732219672213)
                  ·
                    refine ⟨714896522106174947797135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15251125804931732219672213 714896522106174947797135)
                    ·
                      rfl

theorem cell22_2088384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_2088384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088384 prefixEnd_2088384 := by exact prefixLift 2088384
  have htrace : WordTrace (prefixWord ++ tailWord_2088384) baseStart_2088384 baseEnd_2088384 := by
    simpa [prefixWord, tailWord_2088384, baseEnd_2088384] using wordTrace_append hprefix tailTrace_2088384
  have hstable : (prefixWord ++ tailWord_2088384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088384).length < 2 ^ (prefixWord ++ tailWord_2088384).sum := by decide
  have hdescent : baseEnd_2088384 < baseStart_2088384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088437 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2088437 : Nat := 118140960795 + 2088437 * 2 ^ 59
def prefixEnd_2088437 : Nat := 4983230072969 + 3 ^ 40 * 2088437 * 2
def baseEnd_2088437 : Nat := 714914665089300476221973

theorem tailTrace_2088437 : CollatzResearch.WordTrace tailWord_2088437 prefixEnd_2088437 714914665089300476221973 := by
  unfold tailWord_2088437
  simp only [CollatzResearch.WordTrace]
  refine ⟨76171555134956900488231565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50781036756637933658821043 76171555134956900488231565)
  ·
    refine ⟨28564333175608837683086837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76171555134956900488231565 28564333175608837683086837)
    ·
      refine ⟨2677906235213328532789391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28564333175608837683086837 2677906235213328532789391)
      ·
        refine ⟨4016859352819992799184087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677906235213328532789391 4016859352819992799184087)
        ·
          refine ⟨6025289029229989198776131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016859352819992799184087 6025289029229989198776131)
          ·
            refine ⟨9037933543844983798164197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025289029229989198776131 9037933543844983798164197)
            ·
              refine ⟨1694612539470934462155787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9037933543844983798164197 1694612539470934462155787)
              ·
                refine ⟨2541918809206401693233681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694612539470934462155787 2541918809206401693233681)
                ·
                  refine ⟨1906439106904801269925261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541918809206401693233681 1906439106904801269925261)
                  ·
                    refine ⟨714914665089300476221973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906439106904801269925261 714914665089300476221973)
                    ·
                      rfl

theorem cell22_2088437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2088437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088437 prefixEnd_2088437 := by exact prefixLift 2088437
  have htrace : WordTrace (prefixWord ++ tailWord_2088437) baseStart_2088437 baseEnd_2088437 := by
    simpa [prefixWord, tailWord_2088437, baseEnd_2088437] using wordTrace_append hprefix tailTrace_2088437
  have hstable : (prefixWord ++ tailWord_2088437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088437).length < 2 ^ (prefixWord ++ tailWord_2088437).sum := by decide
  have hdescent : baseEnd_2088437 < baseStart_2088437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088476 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2088476 : Nat := 118140960795 + 2088476 * 2 ^ 59
def prefixEnd_2088476 : Nat := 4983230072969 + 3 ^ 40 * 2088476 * 2
def baseEnd_2088476 : Nat := 714928015586317374496853

theorem tailTrace_2088476 : CollatzResearch.WordTrace tailWord_2088476 prefixEnd_2088476 714928015586317374496853 := by
  unfold tailWord_2088476
  simp only [CollatzResearch.WordTrace]
  refine ⟨38086488790907805074450641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50781985054543740099267521 38086488790907805074450641)
  ·
    refine ⟨28564866593180853805837981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38086488790907805074450641 28564866593180853805837981)
    ·
      refine ⟨10711824972442820177189243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28564866593180853805837981 10711824972442820177189243)
      ·
        refine ⟨16067737458664230265783865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711824972442820177189243 16067737458664230265783865)
        ·
          refine ⟨12050803093998172699337899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16067737458664230265783865 12050803093998172699337899)
          ·
            refine ⟨18076204640997259049006849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050803093998172699337899 18076204640997259049006849)
            ·
              refine ⟨13557153480747944286755137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18076204640997259049006849 13557153480747944286755137)
              ·
                refine ⟨10167865110560958215066353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13557153480747944286755137 10167865110560958215066353)
                ·
                  refine ⟨7625898832920718661299765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10167865110560958215066353 7625898832920718661299765)
                  ·
                    refine ⟨714928015586317374496853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7625898832920718661299765 714928015586317374496853)
                    ·
                      rfl

theorem cell22_2088476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2088476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088476 prefixEnd_2088476 := by exact prefixLift 2088476
  have htrace : WordTrace (prefixWord ++ tailWord_2088476) baseStart_2088476 baseEnd_2088476 := by
    simpa [prefixWord, tailWord_2088476, baseEnd_2088476] using wordTrace_append hprefix tailTrace_2088476
  have hstable : (prefixWord ++ tailWord_2088476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088476).length < 2 ^ (prefixWord ++ tailWord_2088476).sum := by decide
  have hdescent : baseEnd_2088476 < baseStart_2088476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088482 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2088482 : Nat := 118140960795 + 2088482 * 2 ^ 59
def prefixEnd_2088482 : Nat := 4983230072969 + 3 ^ 40 * 2088482 * 2
def baseEnd_2088482 : Nat := 714930069508935358846835

theorem tailTrace_2088482 : CollatzResearch.WordTrace tailWord_2088482 prefixEnd_2088482 714930069508935358846835 := by
  unfold tailWord_2088482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19043299104948468293404925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50782130946529248782413133 19043299104948468293404925)
  ·
    refine ⟨7141237164355675610026847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19043299104948468293404925 7141237164355675610026847)
    ·
      refine ⟨10711855746533513415040271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7141237164355675610026847 10711855746533513415040271)
      ·
        refine ⟨16067783619800270122560407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711855746533513415040271 16067783619800270122560407)
        ·
          refine ⟨24101675429700405183840611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16067783619800270122560407 24101675429700405183840611)
          ·
            refine ⟨36152513144550607775760917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24101675429700405183840611 36152513144550607775760917)
            ·
              refine ⟨1694649053650809739488793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36152513144550607775760917 1694649053650809739488793)
              ·
                refine ⟨1270986790238107304616595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694649053650809739488793 1270986790238107304616595)
                ·
                  refine ⟨1906480185357160956924893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270986790238107304616595 1906480185357160956924893)
                  ·
                    refine ⟨714930069508935358846835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906480185357160956924893 714930069508935358846835)
                    ·
                      rfl

theorem cell22_2088482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2088482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088482 prefixEnd_2088482 := by exact prefixLift 2088482
  have htrace : WordTrace (prefixWord ++ tailWord_2088482) baseStart_2088482 baseEnd_2088482 := by
    simpa [prefixWord, tailWord_2088482, baseEnd_2088482] using wordTrace_append hprefix tailTrace_2088482
  have hstable : (prefixWord ++ tailWord_2088482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088482).length < 2 ^ (prefixWord ++ tailWord_2088482).sum := by decide
  have hdescent : baseEnd_2088482 < baseStart_2088482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088506 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_2088506 : Nat := 118140960795 + 2088506 * 2 ^ 59
def prefixEnd_2088506 : Nat := 4983230072969 + 3 ^ 40 * 2088506 * 2
def baseEnd_2088506 : Nat := 238312761733135765415587

theorem tailTrace_2088506 : CollatzResearch.WordTrace tailWord_2088506 prefixEnd_2088506 238312761733135765415587 := by
  unfold tailWord_2088506
  simp only [CollatzResearch.WordTrace]
  refine ⟨19043517942926731318123343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50782714514471283514995581 19043517942926731318123343)
  ·
    refine ⟨28565276914390096977185015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19043517942926731318123343 28565276914390096977185015)
    ·
      refine ⟨42847915371585145465777523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28565276914390096977185015 42847915371585145465777523)
      ·
        refine ⟨64271873057377718198666285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42847915371585145465777523 64271873057377718198666285)
        ·
          refine ⟨24101952396516644324499857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64271873057377718198666285 24101952396516644324499857)
          ·
            refine ⟨18076464297387483243374893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24101952396516644324499857 18076464297387483243374893)
            ·
              refine ⟨6778674111520306216265585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18076464297387483243374893 6778674111520306216265585)
              ·
                refine ⟨5084005583640229662199189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778674111520306216265585 5084005583640229662199189)
                ·
                  refine ⟨238312761733135765415587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5084005583640229662199189 238312761733135765415587)
                  ·
                    rfl

theorem cell22_2088506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_2088506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088506 prefixEnd_2088506 := by exact prefixLift 2088506
  have htrace : WordTrace (prefixWord ++ tailWord_2088506) baseStart_2088506 baseEnd_2088506 := by
    simpa [prefixWord, tailWord_2088506, baseEnd_2088506] using wordTrace_append hprefix tailTrace_2088506
  have hstable : (prefixWord ++ tailWord_2088506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088506).length < 2 ^ (prefixWord ++ tailWord_2088506).sum := by decide
  have hdescent : baseEnd_2088506 < baseStart_2088506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088536 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_2088536 : Nat := 118140960795 + 2088536 * 2 ^ 59
def prefixEnd_2088536 : Nat := 4983230072969 + 3 ^ 40 * 2088536 * 2
def baseEnd_2088536 : Nat := 714948554812497217996669

theorem tailTrace_2088536 : CollatzResearch.WordTrace tailWord_2088536 prefixEnd_2088536 714948554812497217996669 := by
  unfold tailWord_2088536
  simp only [CollatzResearch.WordTrace]
  refine ⟨38087582980799120198042731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50783443974398826930723641 38087582980799120198042731)
  ·
    refine ⟨57131374471198680297064097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38087582980799120198042731 57131374471198680297064097)
    ·
      refine ⟨42848530853399010222798073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57131374471198680297064097 42848530853399010222798073)
      ·
        refine ⟨32136398140049257667098555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42848530853399010222798073 32136398140049257667098555)
        ·
          refine ⟨48204597210073886500647833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32136398140049257667098555 48204597210073886500647833)
          ·
            refine ⟨36153447907555414875485875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48204597210073886500647833 36153447907555414875485875)
            ·
              refine ⟨54230171861333122313228813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36153447907555414875485875 54230171861333122313228813)
              ·
                refine ⟨20336314447999920867460805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54230171861333122313228813 20336314447999920867460805)
                ·
                  refine ⟨3813058958999985162648901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20336314447999920867460805 3813058958999985162648901)
                  ·
                    refine ⟨714948554812497217996669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813058958999985162648901 714948554812497217996669)
                    ·
                      rfl

theorem cell22_2088536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_2088536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088536 prefixEnd_2088536 := by exact prefixLift 2088536
  have htrace : WordTrace (prefixWord ++ tailWord_2088536) baseStart_2088536 baseEnd_2088536 := by
    simpa [prefixWord, tailWord_2088536, baseEnd_2088536] using wordTrace_append hprefix tailTrace_2088536
  have hstable : (prefixWord ++ tailWord_2088536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088536).length < 2 ^ (prefixWord ++ tailWord_2088536).sum := by decide
  have hdescent : baseEnd_2088536 < baseStart_2088536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088540 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 4]
def baseStart_2088540 : Nat := 118140960795 + 2088540 * 2 ^ 59
def prefixEnd_2088540 : Nat := 4983230072969 + 3 ^ 40 * 2088540 * 2
def baseEnd_2088540 : Nat := 238316641364747513632219

theorem tailTrace_2088540 : CollatzResearch.WordTrace tailWord_2088540 prefixEnd_2088540 238316641364747513632219 := by
  unfold tailWord_2088540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38087655926791874539615537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50783541235722499386154049 38087655926791874539615537)
  ·
    refine ⟨28565741945093905904711653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38087655926791874539615537 28565741945093905904711653)
    ·
      refine ⟨5356076614705107357133435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28565741945093905904711653 5356076614705107357133435)
      ·
        refine ⟨8034114922057661035700153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356076614705107357133435 8034114922057661035700153)
        ·
          refine ⟨6025586191543245776775115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8034114922057661035700153 6025586191543245776775115)
          ·
            refine ⟨9038379287314868665162673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025586191543245776775115 9038379287314868665162673)
            ·
              refine ⟨6778784465486151498872005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9038379287314868665162673 6778784465486151498872005)
              ·
                refine ⟨1271022087278653406038501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6778784465486151498872005 1271022087278653406038501)
                ·
                  refine ⟨238316641364747513632219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271022087278653406038501 238316641364747513632219)
                  ·
                    rfl

theorem cell22_2088540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_2088540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088540 prefixEnd_2088540 := by exact prefixLift 2088540
  have htrace : WordTrace (prefixWord ++ tailWord_2088540) baseStart_2088540 baseEnd_2088540 := by
    simpa [prefixWord, tailWord_2088540, baseEnd_2088540] using wordTrace_append hprefix tailTrace_2088540
  have hstable : (prefixWord ++ tailWord_2088540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088540).length < 2 ^ (prefixWord ++ tailWord_2088540).sum := by decide
  have hdescent : baseEnd_2088540 < baseStart_2088540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088600 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_2088600 : Nat := 118140960795 + 2088600 * 2 ^ 59
def prefixEnd_2088600 : Nat := 4983230072969 + 3 ^ 40 * 2088600 * 2
def baseEnd_2088600 : Nat := 714970463320422384396473

theorem tailTrace_2088600 : CollatzResearch.WordTrace tailWord_2088600 prefixEnd_2088600 714970463320422384396473 := by
  unfold tailWord_2088600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38088750116683189663207627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50785000155577586217610169 38088750116683189663207627)
  ·
    refine ⟨57133125175024784494811441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38088750116683189663207627 57133125175024784494811441)
    ·
      refine ⟨42849843881268588371108581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57133125175024784494811441 42849843881268588371108581)
      ·
        refine ⟨8034345727737860319582859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42849843881268588371108581 8034345727737860319582859)
        ·
          refine ⟨12051518591606790479374289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034345727737860319582859 12051518591606790479374289)
          ·
            refine ⟨9038638943705092859530717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12051518591606790479374289 9038638943705092859530717)
            ·
              refine ⟨3389489603889409822324019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9038638943705092859530717 3389489603889409822324019)
              ·
                refine ⟨5084234405834114733486029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389489603889409822324019 5084234405834114733486029)
                ·
                  refine ⟨1906587902187793025057261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5084234405834114733486029 1906587902187793025057261)
                  ·
                    refine ⟨714970463320422384396473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906587902187793025057261 714970463320422384396473)
                    ·
                      rfl

theorem cell22_2088600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_2088600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088600 prefixEnd_2088600 := by exact prefixLift 2088600
  have htrace : WordTrace (prefixWord ++ tailWord_2088600) baseStart_2088600 baseEnd_2088600 := by
    simpa [prefixWord, tailWord_2088600, baseEnd_2088600] using wordTrace_append hprefix tailTrace_2088600
  have hstable : (prefixWord ++ tailWord_2088600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088600).length < 2 ^ (prefixWord ++ tailWord_2088600).sum := by decide
  have hdescent : baseEnd_2088600 < baseStart_2088600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088611 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_2088611 : Nat := 118140960795 + 2088611 * 2 ^ 59
def prefixEnd_2088611 : Nat := 4983230072969 + 3 ^ 40 * 2088611 * 2
def baseEnd_2088611 : Nat := 714974228845222022371439

theorem tailTrace_2088611 : CollatzResearch.WordTrace tailWord_2088611 prefixEnd_2088611 714974228845222022371439 := by
  unfold tailWord_2088611
  simp only [CollatzResearch.WordTrace]
  refine ⟨76177901436326528205065687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50785267624217685470043791 76177901436326528205065687)
  ·
    refine ⟨114266852154489792307598531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76177901436326528205065687 114266852154489792307598531)
    ·
      refine ⟨171400278231734688461397797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114266852154489792307598531 171400278231734688461397797)
      ·
        refine ⟨32137552168450254086512087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171400278231734688461397797 32137552168450254086512087)
        ·
          refine ⟨48206328252675381129768131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32137552168450254086512087 48206328252675381129768131)
          ·
            refine ⟨72309492379013071694652197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48206328252675381129768131 72309492379013071694652197)
            ·
              refine ⟨13558029821064950942747287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72309492379013071694652197 13558029821064950942747287)
              ·
                refine ⟨20337044731597426414120931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13558029821064950942747287 20337044731597426414120931)
                ·
                  refine ⟨30505567097396139621181397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20337044731597426414120931 30505567097396139621181397)
                  ·
                    refine ⟨714974228845222022371439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30505567097396139621181397 714974228845222022371439)
                    ·
                      rfl

theorem cell22_2088611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_2088611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088611 prefixEnd_2088611 := by exact prefixLift 2088611
  have htrace : WordTrace (prefixWord ++ tailWord_2088611) baseStart_2088611 baseEnd_2088611 := by
    simpa [prefixWord, tailWord_2088611, baseEnd_2088611] using wordTrace_append hprefix tailTrace_2088611
  have hstable : (prefixWord ++ tailWord_2088611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088611).length < 2 ^ (prefixWord ++ tailWord_2088611).sum := by decide
  have hdescent : baseEnd_2088611 < baseStart_2088611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088660 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2088660 : Nat := 118140960795 + 2088660 * 2 ^ 59
def prefixEnd_2088660 : Nat := 4983230072969 + 3 ^ 40 * 2088660 * 2
def baseEnd_2088660 : Nat := 714991002546602227896289

theorem tailTrace_2088660 : CollatzResearch.WordTrace tailWord_2088660 prefixEnd_2088660 714991002546602227896289 := by
  unfold tailWord_2088660
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089844306574504786799717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50786459075432673049066289 38089844306574504786799717)
  ·
    refine ⟨7141845807482719647524947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38089844306574504786799717 7141845807482719647524947)
    ·
      refine ⟨10712768711224079471287421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7141845807482719647524947 10712768711224079471287421)
      ·
        refine ⟨4017288266709029801732783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10712768711224079471287421 4017288266709029801732783)
        ·
          refine ⟨6025932400063544702599175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017288266709029801732783 6025932400063544702599175)
          ·
            refine ⟨9038898600095317053898763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025932400063544702599175 9038898600095317053898763)
            ·
              refine ⟨13558347900142975580848145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038898600095317053898763 13558347900142975580848145)
              ·
                refine ⟨10168760925107231685636109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13558347900142975580848145 10168760925107231685636109)
                ·
                  refine ⟨3813285346915211882113541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10168760925107231685636109 3813285346915211882113541)
                  ·
                    refine ⟨714991002546602227896289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813285346915211882113541 714991002546602227896289)
                    ·
                      rfl

theorem cell22_2088660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2088660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088660 prefixEnd_2088660 := by exact prefixLift 2088660
  have htrace : WordTrace (prefixWord ++ tailWord_2088660) baseStart_2088660 baseEnd_2088660 := by
    simpa [prefixWord, tailWord_2088660, baseEnd_2088660] using wordTrace_append hprefix tailTrace_2088660
  have hstable : (prefixWord ++ tailWord_2088660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088660).length < 2 ^ (prefixWord ++ tailWord_2088660).sum := by decide
  have hdescent : baseEnd_2088660 < baseStart_2088660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088675 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 6]
def baseStart_2088675 : Nat := 118140960795 + 2088675 * 2 ^ 59
def prefixEnd_2088675 : Nat := 4983230072969 + 3 ^ 40 * 2088675 * 2
def baseEnd_2088675 : Nat := 238332045784382396257081

theorem tailTrace_2088675 : CollatzResearch.WordTrace tailWord_2088675 prefixEnd_2088675 238332045784382396257081 := by
  unfold tailWord_2088675
  simp only [CollatzResearch.WordTrace]
  refine ⟨76180235708094667135395479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50786823805396444756930319 76180235708094667135395479)
  ·
    refine ⟨114270353562142000703093219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76180235708094667135395479 114270353562142000703093219)
    ·
      refine ⟨171405530343213001054639829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114270353562142000703093219 171405530343213001054639829)
      ·
        refine ⟨4017317117419054712218121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 171405530343213001054639829 4017317117419054712218121)
        ·
          refine ⟨3012987838064291034163591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4017317117419054712218121 3012987838064291034163591)
          ·
            refine ⟨4519481757096436551245387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012987838064291034163591 4519481757096436551245387)
            ·
              refine ⟨6779222635644654826868081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519481757096436551245387 6779222635644654826868081)
              ·
                refine ⟨5084416976733491120151061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6779222635644654826868081 5084416976733491120151061)
                ·
                  refine ⟨238332045784382396257081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5084416976733491120151061 238332045784382396257081)
                  ·
                    rfl

theorem cell22_2088675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 6].length) (baseStart_2088675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088675 prefixEnd_2088675 := by exact prefixLift 2088675
  have htrace : WordTrace (prefixWord ++ tailWord_2088675) baseStart_2088675 baseEnd_2088675 := by
    simpa [prefixWord, tailWord_2088675, baseEnd_2088675] using wordTrace_append hprefix tailTrace_2088675
  have hstable : (prefixWord ++ tailWord_2088675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088675).length < 2 ^ (prefixWord ++ tailWord_2088675).sum := by decide
  have hdescent : baseEnd_2088675 < baseStart_2088675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088688 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_2088688 : Nat := 118140960795 + 2088688 * 2 ^ 59
def prefixEnd_2088688 : Nat := 4983230072969 + 3 ^ 40 * 2088688 * 2
def baseEnd_2088688 : Nat := 715000587518819488196203

theorem tailTrace_2088688 : CollatzResearch.WordTrace tailWord_2088688 prefixEnd_2088688 715000587518819488196203 := by
  unfold tailWord_2088688
  simp only [CollatzResearch.WordTrace]
  refine ⟨38090354928523785177809359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50787139904698380237079145 38090354928523785177809359)
  ·
    refine ⟨57135532392785677766714039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38090354928523785177809359 57135532392785677766714039)
    ·
      refine ⟨85703298589178516650071059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57135532392785677766714039 85703298589178516650071059)
      ·
        refine ⟨128554947883767774975106589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85703298589178516650071059 128554947883767774975106589)
        ·
          refine ⟨48208105456412915615664971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128554947883767774975106589 48208105456412915615664971)
          ·
            refine ⟨72312158184619373423497457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48208105456412915615664971 72312158184619373423497457)
            ·
              refine ⟨54234118638464530067623093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72312158184619373423497457 54234118638464530067623093)
              ·
                refine ⟨5084448622356049693839665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54234118638464530067623093 5084448622356049693839665)
                ·
                  refine ⟨3813336466767037270379749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084448622356049693839665 3813336466767037270379749)
                  ·
                    refine ⟨715000587518819488196203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813336466767037270379749 715000587518819488196203)
                    ·
                      rfl

theorem cell22_2088688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_2088688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088688 prefixEnd_2088688 := by exact prefixLift 2088688
  have htrace : WordTrace (prefixWord ++ tailWord_2088688) baseStart_2088688 baseEnd_2088688 := by
    simpa [prefixWord, tailWord_2088688, baseEnd_2088688] using wordTrace_append hprefix tailTrace_2088688
  have hstable : (prefixWord ++ tailWord_2088688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088688).length < 2 ^ (prefixWord ++ tailWord_2088688).sum := by decide
  have hdescent : baseEnd_2088688 < baseStart_2088688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088690 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_2088690 : Nat := 118140960795 + 2088690 * 2 ^ 59
def prefixEnd_2088690 : Nat := 4983230072969 + 3 ^ 40 * 2088690 * 2
def baseEnd_2088690 : Nat := 715001272159692149646197

theorem tailTrace_2088690 : CollatzResearch.WordTrace tailWord_2088690 prefixEnd_2088690 715001272159692149646197 := by
  unfold tailWord_2088690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045195700760081174297881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50787188535360216464794349 19045195700760081174297881)
  ·
    refine ⟨14283896775570060880723411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19045195700760081174297881 14283896775570060880723411)
    ·
      refine ⟨21425845163355091321085117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14283896775570060880723411 21425845163355091321085117)
      ·
        refine ⟨8034691936258159245406919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21425845163355091321085117 8034691936258159245406919)
        ·
          refine ⟨12052037904387238868110379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034691936258159245406919 12052037904387238868110379)
          ·
            refine ⟨18078056856580858302165569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052037904387238868110379 18078056856580858302165569)
            ·
              refine ⟨13558542642435643726624177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18078056856580858302165569 13558542642435643726624177)
              ·
                refine ⟨10168906981826732794968133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13558542642435643726624177 10168906981826732794968133)
                ·
                  refine ⟨1906670059092512399056525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10168906981826732794968133 1906670059092512399056525)
                  ·
                    refine ⟨715001272159692149646197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906670059092512399056525 715001272159692149646197)
                    ·
                      rfl

theorem cell22_2088690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_2088690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088690 prefixEnd_2088690 := by exact prefixLift 2088690
  have htrace : WordTrace (prefixWord ++ tailWord_2088690) baseStart_2088690 baseEnd_2088690 := by
    simpa [prefixWord, tailWord_2088690, baseEnd_2088690] using wordTrace_append hprefix tailTrace_2088690
  have hstable : (prefixWord ++ tailWord_2088690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088690).length < 2 ^ (prefixWord ++ tailWord_2088690).sum := by decide
  have hdescent : baseEnd_2088690 < baseStart_2088690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088694 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2088694 : Nat := 118140960795 + 2088694 * 2 ^ 59
def prefixEnd_2088694 : Nat := 4983230072969 + 3 ^ 40 * 2088694 * 2
def baseEnd_2088694 : Nat := 715002641441437472546185

theorem tailTrace_2088694 : CollatzResearch.WordTrace tailWord_2088694 prefixEnd_2088694 715002641441437472546185 := by
  unfold tailWord_2088694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761308043439114586271071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50787285796683888920224757 4761308043439114586271071)
  ·
    refine ⟨7141962065158671879406607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4761308043439114586271071 7141962065158671879406607)
    ·
      refine ⟨10712943097738007819109911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7141962065158671879406607 10712943097738007819109911)
      ·
        refine ⟨16069414646607011728664867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10712943097738007819109911 16069414646607011728664867)
        ·
          refine ⟨24104121969910517592997301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16069414646607011728664867 24104121969910517592997301)
          ·
            refine ⟨2259761434679111024343497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24104121969910517592997301 2259761434679111024343497)
            ·
              refine ⟨1694821076009333268257623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259761434679111024343497 1694821076009333268257623)
              ·
                refine ⟨2542231614013999902386435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694821076009333268257623 2542231614013999902386435)
                ·
                  refine ⟨3813347421020999853579653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542231614013999902386435 3813347421020999853579653)
                  ·
                    refine ⟨715002641441437472546185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813347421020999853579653 715002641441437472546185)
                    ·
                      rfl

theorem cell22_2088694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2088694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088694 prefixEnd_2088694 := by exact prefixLift 2088694
  have htrace : WordTrace (prefixWord ++ tailWord_2088694) baseStart_2088694 baseEnd_2088694 := by
    simpa [prefixWord, tailWord_2088694, baseEnd_2088694] using wordTrace_append hprefix tailTrace_2088694
  have hstable : (prefixWord ++ tailWord_2088694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088694).length < 2 ^ (prefixWord ++ tailWord_2088694).sum := by decide
  have hdescent : baseEnd_2088694 < baseStart_2088694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088735 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 3, 3]
def baseStart_2088735 : Nat := 118140960795 + 2088735 * 2 ^ 59
def prefixEnd_2088735 : Nat := 4983230072969 + 3 ^ 40 * 2088735 * 2
def baseEnd_2088735 : Nat := 715016676579327032271059

theorem tailTrace_2088735 : CollatzResearch.WordTrace tailWord_2088735 prefixEnd_2088735 715016676579327032271059 := by
  unfold tailWord_2088735
  simp only [CollatzResearch.WordTrace]
  refine ⟨76182424087877297382579659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50788282725251531588386439 76182424087877297382579659)
  ·
    refine ⟨114273636131815946073869489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76182424087877297382579659 114273636131815946073869489)
    ·
      refine ⟨85705227098861959555402117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114273636131815946073869489 85705227098861959555402117)
      ·
        refine ⟨16069730081036617416637897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85705227098861959555402117 16069730081036617416637897)
        ·
          refine ⟨12052297560777463062478423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16069730081036617416637897 12052297560777463062478423)
          ·
            refine ⟨18078446341166194593717635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052297560777463062478423 18078446341166194593717635)
            ·
              refine ⟨27117669511749291890576453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18078446341166194593717635 27117669511749291890576453)
              ·
                refine ⟨5084563033452992229483085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27117669511749291890576453 5084563033452992229483085)
                ·
                  refine ⟨1906711137544872086056157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5084563033452992229483085 1906711137544872086056157)
                  ·
                    refine ⟨715016676579327032271059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906711137544872086056157 715016676579327032271059)
                    ·
                      rfl

theorem cell22_2088735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_2088735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088735 prefixEnd_2088735 := by exact prefixLift 2088735
  have htrace : WordTrace (prefixWord ++ tailWord_2088735) baseStart_2088735 baseEnd_2088735 := by
    simpa [prefixWord, tailWord_2088735, baseEnd_2088735] using wordTrace_append hprefix tailTrace_2088735
  have hstable : (prefixWord ++ tailWord_2088735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088735).length < 2 ^ (prefixWord ++ tailWord_2088735).sum := by decide
  have hdescent : baseEnd_2088735 < baseStart_2088735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088748 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_2088748 : Nat := 118140960795 + 2088748 * 2 ^ 59
def prefixEnd_2088748 : Nat := 4983230072969 + 3 ^ 40 * 2088748 * 2
def baseEnd_2088748 : Nat := 238340375581666443898673

theorem tailTrace_2088748 : CollatzResearch.WordTrace tailWord_2088748 prefixEnd_2088748 238340375581666443898673 := by
  unfold tailWord_2088748
  simp only [CollatzResearch.WordTrace]
  refine ⟨38091449118415100301401449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50788598824553467068535265 38091449118415100301401449)
  ·
    refine ⟨28568586838811325226051087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38091449118415100301401449 28568586838811325226051087)
    ·
      refine ⟨42852880258216987839076631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28568586838811325226051087 42852880258216987839076631)
      ·
        refine ⟨64279320387325481758614947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42852880258216987839076631 64279320387325481758614947)
        ·
          refine ⟨96418980580988222637922421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64279320387325481758614947 96418980580988222637922421)
          ·
            refine ⟨9039279429467645872305227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96418980580988222637922421 9039279429467645872305227)
            ·
              refine ⟨13558919144201468808457841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039279429467645872305227 13558919144201468808457841)
              ·
                refine ⟨10169189358151101606343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13558919144201468808457841 10169189358151101606343381)
                ·
                  refine ⟨238340375581666443898673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10169189358151101606343381 238340375581666443898673)
                  ·
                    rfl

theorem cell22_2088748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_2088748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088748 prefixEnd_2088748 := by exact prefixLift 2088748
  have htrace : WordTrace (prefixWord ++ tailWord_2088748) baseStart_2088748 baseEnd_2088748 := by
    simpa [prefixWord, tailWord_2088748, baseEnd_2088748] using wordTrace_append hprefix tailTrace_2088748
  have hstable : (prefixWord ++ tailWord_2088748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088748).length < 2 ^ (prefixWord ++ tailWord_2088748).sum := by decide
  have hdescent : baseEnd_2088748 < baseStart_2088748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088765 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2088765 : Nat := 118140960795 + 2088765 * 2 ^ 59
def prefixEnd_2088765 : Nat := 4983230072969 + 3 ^ 40 * 2088765 * 2
def baseEnd_2088765 : Nat := 238342315397472318006989

theorem tailTrace_2088765 : CollatzResearch.WordTrace tailWord_2088765 prefixEnd_2088765 238342315397472318006989 := by
  unfold tailWord_2088765
  simp only [CollatzResearch.WordTrace]
  refine ⟨76183518277768612506171749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50789012185179075004114499 76183518277768612506171749)
  ·
    refine ⟨14284409677081614844907203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76183518277768612506171749 14284409677081614844907203)
    ·
      refine ⟨21426614515622422267360805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14284409677081614844907203 21426614515622422267360805)
      ·
        refine ⟨4017490221679204175130151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21426614515622422267360805 4017490221679204175130151)
        ·
          refine ⟨6026235332518806262695227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017490221679204175130151 6026235332518806262695227)
          ·
            refine ⟨9039352998778209394042841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026235332518806262695227 9039352998778209394042841)
            ·
              refine ⟨6779514749083657045532131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9039352998778209394042841 6779514749083657045532131)
              ·
                refine ⟨10169272123625485568298197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779514749083657045532131 10169272123625485568298197)
                ·
                  refine ⟨238342315397472318006989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10169272123625485568298197 238342315397472318006989)
                  ·
                    rfl

theorem cell22_2088765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2088765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088765 prefixEnd_2088765 := by exact prefixLift 2088765
  have htrace : WordTrace (prefixWord ++ tailWord_2088765) baseStart_2088765 baseEnd_2088765 := by
    simpa [prefixWord, tailWord_2088765, baseEnd_2088765] using wordTrace_append hprefix tailTrace_2088765
  have hstable : (prefixWord ++ tailWord_2088765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088765).length < 2 ^ (prefixWord ++ tailWord_2088765).sum := by decide
  have hdescent : baseEnd_2088765 < baseStart_2088765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088793 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 8]
def baseStart_2088793 : Nat := 118140960795 + 2088793 * 2 ^ 59
def prefixEnd_2088793 : Nat := 4983230072969 + 3 ^ 40 * 2088793 * 2
def baseEnd_2088793 : Nat := 238345510388211404773627

theorem tailTrace_2088793 : CollatzResearch.WordTrace tailWord_2088793 prefixEnd_2088793 238345510388211404773627 := by
  unfold tailWord_2088793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76184539521667173288191033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50789693014444782192127355 76184539521667173288191033)
  ·
    refine ⟨57138404641250379966143275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76184539521667173288191033 57138404641250379966143275)
    ·
      refine ⟨85707606961875569949214913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57138404641250379966143275 85707606961875569949214913)
      ·
        refine ⟨64280705221406677461911185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85707606961875569949214913 64280705221406677461911185)
        ·
          refine ⟨48210528916055008096433389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64280705221406677461911185 48210528916055008096433389)
          ·
            refine ⟨18078948343520628036162521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48210528916055008096433389 18078948343520628036162521)
            ·
              refine ⟨13559211257640471027121891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18078948343520628036162521 13559211257640471027121891)
              ·
                refine ⟨20338816886460706540682837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13559211257640471027121891 20338816886460706540682837)
                ·
                  refine ⟨238345510388211404773627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20338816886460706540682837 238345510388211404773627)
                  ·
                    rfl

theorem cell22_2088793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_2088793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088793 prefixEnd_2088793 := by exact prefixLift 2088793
  have htrace : WordTrace (prefixWord ++ tailWord_2088793) baseStart_2088793 baseEnd_2088793 := by
    simpa [prefixWord, tailWord_2088793, baseEnd_2088793] using wordTrace_append hprefix tailTrace_2088793
  have hstable : (prefixWord ++ tailWord_2088793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088793).length < 2 ^ (prefixWord ++ tailWord_2088793).sum := by decide
  have hdescent : baseEnd_2088793 < baseStart_2088793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088823 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2088823 : Nat := 118140960795 + 2088823 * 2 ^ 59
def prefixEnd_2088823 : Nat := 4983230072969 + 3 ^ 40 * 2088823 * 2
def baseEnd_2088823 : Nat := 715046800777724136070789

theorem tailTrace_2088823 : CollatzResearch.WordTrace tailWord_2088823 prefixEnd_2088823 715046800777724136070789 := by
  unfold tailWord_2088823
  simp only [CollatzResearch.WordTrace]
  refine ⟨76185633711558488411783123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50790422474372325607855415 76185633711558488411783123)
  ·
    refine ⟨114278450567337732617674685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76185633711558488411783123 114278450567337732617674685)
    ·
      refine ⟨42854418962751649731628007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114278450567337732617674685 42854418962751649731628007)
      ·
        refine ⟨64281628444127474597442011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42854418962751649731628007 64281628444127474597442011)
        ·
          refine ⟨96422442666191211896163017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64281628444127474597442011 96422442666191211896163017)
          ·
            refine ⟨72316831999643408922122263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96422442666191211896163017 72316831999643408922122263)
            ·
              refine ⟨108475247999465113383183395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72316831999643408922122263 108475247999465113383183395)
              ·
                refine ⟨162712871999197670074775093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108475247999465113383183395 162712871999197670074775093)
                ·
                  refine ⟨15254331749924781569510165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162712871999197670074775093 15254331749924781569510165)
                  ·
                    refine ⟨715046800777724136070789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15254331749924781569510165 715046800777724136070789)
                    ·
                      rfl

theorem cell22_2088823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2088823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088823 prefixEnd_2088823 := by exact prefixLift 2088823
  have htrace : WordTrace (prefixWord ++ tailWord_2088823) baseStart_2088823 baseEnd_2088823 := by
    simpa [prefixWord, tailWord_2088823, baseEnd_2088823] using wordTrace_append hprefix tailTrace_2088823
  have hstable : (prefixWord ++ tailWord_2088823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088823).length < 2 ^ (prefixWord ++ tailWord_2088823).sum := by decide
  have hdescent : baseEnd_2088823 < baseStart_2088823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088981 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_2088981 : Nat := 118140960795 + 2088981 * 2 ^ 59
def prefixEnd_2088981 : Nat := 4983230072969 + 3 ^ 40 * 2088981 * 2
def baseEnd_2088981 : Nat := 715100887406664390620305

theorem tailTrace_2088981 : CollatzResearch.WordTrace tailWord_2088981 prefixEnd_2088981 715100887406664390620305 := by
  unfold tailWord_2088981
  simp only [CollatzResearch.WordTrace]
  refine ⟨76191396444986081396034797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50794264296657387597356531 76191396444986081396034797)
  ·
    refine ⟨28571773666869780523513049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76191396444986081396034797 28571773666869780523513049)
    ·
      refine ⟨21428830250152335392634787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28571773666869780523513049 21428830250152335392634787)
      ·
        refine ⟨32143245375228503088952181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21428830250152335392634787 32143245375228503088952181)
        ·
          refine ⟨3013429253927672164589267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32143245375228503088952181 3013429253927672164589267)
          ·
            refine ⟨4520143880891508246883901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013429253927672164589267 4520143880891508246883901)
            ·
              refine ⟨1695053955334315592581463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4520143880891508246883901 1695053955334315592581463)
              ·
                refine ⟨2542580933001473388872195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695053955334315592581463 2542580933001473388872195)
                ·
                  refine ⟨3813871399502210083308293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542580933001473388872195 3813871399502210083308293)
                  ·
                    refine ⟨715100887406664390620305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813871399502210083308293 715100887406664390620305)
                    ·
                      rfl

theorem cell22_2088981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_2088981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088981 prefixEnd_2088981 := by exact prefixLift 2088981
  have htrace : WordTrace (prefixWord ++ tailWord_2088981) baseStart_2088981 baseEnd_2088981 := by
    simpa [prefixWord, tailWord_2088981, baseEnd_2088981] using wordTrace_append hprefix tailTrace_2088981
  have hstable : (prefixWord ++ tailWord_2088981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088981).length < 2 ^ (prefixWord ++ tailWord_2088981).sum := by decide
  have hdescent : baseEnd_2088981 < baseStart_2088981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088996 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 4]
def baseStart_2088996 : Nat := 118140960795 + 2088996 * 2 ^ 59
def prefixEnd_2088996 : Nat := 4983230072969 + 3 ^ 40 * 2088996 * 2
def baseEnd_2088996 : Nat := 238368674071069783831753

theorem tailTrace_2088996 : CollatzResearch.WordTrace tailWord_2088996 prefixEnd_2088996 238368674071069783831753 := by
  unfold tailWord_2088996
  simp only [CollatzResearch.WordTrace]
  refine ⟨38095971769965869478915421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50794629026621159305220561 38095971769965869478915421)
  ·
    refine ⟨14285989413737201054593283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38095971769965869478915421 14285989413737201054593283)
    ·
      refine ⟨21428984120605801581889925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14285989413737201054593283 21428984120605801581889925)
      ·
        refine ⟨4017934522613587796604361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21428984120605801581889925 4017934522613587796604361)
        ·
          refine ⟨3013450891960190847453271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4017934522613587796604361 3013450891960190847453271)
          ·
            refine ⟨4520176337940286271179907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013450891960190847453271 4520176337940286271179907)
            ·
              refine ⟨6780264506910429406769861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520176337940286271179907 6780264506910429406769861)
              ·
                refine ⟨1271299595045705513769349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6780264506910429406769861 1271299595045705513769349)
                ·
                  refine ⟨238368674071069783831753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271299595045705513769349 238368674071069783831753)
                  ·
                    rfl

theorem cell22_2088996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_2088996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2088996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2088996 prefixEnd_2088996 := by exact prefixLift 2088996
  have htrace : WordTrace (prefixWord ++ tailWord_2088996) baseStart_2088996 baseEnd_2088996 := by
    simpa [prefixWord, tailWord_2088996, baseEnd_2088996] using wordTrace_append hprefix tailTrace_2088996
  have hstable : (prefixWord ++ tailWord_2088996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088996).length < 2 ^ (prefixWord ++ tailWord_2088996).sum := by decide
  have hdescent : baseEnd_2088996 < baseStart_2088996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089035 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 9]
def baseStart_2089035 : Nat := 118140960795 + 2089035 * 2 ^ 59
def prefixEnd_2089035 : Nat := 4983230072969 + 3 ^ 40 * 2089035 * 2
def baseEnd_2089035 : Nat := 238373124236742083256713

theorem tailTrace_2089035 : CollatzResearch.WordTrace tailWord_2089035 prefixEnd_2089035 238373124236742083256713 := by
  unfold tailWord_2089035
  simp only [CollatzResearch.WordTrace]
  refine ⟨76193365986790448618500559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50795577324526965745667039 76193365986790448618500559)
  ·
    refine ⟨114290048980185672927750839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76193365986790448618500559 114290048980185672927750839)
    ·
      refine ⟨171435073470278509391626259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114290048980185672927750839 171435073470278509391626259)
      ·
        refine ⟨257152610205417764087439389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171435073470278509391626259 257152610205417764087439389)
        ·
          refine ⟨96432228827031661532789771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257152610205417764087439389 96432228827031661532789771)
          ·
            refine ⟨144648343240547492299184657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96432228827031661532789771 144648343240547492299184657)
            ·
              refine ⟨108486257430410619224388493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144648343240547492299184657 108486257430410619224388493)
              ·
                refine ⟨40682346536403982209145685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108486257430410619224388493 40682346536403982209145685)
                ·
                  refine ⟨238373124236742083256713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40682346536403982209145685 238373124236742083256713)
                  ·
                    rfl

theorem cell22_2089035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_2089035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089035 prefixEnd_2089035 := by exact prefixLift 2089035
  have htrace : WordTrace (prefixWord ++ tailWord_2089035) baseStart_2089035 baseEnd_2089035 := by
    simpa [prefixWord, tailWord_2089035, baseEnd_2089035] using wordTrace_append hprefix tailTrace_2089035
  have hstable : (prefixWord ++ tailWord_2089035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089035).length < 2 ^ (prefixWord ++ tailWord_2089035).sum := by decide
  have hdescent : baseEnd_2089035 < baseStart_2089035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089056 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 1, 3]
def baseStart_2089056 : Nat := 118140960795 + 2089056 * 2 ^ 59
def prefixEnd_2089056 : Nat := 4983230072969 + 3 ^ 40 * 2089056 * 2
def baseEnd_2089056 : Nat := 715126561439389194995075

theorem tailTrace_2089056 : CollatzResearch.WordTrace tailWord_2089056 prefixEnd_2089056 715126561439389194995075 := by
  unfold tailWord_2089056
  simp only [CollatzResearch.WordTrace]
  refine ⟨38097065959857184602507511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50796087946476246136676681 38097065959857184602507511)
  ·
    refine ⟨57145598939785776903761267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38097065959857184602507511 57145598939785776903761267)
    ·
      refine ⟨85718398409678665355641901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57145598939785776903761267 85718398409678665355641901)
      ·
        refine ⟨32144399403629499508365713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85718398409678665355641901 32144399403629499508365713)
        ·
          refine ⟨24108299552722124631274285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32144399403629499508365713 24108299552722124631274285)
          ·
            refine ⟨9040612332270796736727857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24108299552722124631274285 9040612332270796736727857)
            ·
              refine ⟨6780459249203097552545893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9040612332270796736727857 6780459249203097552545893)
              ·
                refine ⟨1271336109225580791102355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6780459249203097552545893 1271336109225580791102355)
                ·
                  refine ⟨1907004163838371186653533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271336109225580791102355 1907004163838371186653533)
                  ·
                    refine ⟨715126561439389194995075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907004163838371186653533 715126561439389194995075)
                    ·
                      rfl

theorem cell22_2089056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_2089056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089056 prefixEnd_2089056 := by exact prefixLift 2089056
  have htrace : WordTrace (prefixWord ++ tailWord_2089056) baseStart_2089056 baseEnd_2089056 := by
    simpa [prefixWord, tailWord_2089056, baseEnd_2089056] using wordTrace_append hprefix tailTrace_2089056
  have hstable : (prefixWord ++ tailWord_2089056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089056).length < 2 ^ (prefixWord ++ tailWord_2089056).sum := by decide
  have hdescent : baseEnd_2089056 < baseStart_2089056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089133 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2089133 : Nat := 118140960795 + 2089133 * 2 ^ 59
def prefixEnd_2089133 : Nat := 4983230072969 + 3 ^ 40 * 2089133 * 2
def baseEnd_2089133 : Nat := 715152920112986660819839

theorem tailTrace_2089133 : CollatzResearch.WordTrace tailWord_2089133 prefixEnd_2089133 715152920112986660819839 := by
  unfold tailWord_2089133
  simp only [CollatzResearch.WordTrace]
  refine ⟨76196940340435411355568053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50797960226956940903712035 76196940340435411355568053)
  ·
    refine ⟨7143463156915819814584505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76196940340435411355568053 7143463156915819814584505)
    ·
      refine ⟨5357597367686864860938379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7143463156915819814584505 5357597367686864860938379)
      ·
        refine ⟨8036396051530297291407569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357597367686864860938379 8036396051530297291407569)
        ·
          refine ⟨6027297038647722968555677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8036396051530297291407569 6027297038647722968555677)
          ·
            refine ⟨2260236389492896113208379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6027297038647722968555677 2260236389492896113208379)
            ·
              refine ⟨3390354584239344169812569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260236389492896113208379 3390354584239344169812569)
              ·
                refine ⟨2542765938179508127359427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390354584239344169812569 2542765938179508127359427)
                ·
                  refine ⟨3814148907269262191039141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542765938179508127359427 3814148907269262191039141)
                  ·
                    refine ⟨715152920112986660819839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3814148907269262191039141 715152920112986660819839)
                    ·
                      rfl

theorem cell22_2089133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2089133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089133 prefixEnd_2089133 := by exact prefixLift 2089133
  have htrace : WordTrace (prefixWord ++ tailWord_2089133) baseStart_2089133 baseEnd_2089133 := by
    simpa [prefixWord, tailWord_2089133, baseEnd_2089133] using wordTrace_append hprefix tailTrace_2089133
  have hstable : (prefixWord ++ tailWord_2089133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089133).length < 2 ^ (prefixWord ++ tailWord_2089133).sum := by decide
  have hdescent : baseEnd_2089133 < baseStart_2089133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089144 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_2089144 : Nat := 118140960795 + 2089144 * 2 ^ 59
def prefixEnd_2089144 : Nat := 4983230072969 + 3 ^ 40 * 2089144 * 2
def baseEnd_2089144 : Nat := 715156685637786298794805

theorem tailTrace_2089144 : CollatzResearch.WordTrace tailWord_2089144 prefixEnd_2089144 715156685637786298794805 := by
  unfold tailWord_2089144
  simp only [CollatzResearch.WordTrace]
  refine ⟨38098670771697780117109243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50798227695597040156145657 38098670771697780117109243)
  ·
    refine ⟨57148006157546670175663865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38098670771697780117109243 57148006157546670175663865)
    ·
      refine ⟨42861004618160002631747899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57148006157546670175663865 42861004618160002631747899)
      ·
        refine ⟨64291506927240003947621849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42861004618160002631747899 64291506927240003947621849)
        ·
          refine ⟨48218630195430002960716387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64291506927240003947621849 48218630195430002960716387)
          ·
            refine ⟨72327945293145004441074581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48218630195430002960716387 72327945293145004441074581)
            ·
              refine ⟨3390372435616172083175371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72327945293145004441074581 3390372435616172083175371)
              ·
                refine ⟨5085558653424258124763057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390372435616172083175371 5085558653424258124763057)
                ·
                  refine ⟨3814168990068193593572293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5085558653424258124763057 3814168990068193593572293)
                  ·
                    refine ⟨715156685637786298794805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3814168990068193593572293 715156685637786298794805)
                    ·
                      rfl

theorem cell22_2089144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_2089144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089144 prefixEnd_2089144 := by exact prefixLift 2089144
  have htrace : WordTrace (prefixWord ++ tailWord_2089144) baseStart_2089144 baseEnd_2089144 := by
    simpa [prefixWord, tailWord_2089144, baseEnd_2089144] using wordTrace_append hprefix tailTrace_2089144
  have hstable : (prefixWord ++ tailWord_2089144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089144).length < 2 ^ (prefixWord ++ tailWord_2089144).sum := by decide
  have hdescent : baseEnd_2089144 < baseStart_2089144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089191 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2089191 : Nat := 118140960795 + 2089191 * 2 ^ 59
def prefixEnd_2089191 : Nat := 4983230072969 + 3 ^ 40 * 2089191 * 2
def baseEnd_2089191 : Nat := 715172774698293842869661

theorem tailTrace_2089191 : CollatzResearch.WordTrace tailWord_2089191 prefixEnd_2089191 715172774698293842869661 := by
  unfold tailWord_2089191
  simp only [CollatzResearch.WordTrace]
  refine ⟨76199055774225287261179427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50799370516150191507452951 76199055774225287261179427)
  ·
    refine ⟨114298583661337930891769141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76199055774225287261179427 114298583661337930891769141)
    ·
      refine ⟨10715492218250431021103357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114298583661337930891769141 10715492218250431021103357)
      ·
        refine ⟨4018309581843911632913759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10715492218250431021103357 4018309581843911632913759)
        ·
          refine ⟨6027464372765867449370639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018309581843911632913759 6027464372765867449370639)
          ·
            refine ⟨9041196559148801174055959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027464372765867449370639 9041196559148801174055959)
            ·
              refine ⟨13561794838723201761083939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041196559148801174055959 13561794838723201761083939)
              ·
                refine ⟨20342692258084802641625909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13561794838723201761083939 20342692258084802641625909)
                ·
                  refine ⟨1907127399195450247652429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20342692258084802641625909 1907127399195450247652429)
                  ·
                    refine ⟨715172774698293842869661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907127399195450247652429 715172774698293842869661)
                    ·
                      rfl

theorem cell22_2089191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2089191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089191 prefixEnd_2089191 := by exact prefixLift 2089191
  have htrace : WordTrace (prefixWord ++ tailWord_2089191) baseStart_2089191 baseEnd_2089191 := by
    simpa [prefixWord, tailWord_2089191, baseEnd_2089191] using wordTrace_append hprefix tailTrace_2089191
  have hstable : (prefixWord ++ tailWord_2089191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089191).length < 2 ^ (prefixWord ++ tailWord_2089191).sum := by decide
  have hdescent : baseEnd_2089191 < baseStart_2089191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089249 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 6]
def baseStart_2089249 : Nat := 118140960795 + 2089249 * 2 ^ 59
def prefixEnd_2089249 : Nat := 4983230072969 + 3 ^ 40 * 2089249 * 2
def baseEnd_2089249 : Nat := 238397543094533674973161

theorem tailTrace_2089249 : CollatzResearch.WordTrace tailWord_2089249 prefixEnd_2089249 238397543094533674973161 := by
  unfold tailWord_2089249
  simp only [CollatzResearch.WordTrace]
  refine ⟨76201171208015163166790801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50800780805343442111193867 76201171208015163166790801)
  ·
    refine ⟨57150878406011372375093101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76201171208015163166790801 57150878406011372375093101)
    ·
      refine ⟨21431579402254264640659913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57150878406011372375093101 21431579402254264640659913)
      ·
        refine ⟨16073684551690698480494935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21431579402254264640659913 16073684551690698480494935)
        ·
          refine ⟨24110526827536047720742403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16073684551690698480494935 24110526827536047720742403)
          ·
            refine ⟨36165790241304071581113605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24110526827536047720742403 36165790241304071581113605)
            ·
              refine ⟨6781085670244513421458801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36165790241304071581113605 6781085670244513421458801)
              ·
                refine ⟨5085814252683385066094101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6781085670244513421458801 5085814252683385066094101)
                ·
                  refine ⟨238397543094533674973161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5085814252683385066094101 238397543094533674973161)
                  ·
                    rfl

theorem cell22_2089249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_2089249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089249 prefixEnd_2089249 := by exact prefixLift 2089249
  have htrace : WordTrace (prefixWord ++ tailWord_2089249) baseStart_2089249 baseEnd_2089249 := by
    simpa [prefixWord, tailWord_2089249, baseEnd_2089249] using wordTrace_append hprefix tailTrace_2089249
  have hstable : (prefixWord ++ tailWord_2089249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089249).length < 2 ^ (prefixWord ++ tailWord_2089249).sum := by decide
  have hdescent : baseEnd_2089249 < baseStart_2089249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089251 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 1, 4]
def baseStart_2089251 : Nat := 118140960795 + 2089251 * 2 ^ 59
def prefixEnd_2089251 : Nat := 4983230072969 + 3 ^ 40 * 2089251 * 2
def baseEnd_2089251 : Nat := 715193313924473686369477

theorem tailTrace_2089251 : CollatzResearch.WordTrace tailWord_2089251 prefixEnd_2089251 715193313924473686369477 := by
  unfold tailWord_2089251
  simp only [CollatzResearch.WordTrace]
  refine ⟨76201244154007917508363607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50800829436005278338909071 76201244154007917508363607)
  ·
    refine ⟨114301866231011876262545411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76201244154007917508363607 114301866231011876262545411)
    ·
      refine ⟨171452799346517814393818117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114301866231011876262545411 171452799346517814393818117)
      ·
        refine ⟨32147399877472090198840897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171452799346517814393818117 32147399877472090198840897)
        ·
          refine ⟨24110549908104067649130673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32147399877472090198840897 24110549908104067649130673)
          ·
            refine ⟨18082912431078050736848005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24110549908104067649130673 18082912431078050736848005)
            ·
              refine ⟨3390546080827134513159001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18082912431078050736848005 3390546080827134513159001)
              ·
                refine ⟨2542909560620350884869251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390546080827134513159001 2542909560620350884869251)
                ·
                  refine ⟨3814364340930526327303877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542909560620350884869251 3814364340930526327303877)
                  ·
                    refine ⟨715193313924473686369477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3814364340930526327303877 715193313924473686369477)
                    ·
                      rfl

theorem cell22_2089251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 4].length) (baseStart_2089251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089251 prefixEnd_2089251 := by exact prefixLift 2089251
  have htrace : WordTrace (prefixWord ++ tailWord_2089251) baseStart_2089251 baseEnd_2089251 := by
    simpa [prefixWord, tailWord_2089251, baseEnd_2089251] using wordTrace_append hprefix tailTrace_2089251
  have hstable : (prefixWord ++ tailWord_2089251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089251).length < 2 ^ (prefixWord ++ tailWord_2089251).sum := by decide
  have hdescent : baseEnd_2089251 < baseStart_2089251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089268 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2089268 : Nat := 118140960795 + 2089268 * 2 ^ 59
def prefixEnd_2089268 : Nat := 4983230072969 + 3 ^ 40 * 2089268 * 2
def baseEnd_2089268 : Nat := 715199133371891308694425

theorem tailTrace_2089268 : CollatzResearch.WordTrace tailWord_2089268 prefixEnd_2089268 715199133371891308694425 := by
  unfold tailWord_2089268
  simp only [CollatzResearch.WordTrace]
  refine ⟨38100932097473164705866229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50801242796630886274488305 38100932097473164705866229)
  ·
    refine ⟨3571962384138109191174959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38100932097473164705866229 3571962384138109191174959)
    ·
      refine ⟨5357943576207163786762439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3571962384138109191174959 5357943576207163786762439)
      ·
        refine ⟨8036915364310745680143659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357943576207163786762439 8036915364310745680143659)
        ·
          refine ⟨12055373046466118520215489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036915364310745680143659 12055373046466118520215489)
          ·
            refine ⟨9041529784849588890161617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12055373046466118520215489 9041529784849588890161617)
            ·
              refine ⟨6781147338637191667621213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9041529784849588890161617 6781147338637191667621213)
              ·
                refine ⟨2542930251988946875357955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6781147338637191667621213 2542930251988946875357955)
                ·
                  refine ⟨3814395377983420313036933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542930251988946875357955 3814395377983420313036933)
                  ·
                    refine ⟨715199133371891308694425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3814395377983420313036933 715199133371891308694425)
                    ·
                      rfl

theorem cell22_2089268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2089268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089268 prefixEnd_2089268 := by exact prefixLift 2089268
  have htrace : WordTrace (prefixWord ++ tailWord_2089268) baseStart_2089268 baseEnd_2089268 := by
    simpa [prefixWord, tailWord_2089268, baseEnd_2089268] using wordTrace_append hprefix tailTrace_2089268
  have hstable : (prefixWord ++ tailWord_2089268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089268).length < 2 ^ (prefixWord ++ tailWord_2089268).sum := by decide
  have hdescent : baseEnd_2089268 < baseStart_2089268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089334 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_2089334 : Nat := 118140960795 + 2089334 * 2 ^ 59
def prefixEnd_2089334 : Nat := 4983230072969 + 3 ^ 40 * 2089334 * 2
def baseEnd_2089334 : Nat := 238407242173563045514741

theorem tailTrace_2089334 : CollatzResearch.WordTrace tailWord_2089334 prefixEnd_2089334 238407242173563045514741 := by
  unfold tailWord_2089334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762766963294201417727191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50802847608471481789090037 4762766963294201417727191)
  ·
    refine ⟨7144150444941302126590787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4762766963294201417727191 7144150444941302126590787)
    ·
      refine ⟨10716225667411953189886181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144150444941302126590787 10716225667411953189886181)
      ·
        refine ⟨2009292312639741223103659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10716225667411953189886181 2009292312639741223103659)
        ·
          refine ⟨3013938468959611834655489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009292312639741223103659 3013938468959611834655489)
          ·
            refine ⟨2260453851719708875991617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013938468959611834655489 2260453851719708875991617)
            ·
              refine ⟨1695340388789781656993713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260453851719708875991617 1695340388789781656993713)
              ·
                refine ⟨1271505291592336242745285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695340388789781656993713 1271505291592336242745285)
                ·
                  refine ⟨238407242173563045514741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271505291592336242745285 238407242173563045514741)
                  ·
                    rfl

theorem cell22_2089334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_2089334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089334 prefixEnd_2089334 := by exact prefixLift 2089334
  have htrace : WordTrace (prefixWord ++ tailWord_2089334) baseStart_2089334 baseEnd_2089334 := by
    simpa [prefixWord, tailWord_2089334, baseEnd_2089334] using wordTrace_append hprefix tailTrace_2089334
  have hstable : (prefixWord ++ tailWord_2089334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089334).length < 2 ^ (prefixWord ++ tailWord_2089334).sum := by decide
  have hdescent : baseEnd_2089334 < baseStart_2089334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089343 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 1, 3]
def baseStart_2089343 : Nat := 118140960795 + 2089343 * 2 ^ 59
def prefixEnd_2089343 : Nat := 4983230072969 + 3 ^ 40 * 2089343 * 2
def baseEnd_2089343 : Nat := 715224807404616113069195

theorem tailTrace_2089343 : CollatzResearch.WordTrace tailWord_2089343 prefixEnd_2089343 715224807404616113069195 := by
  unfold tailWord_2089343
  simp only [CollatzResearch.WordTrace]
  refine ⟨76204599669674617220712683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50803066446449744813808455 76204599669674617220712683)
  ·
    refine ⟨114306899504511925831069025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76204599669674617220712683 114306899504511925831069025)
    ·
      refine ⟨85730174628383944373301769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114306899504511925831069025 85730174628383944373301769)
      ·
        refine ⟨64297630971287958279976327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85730174628383944373301769 64297630971287958279976327)
        ·
          refine ⟨96446446456931937419964491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64297630971287958279976327 96446446456931937419964491)
          ·
            refine ⟨144669669685397906129946737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96446446456931937419964491 144669669685397906129946737)
            ·
              refine ⟨108502252264048429597460053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144669669685397906129946737 108502252264048429597460053)
              ·
                refine ⟨1271510768719317534345235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 108502252264048429597460053 1271510768719317534345235)
                ·
                  refine ⟨1907266153078976301517853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271510768719317534345235 1907266153078976301517853)
                  ·
                    refine ⟨715224807404616113069195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907266153078976301517853 715224807404616113069195)
                    ·
                      rfl

theorem cell22_2089343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_2089343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089343 prefixEnd_2089343 := by exact prefixLift 2089343
  have htrace : WordTrace (prefixWord ++ tailWord_2089343) baseStart_2089343 baseEnd_2089343 := by
    simpa [prefixWord, tailWord_2089343, baseEnd_2089343] using wordTrace_append hprefix tailTrace_2089343
  have hstable : (prefixWord ++ tailWord_2089343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089343).length < 2 ^ (prefixWord ++ tailWord_2089343).sum := by decide
  have hdescent : baseEnd_2089343 < baseStart_2089343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089356 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_2089356 : Nat := 118140960795 + 2089356 * 2 ^ 59
def prefixEnd_2089356 : Nat := 4983230072969 + 3 ^ 40 * 2089356 * 2
def baseEnd_2089356 : Nat := 238409752523429470831385

theorem tailTrace_2089356 : CollatzResearch.WordTrace tailWord_2089356 prefixEnd_2089356 238409752523429470831385 := by
  unfold tailWord_2089356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38102536909313760220467961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50803382545751680293957281 38102536909313760220467961)
  ·
    refine ⟨28576902681985320165350971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38102536909313760220467961 28576902681985320165350971)
    ·
      refine ⟨42865354022977980248026457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28576902681985320165350971 42865354022977980248026457)
      ·
        refine ⟨32149015517233485186019843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42865354022977980248026457 32149015517233485186019843)
        ·
          refine ⟨48223523275850227779029765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32149015517233485186019843 48223523275850227779029765)
          ·
            refine ⟨9041910614221917708568081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48223523275850227779029765 9041910614221917708568081)
            ·
              refine ⟨6781432960666438281426061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9041910614221917708568081 6781432960666438281426061)
              ·
                refine ⟨2543037360249914355534773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6781432960666438281426061 2543037360249914355534773)
                ·
                  refine ⟨238409752523429470831385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2543037360249914355534773 238409752523429470831385)
                  ·
                    rfl

theorem cell22_2089356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_2089356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089356 prefixEnd_2089356 := by exact prefixLift 2089356
  have htrace : WordTrace (prefixWord ++ tailWord_2089356) baseStart_2089356 baseEnd_2089356 := by
    simpa [prefixWord, tailWord_2089356, baseEnd_2089356] using wordTrace_append hprefix tailTrace_2089356
  have hstable : (prefixWord ++ tailWord_2089356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089356).length < 2 ^ (prefixWord ++ tailWord_2089356).sum := by decide
  have hdescent : baseEnd_2089356 < baseStart_2089356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089401 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 6]
def baseStart_2089401 : Nat := 118140960795 + 2089401 * 2 ^ 59
def prefixEnd_2089401 : Nat := 4983230072969 + 3 ^ 40 * 2089401 * 2
def baseEnd_2089401 : Nat := 238414887329974431706339

theorem tailTrace_2089401 : CollatzResearch.WordTrace tailWord_2089401 prefixEnd_2089401 238414887329974431706339 := by
  unfold tailWord_2089401
  simp only [CollatzResearch.WordTrace]
  refine ⟨76206715103464493126324057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50804476735642995417549371 76206715103464493126324057)
  ·
    refine ⟨57155036327598369844743043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76206715103464493126324057 57155036327598369844743043)
    ·
      refine ⟨85732554491397554767114565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57155036327598369844743043 85732554491397554767114565)
      ·
        refine ⟨16074853967137041518833981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85732554491397554767114565 16074853967137041518833981)
        ·
          refine ⟨6028070237676390569562743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16074853967137041518833981 6028070237676390569562743)
          ·
            refine ⟨9042105356514585854344115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028070237676390569562743 9042105356514585854344115)
            ·
              refine ⟨13563158034771878781516173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042105356514585854344115 13563158034771878781516173)
              ·
                refine ⟨5086184263039454543068565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13563158034771878781516173 5086184263039454543068565)
                ·
                  refine ⟨238414887329974431706339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5086184263039454543068565 238414887329974431706339)
                  ·
                    rfl

theorem cell22_2089401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_2089401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089401 prefixEnd_2089401 := by exact prefixLift 2089401
  have htrace : WordTrace (prefixWord ++ tailWord_2089401) baseStart_2089401 baseEnd_2089401 := by
    simpa [prefixWord, tailWord_2089401, baseEnd_2089401] using wordTrace_append hprefix tailTrace_2089401
  have hstable : (prefixWord ++ tailWord_2089401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089401).length < 2 ^ (prefixWord ++ tailWord_2089401).sum := by decide
  have hdescent : baseEnd_2089401 < baseStart_2089401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089420 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_2089420 : Nat := 118140960795 + 2089420 * 2 ^ 59
def prefixEnd_2089420 : Nat := 4983230072969 + 3 ^ 40 * 2089420 * 2
def baseEnd_2089420 : Nat := 715251166078213578893959

theorem tailTrace_2089420 : CollatzResearch.WordTrace tailWord_2089420 prefixEnd_2089420 715251166078213578893959 := by
  unfold tailWord_2089420
  simp only [CollatzResearch.WordTrace]
  refine ⟨38103704045197829685632857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50804938726930439580843809 38103704045197829685632857)
  ·
    refine ⟨28577778033898372264224643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38103704045197829685632857 28577778033898372264224643)
    ·
      refine ⟨42866667050847558396336965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28577778033898372264224643 42866667050847558396336965)
      ·
        refine ⟨8037500072033917199313181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42866667050847558396336965 8037500072033917199313181)
        ·
          refine ⟨3014062527012718949742443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8037500072033917199313181 3014062527012718949742443)
          ·
            refine ⟨4521093790519078424613665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014062527012718949742443 4521093790519078424613665)
            ·
              refine ⟨3390820342889308818460249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4521093790519078424613665 3390820342889308818460249)
              ·
                refine ⟨2543115257166981613845187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390820342889308818460249 2543115257166981613845187)
                ·
                  refine ⟨3814672885750472420767781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543115257166981613845187 3814672885750472420767781)
                  ·
                    refine ⟨715251166078213578893959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3814672885750472420767781 715251166078213578893959)
                    ·
                      rfl

theorem cell22_2089420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_2089420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089420 prefixEnd_2089420 := by exact prefixLift 2089420
  have htrace : WordTrace (prefixWord ++ tailWord_2089420) baseStart_2089420 baseEnd_2089420 := by
    simpa [prefixWord, tailWord_2089420, baseEnd_2089420] using wordTrace_append hprefix tailTrace_2089420
  have hstable : (prefixWord ++ tailWord_2089420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089420).length < 2 ^ (prefixWord ++ tailWord_2089420).sum := by decide
  have hdescent : baseEnd_2089420 < baseStart_2089420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089448 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2089448 : Nat := 118140960795 + 2089448 * 2 ^ 59
def prefixEnd_2089448 : Nat := 4983230072969 + 3 ^ 40 * 2089448 * 2
def baseEnd_2089448 : Nat := 715260751050430839193873

theorem tailTrace_2089448 : CollatzResearch.WordTrace tailWord_2089448 prefixEnd_2089448 715260751050430839193873 := by
  unfold tailWord_2089448
  simp only [CollatzResearch.WordTrace]
  refine ⟨38104214667147110076642499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50805619556196146768856665 38104214667147110076642499)
  ·
    refine ⟨57156322000720665114963749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38104214667147110076642499 57156322000720665114963749)
    ·
      refine ⟨10716810375135124709055703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57156322000720665114963749 10716810375135124709055703)
      ·
        refine ⟨16075215562702687063583555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716810375135124709055703 16075215562702687063583555)
        ·
          refine ⟨24112823344054030595375333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16075215562702687063583555 24112823344054030595375333)
          ·
            refine ⟨4521154377010130736632875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24112823344054030595375333 4521154377010130736632875)
            ·
              refine ⟨6781731565515196104949313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521154377010130736632875 6781731565515196104949313)
              ·
                refine ⟨5086298674136397078711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6781731565515196104949313 5086298674136397078711985)
                ·
                  refine ⟨3814724005602297809033989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086298674136397078711985 3814724005602297809033989)
                  ·
                    refine ⟨715260751050430839193873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3814724005602297809033989 715260751050430839193873)
                    ·
                      rfl

theorem cell22_2089448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2089448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089448 prefixEnd_2089448 := by exact prefixLift 2089448
  have htrace : WordTrace (prefixWord ++ tailWord_2089448) baseStart_2089448 baseEnd_2089448 := by
    simpa [prefixWord, tailWord_2089448, baseEnd_2089448] using wordTrace_append hprefix tailTrace_2089448
  have hstable : (prefixWord ++ tailWord_2089448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089448).length < 2 ^ (prefixWord ++ tailWord_2089448).sum := by decide
  have hdescent : baseEnd_2089448 < baseStart_2089448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089536 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_2089536 : Nat := 118140960795 + 2089536 * 2 ^ 59
def prefixEnd_2089536 : Nat := 4983230072969 + 3 ^ 40 * 2089536 * 2
def baseEnd_2089536 : Nat := 238430291749609314331201

theorem tailTrace_2089536 : CollatzResearch.WordTrace tailWord_2089536 prefixEnd_2089536 238430291749609314331201 := by
  unfold tailWord_2089536
  simp only [CollatzResearch.WordTrace]
  refine ⟨38105819478987705591244231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50807759305316940788325641 38105819478987705591244231)
  ·
    refine ⟨57158729218481558386866347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38105819478987705591244231 57158729218481558386866347)
    ·
      refine ⟨85738093827722337580299521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57158729218481558386866347 85738093827722337580299521)
      ·
        refine ⟨64303570370791753185224641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85738093827722337580299521 64303570370791753185224641)
        ·
          refine ⟨48227677778093814888918481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64303570370791753185224641 48227677778093814888918481)
          ·
            refine ⟨36170758333570361166688861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48227677778093814888918481 36170758333570361166688861)
            ·
              refine ⟨13564034375088885437508323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36170758333570361166688861 13564034375088885437508323)
              ·
                refine ⟨20346051562633328156262485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13564034375088885437508323 20346051562633328156262485)
                ·
                  refine ⟨238430291749609314331201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20346051562633328156262485 238430291749609314331201)
                  ·
                    rfl

theorem cell22_2089536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_2089536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089536 prefixEnd_2089536 := by exact prefixLift 2089536
  have htrace : WordTrace (prefixWord ++ tailWord_2089536) baseStart_2089536 baseEnd_2089536 := by
    simpa [prefixWord, tailWord_2089536, baseEnd_2089536] using wordTrace_append hprefix tailTrace_2089536
  have hstable : (prefixWord ++ tailWord_2089536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089536).length < 2 ^ (prefixWord ++ tailWord_2089536).sum := by decide
  have hdescent : baseEnd_2089536 < baseStart_2089536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089692 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2089692 : Nat := 118140960795 + 2089692 * 2 ^ 59
def prefixEnd_2089692 : Nat := 4983230072969 + 3 ^ 40 * 2089692 * 2
def baseEnd_2089692 : Nat := 715344277236895536093125

theorem tailTrace_2089692 : CollatzResearch.WordTrace tailWord_2089692 prefixEnd_2089692 715344277236895536093125 := by
  unfold tailWord_2089692
  simp only [CollatzResearch.WordTrace]
  refine ⟨38108664372705124912583665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50811552496940166550111553 38108664372705124912583665)
  ·
    refine ⟨28581498279528843684437749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38108664372705124912583665 28581498279528843684437749)
    ·
      refine ⟨2679515463705829095416039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28581498279528843684437749 2679515463705829095416039)
      ·
        refine ⟨4019273195558743643124059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679515463705829095416039 4019273195558743643124059)
        ·
          refine ⟨6028909793338115464686089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019273195558743643124059 6028909793338115464686089)
          ·
            refine ⟨4521682345003586598514567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028909793338115464686089 4521682345003586598514567)
            ·
              refine ⟨6782523517505379897771851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521682345003586598514567 6782523517505379897771851)
              ·
                refine ⟨10173785276258069846657777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782523517505379897771851 10173785276258069846657777)
                ·
                  refine ⟨7630338957193552384993333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10173785276258069846657777 7630338957193552384993333)
                  ·
                    refine ⟨715344277236895536093125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7630338957193552384993333 715344277236895536093125)
                    ·
                      rfl

theorem cell22_2089692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2089692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089692 prefixEnd_2089692 := by exact prefixLift 2089692
  have htrace : WordTrace (prefixWord ++ tailWord_2089692) baseStart_2089692 baseEnd_2089692 := by
    simpa [prefixWord, tailWord_2089692, baseEnd_2089692] using wordTrace_append hprefix tailTrace_2089692
  have hstable : (prefixWord ++ tailWord_2089692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089692).length < 2 ^ (prefixWord ++ tailWord_2089692).sum := by decide
  have hdescent : baseEnd_2089692 < baseStart_2089692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089720 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_2089720 : Nat := 118140960795 + 2089720 * 2 ^ 59
def prefixEnd_2089720 : Nat := 4983230072969 + 3 ^ 40 * 2089720 * 2
def baseEnd_2089720 : Nat := 715353862209112796393039

theorem tailTrace_2089720 : CollatzResearch.WordTrace tailWord_2089720 prefixEnd_2089720 715353862209112796393039 := by
  unfold tailWord_2089720
  simp only [CollatzResearch.WordTrace]
  refine ⟨38109174994654405303593307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50812233326205873738124409 38109174994654405303593307)
  ·
    refine ⟨57163762491981607955389961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38109174994654405303593307 57163762491981607955389961)
    ·
      refine ⟨42872821868986205966542471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57163762491981607955389961 42872821868986205966542471)
      ·
        refine ⟨64309232803479308949813707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42872821868986205966542471 64309232803479308949813707)
        ·
          refine ⟨96463849205218963424720561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64309232803479308949813707 96463849205218963424720561)
          ·
            refine ⟨72347886903914222568540421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96463849205218963424720561 72347886903914222568540421)
            ·
              refine ⟨13565228794483916731601329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72347886903914222568540421 13565228794483916731601329)
              ·
                refine ⟨10173921595862937548700997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13565228794483916731601329 10173921595862937548700997)
                ·
                  refine ⟨1907610299224300790381437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10173921595862937548700997 1907610299224300790381437)
                  ·
                    refine ⟨715353862209112796393039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907610299224300790381437 715353862209112796393039)
                    ·
                      rfl

theorem cell22_2089720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_2089720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089720 prefixEnd_2089720 := by exact prefixLift 2089720
  have htrace : WordTrace (prefixWord ++ tailWord_2089720) baseStart_2089720 baseEnd_2089720 := by
    simpa [prefixWord, tailWord_2089720, baseEnd_2089720] using wordTrace_append hprefix tailTrace_2089720
  have hstable : (prefixWord ++ tailWord_2089720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089720).length < 2 ^ (prefixWord ++ tailWord_2089720).sum := by decide
  have hdescent : baseEnd_2089720 < baseStart_2089720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089724 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_2089724 : Nat := 118140960795 + 2089724 * 2 ^ 59
def prefixEnd_2089724 : Nat := 4983230072969 + 3 ^ 40 * 2089724 * 2
def baseEnd_2089724 : Nat := 715355231490858119293027

theorem tailTrace_2089724 : CollatzResearch.WordTrace tailWord_2089724 prefixEnd_2089724 715355231490858119293027 := by
  unfold tailWord_2089724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38109247940647159645166113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50812330587529546193554817 38109247940647159645166113)
  ·
    refine ⟨28581935955485369733874585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38109247940647159645166113 28581935955485369733874585)
    ·
      refine ⟨21436451966614027300405939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28581935955485369733874585 21436451966614027300405939)
      ·
        refine ⟨32154677949921040950608909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21436451966614027300405939 32154677949921040950608909)
        ·
          refine ⟨12058004231220390356478341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32154677949921040950608909 12058004231220390356478341)
          ·
            refine ⟨2260875793353823191839689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12058004231220390356478341 2260875793353823191839689)
            ·
              refine ⟨1695656845015367393879767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260875793353823191839689 1695656845015367393879767)
              ·
                refine ⟨2543485267523051090819651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695656845015367393879767 2543485267523051090819651)
                ·
                  refine ⟨3815227901284576636229477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543485267523051090819651 3815227901284576636229477)
                  ·
                    refine ⟨715355231490858119293027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815227901284576636229477 715355231490858119293027)
                    ·
                      rfl

theorem cell22_2089724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_2089724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089724 prefixEnd_2089724 := by exact prefixLift 2089724
  have htrace : WordTrace (prefixWord ++ tailWord_2089724) baseStart_2089724 baseEnd_2089724 := by
    simpa [prefixWord, tailWord_2089724, baseEnd_2089724] using wordTrace_append hprefix tailTrace_2089724
  have hstable : (prefixWord ++ tailWord_2089724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089724).length < 2 ^ (prefixWord ++ tailWord_2089724).sum := by decide
  have hdescent : baseEnd_2089724 < baseStart_2089724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089737 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_2089737 : Nat := 118140960795 + 2089737 * 2 ^ 59
def prefixEnd_2089737 : Nat := 4983230072969 + 3 ^ 40 * 2089737 * 2
def baseEnd_2089737 : Nat := 715359681656530418717987

theorem tailTrace_2089737 : CollatzResearch.WordTrace tailWord_2089737 prefixEnd_2089737 715359681656530418717987 := by
  unfold tailWord_2089737
  simp only [CollatzResearch.WordTrace]
  refine ⟨76218970030247222510555465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50812646686831481673703643 76218970030247222510555465)
  ·
    refine ⟨57164227522685416882916599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76218970030247222510555465 57164227522685416882916599)
    ·
      refine ⟨85746341284028125324374899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57164227522685416882916599 85746341284028125324374899)
      ·
        refine ⟨128619511926042187986562349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85746341284028125324374899 128619511926042187986562349)
        ·
          refine ⟨48232316972265820494960881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128619511926042187986562349 48232316972265820494960881)
          ·
            refine ⟨36174237729199365371220661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48232316972265820494960881 36174237729199365371220661)
            ·
              refine ⟨3391334787112440503551937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36174237729199365371220661 3391334787112440503551937)
              ·
                refine ⟨2543501090334330377663953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391334787112440503551937 2543501090334330377663953)
                ·
                  refine ⟨1907625817750747783247965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543501090334330377663953 1907625817750747783247965)
                  ·
                    refine ⟨715359681656530418717987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907625817750747783247965 715359681656530418717987)
                    ·
                      rfl

theorem cell22_2089737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_2089737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089737 prefixEnd_2089737 := by exact prefixLift 2089737
  have htrace : WordTrace (prefixWord ++ tailWord_2089737) baseStart_2089737 baseEnd_2089737 := by
    simpa [prefixWord, tailWord_2089737, baseEnd_2089737] using wordTrace_append hprefix tailTrace_2089737
  have hstable : (prefixWord ++ tailWord_2089737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089737).length < 2 ^ (prefixWord ++ tailWord_2089737).sum := by decide
  have hdescent : baseEnd_2089737 < baseStart_2089737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089754 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_2089754 : Nat := 118140960795 + 2089754 * 2 ^ 59
def prefixEnd_2089754 : Nat := 4983230072969 + 3 ^ 40 * 2089754 * 2
def baseEnd_2089754 : Nat := 715365501103948041042935

theorem tailTrace_2089754 : CollatzResearch.WordTrace tailWord_2089754 prefixEnd_2089754 715365501103948041042935 := by
  unfold tailWord_2089754
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054897517796408603481079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50813060047457089609282877 19054897517796408603481079)
  ·
    refine ⟨28582346276694612905221619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19054897517796408603481079 28582346276694612905221619)
    ·
      refine ⟨42873519415041919357832429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28582346276694612905221619 42873519415041919357832429)
      ·
        refine ⟨16077569780640719759187161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42873519415041919357832429 16077569780640719759187161)
        ·
          refine ⟨12058177335480539819390371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16077569780640719759187161 12058177335480539819390371)
          ·
            refine ⟨18087266003220809729085557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12058177335480539819390371 18087266003220809729085557)
            ·
              refine ⟨1695681187801950912101771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18087266003220809729085557 1695681187801950912101771)
              ·
                refine ⟨2543521781702926368152657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695681187801950912101771 2543521781702926368152657)
                ·
                  refine ⟨1907641336277194776114493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543521781702926368152657 1907641336277194776114493)
                  ·
                    refine ⟨715365501103948041042935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907641336277194776114493 715365501103948041042935)
                    ·
                      rfl

theorem cell22_2089754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_2089754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089754 prefixEnd_2089754 := by exact prefixLift 2089754
  have htrace : WordTrace (prefixWord ++ tailWord_2089754) baseStart_2089754 baseEnd_2089754 := by
    simpa [prefixWord, tailWord_2089754, baseEnd_2089754] using wordTrace_append hprefix tailTrace_2089754
  have hstable : (prefixWord ++ tailWord_2089754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089754).length < 2 ^ (prefixWord ++ tailWord_2089754).sum := by decide
  have hdescent : baseEnd_2089754 < baseStart_2089754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089773 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2089773 : Nat := 118140960795 + 2089773 * 2 ^ 59
def prefixEnd_2089773 : Nat := 4983230072969 + 3 ^ 40 * 2089773 * 2
def baseEnd_2089773 : Nat := 238457335064079441605959

theorem tailTrace_2089773 : CollatzResearch.WordTrace tailWord_2089773 prefixEnd_2089773 238457335064079441605959 := by
  unfold tailWord_2089773
  simp only [CollatzResearch.WordTrace]
  refine ⟨76220283058116800658865973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50813522038744533772577315 76220283058116800658865973)
  ·
    refine ⟨7145651536698450061768685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76220283058116800658865973 7145651536698450061768685)
    ·
      refine ⟨2679619326261918773163257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7145651536698450061768685 2679619326261918773163257)
      ·
        refine ⟨2009714494696439079872443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2679619326261918773163257 2009714494696439079872443)
        ·
          refine ⟨3014571742044658619808665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009714494696439079872443 3014571742044658619808665)
          ·
            refine ⟨2260928806533493964856499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014571742044658619808665 2260928806533493964856499)
            ·
              refine ⟨3391393209800240947284749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260928806533493964856499 3391393209800240947284749)
              ·
                refine ⟨1271772453675090355231781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3391393209800240947284749 1271772453675090355231781)
                ·
                  refine ⟨238457335064079441605959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271772453675090355231781 238457335064079441605959)
                  ·
                    rfl

theorem cell22_2089773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2089773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089773 prefixEnd_2089773 := by exact prefixLift 2089773
  have htrace : WordTrace (prefixWord ++ tailWord_2089773) baseStart_2089773 baseEnd_2089773 := by
    simpa [prefixWord, tailWord_2089773, baseEnd_2089773] using wordTrace_append hprefix tailTrace_2089773
  have hstable : (prefixWord ++ tailWord_2089773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089773).length < 2 ^ (prefixWord ++ tailWord_2089773).sum := by decide
  have hdescent : baseEnd_2089773 < baseStart_2089773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089795 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 5]
def baseStart_2089795 : Nat := 118140960795 + 2089795 * 2 ^ 59
def prefixEnd_2089795 : Nat := 4983230072969 + 3 ^ 40 * 2089795 * 2
def baseEnd_2089795 : Nat := 238459845413945866922603

theorem tailTrace_2089795 : CollatzResearch.WordTrace tailWord_2089795 prefixEnd_2089795 238459845413945866922603 := by
  unfold tailWord_2089795
  simp only [CollatzResearch.WordTrace]
  refine ⟨76221085464037098416166839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50814056976024732277444559 76221085464037098416166839)
  ·
    refine ⟨114331628196055647624250259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76221085464037098416166839 114331628196055647624250259)
    ·
      refine ⟨171497442294083471436375389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114331628196055647624250259 171497442294083471436375389)
      ·
        refine ⟨64311540860281301788640771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171497442294083471436375389 64311540860281301788640771)
        ·
          refine ⟨96467311290421952682961157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64311540860281301788640771 96467311290421952682961157)
          ·
            refine ⟨18087620866954116128055217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96467311290421952682961157 18087620866954116128055217)
            ·
              refine ⟨13565715650215587096041413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18087620866954116128055217 13565715650215587096041413)
              ·
                refine ⟨2543571684415422580507765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13565715650215587096041413 2543571684415422580507765)
                ·
                  refine ⟨238459845413945866922603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2543571684415422580507765 238459845413945866922603)
                  ·
                    rfl

theorem cell22_2089795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 5].length) (baseStart_2089795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089795 prefixEnd_2089795 := by exact prefixLift 2089795
  have htrace : WordTrace (prefixWord ++ tailWord_2089795) baseStart_2089795 baseEnd_2089795 := by
    simpa [prefixWord, tailWord_2089795, baseEnd_2089795] using wordTrace_append hprefix tailTrace_2089795
  have hstable : (prefixWord ++ tailWord_2089795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089795).length < 2 ^ (prefixWord ++ tailWord_2089795).sum := by decide
  have hdescent : baseEnd_2089795 < baseStart_2089795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089805 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2089805 : Nat := 118140960795 + 2089805 * 2 ^ 59
def prefixEnd_2089805 : Nat := 4983230072969 + 3 ^ 40 * 2089805 * 2
def baseEnd_2089805 : Nat := 715382959446200908017779

theorem tailTrace_2089805 : CollatzResearch.WordTrace tailWord_2089805 prefixEnd_2089805 715382959446200908017779 := by
  unfold tailWord_2089805
  simp only [CollatzResearch.WordTrace]
  refine ⟨76221450194000870124030869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50814300129333913416020579 76221450194000870124030869)
  ·
    refine ⟨3572880477843790787063947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76221450194000870124030869 3572880477843790787063947)
    ·
      refine ⟨5359320716765686180595921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572880477843790787063947 5359320716765686180595921)
      ·
        refine ⟨4019490537574264635446941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5359320716765686180595921 4019490537574264635446941)
        ·
          refine ⟨1507308951590349238292603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4019490537574264635446941 1507308951590349238292603)
          ·
            refine ⟨2260963427385523857438905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507308951590349238292603 2260963427385523857438905)
            ·
              refine ⟨1695722570539142893079179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260963427385523857438905 1695722570539142893079179)
              ·
                refine ⟨2543583855808714339618769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695722570539142893079179 2543583855808714339618769)
                ·
                  refine ⟨1907687891856535754714077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543583855808714339618769 1907687891856535754714077)
                  ·
                    refine ⟨715382959446200908017779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907687891856535754714077 715382959446200908017779)
                    ·
                      rfl

theorem cell22_2089805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2089805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089805 prefixEnd_2089805 := by exact prefixLift 2089805
  have htrace : WordTrace (prefixWord ++ tailWord_2089805) baseStart_2089805 baseEnd_2089805 := by
    simpa [prefixWord, tailWord_2089805, baseEnd_2089805] using wordTrace_append hprefix tailTrace_2089805
  have hstable : (prefixWord ++ tailWord_2089805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089805).length < 2 ^ (prefixWord ++ tailWord_2089805).sum := by decide
  have hdescent : baseEnd_2089805 < baseStart_2089805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089810 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2089810 : Nat := 118140960795 + 2089810 * 2 ^ 59
def prefixEnd_2089810 : Nat := 4983230072969 + 3 ^ 40 * 2089810 * 2
def baseEnd_2089810 : Nat := 715384671048382561642763

theorem tailTrace_2089810 : CollatzResearch.WordTrace tailWord_2089810 prefixEnd_2089810 715384671048382561642763 := by
  unfold tailWord_2089810
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055408139745688994490721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50814421705988503985308589 19055408139745688994490721)
  ·
    refine ⟨14291556104809266745868041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19055408139745688994490721 14291556104809266745868041)
    ·
      refine ⟨10718667078606950059401031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14291556104809266745868041 10718667078606950059401031)
      ·
        refine ⟨16078000617910425089101547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10718667078606950059401031 16078000617910425089101547)
        ·
          refine ⟨24117000926865637633652321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16078000617910425089101547 24117000926865637633652321)
          ·
            refine ⟨18087750695149228225239241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24117000926865637633652321 18087750695149228225239241)
            ·
              refine ⟨13565813021361921168929431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18087750695149228225239241 13565813021361921168929431)
              ·
                refine ⟨20348719532042881753394147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13565813021361921168929431 20348719532042881753394147)
                ·
                  refine ⟨30523079298064322630091221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20348719532042881753394147 30523079298064322630091221)
                  ·
                    refine ⟨715384671048382561642763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30523079298064322630091221 715384671048382561642763)
                    ·
                      rfl

theorem cell22_2089810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2089810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089810 prefixEnd_2089810 := by exact prefixLift 2089810
  have htrace : WordTrace (prefixWord ++ tailWord_2089810) baseStart_2089810 baseEnd_2089810 := by
    simpa [prefixWord, tailWord_2089810, baseEnd_2089810] using wordTrace_append hprefix tailTrace_2089810
  have hstable : (prefixWord ++ tailWord_2089810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089810).length < 2 ^ (prefixWord ++ tailWord_2089810).sum := by decide
  have hdescent : baseEnd_2089810 < baseStart_2089810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089842 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_2089842 : Nat := 118140960795 + 2089842 * 2 ^ 59
def prefixEnd_2089842 : Nat := 4983230072969 + 3 ^ 40 * 2089842 * 2
def baseEnd_2089842 : Nat := 715395625302345144842665

theorem tailTrace_2089842 : CollatzResearch.WordTrace tailWord_2089842 prefixEnd_2089842 715395625302345144842665 := by
  unfold tailWord_2089842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055699923716706360781945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50815199796577883628751853 19055699923716706360781945)
  ·
    refine ⟨14291774942787529770586459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19055699923716706360781945 14291774942787529770586459)
    ·
      refine ⟨21437662414181294655879689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14291774942787529770586459 21437662414181294655879689)
      ·
        refine ⟨16078246810635970991909767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21437662414181294655879689 16078246810635970991909767)
        ·
          refine ⟨24117370215953956487864651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16078246810635970991909767 24117370215953956487864651)
          ·
            refine ⟨36176055323930934731796977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24117370215953956487864651 36176055323930934731796977)
            ·
              refine ⟨27132041492948201048847733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36176055323930934731796977 27132041492948201048847733)
              ·
                refine ⟨2543628889963893848329475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27132041492948201048847733 2543628889963893848329475)
                ·
                  refine ⟨3815443334945840772494213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543628889963893848329475 3815443334945840772494213)
                  ·
                    refine ⟨715395625302345144842665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815443334945840772494213 715395625302345144842665)
                    ·
                      rfl

theorem cell22_2089842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_2089842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089842 prefixEnd_2089842 := by exact prefixLift 2089842
  have htrace : WordTrace (prefixWord ++ tailWord_2089842) baseStart_2089842 baseEnd_2089842 := by
    simpa [prefixWord, tailWord_2089842, baseEnd_2089842] using wordTrace_append hprefix tailTrace_2089842
  have hstable : (prefixWord ++ tailWord_2089842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089842).length < 2 ^ (prefixWord ++ tailWord_2089842).sum := by decide
  have hdescent : baseEnd_2089842 < baseStart_2089842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089874 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_2089874 : Nat := 118140960795 + 2089874 * 2 ^ 59
def prefixEnd_2089874 : Nat := 4983230072969 + 3 ^ 40 * 2089874 * 2
def baseEnd_2089874 : Nat := 238468859852102576014189

theorem tailTrace_2089874 : CollatzResearch.WordTrace tailWord_2089874 prefixEnd_2089874 238468859852102576014189 := by
  unfold tailWord_2089874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055991707687723727073169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50815977887167263272195117 19055991707687723727073169)
  ·
    refine ⟨14291993780765792795304877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19055991707687723727073169 14291993780765792795304877)
    ·
      refine ⟨5359497667787172298239329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14291993780765792795304877 5359497667787172298239329)
      ·
        refine ⟨4019623250840379223679497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5359497667787172298239329 4019623250840379223679497)
        ·
          refine ⟨3014717438130284417759623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4019623250840379223679497 3014717438130284417759623)
          ·
            refine ⟨4522076157195426626639435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014717438130284417759623 4522076157195426626639435)
            ·
              refine ⟨6783114235793139939959153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522076157195426626639435 6783114235793139939959153)
              ·
                refine ⟨5087335676844854954969365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6783114235793139939959153 5087335676844854954969365)
                ·
                  refine ⟨238468859852102576014189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5087335676844854954969365 238468859852102576014189)
                  ·
                    rfl

theorem cell22_2089874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_2089874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089874 prefixEnd_2089874 := by exact prefixLift 2089874
  have htrace : WordTrace (prefixWord ++ tailWord_2089874) baseStart_2089874 baseEnd_2089874 := by
    simpa [prefixWord, tailWord_2089874, baseEnd_2089874] using wordTrace_append hprefix tailTrace_2089874
  have hstable : (prefixWord ++ tailWord_2089874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089874).length < 2 ^ (prefixWord ++ tailWord_2089874).sum := by decide
  have hdescent : baseEnd_2089874 < baseStart_2089874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089887 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 1, 6]
def baseStart_2089887 : Nat := 118140960795 + 2089887 * 2 ^ 59
def prefixEnd_2089887 : Nat := 4983230072969 + 3 ^ 40 * 2089887 * 2
def baseEnd_2089887 : Nat := 715411029721980027467527

theorem tailTrace_2089887 : CollatzResearch.WordTrace tailWord_2089887 prefixEnd_2089887 715411029721980027467527 := by
  unfold tailWord_2089887
  simp only [CollatzResearch.WordTrace]
  refine ⟨76224440979703798128515915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50816293986469198752343943 76224440979703798128515915)
  ·
    refine ⟨114336661469555697192773873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76224440979703798128515915 114336661469555697192773873)
    ·
      refine ⟨85752496102166772894580405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114336661469555697192773873 85752496102166772894580405)
      ·
        refine ⟨8039296509578134958866913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85752496102166772894580405 8039296509578134958866913)
        ·
          refine ⟨6029472382183601219150185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8039296509578134958866913 6029472382183601219150185)
          ·
            refine ⟨4522104286637700914362639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6029472382183601219150185 4522104286637700914362639)
            ·
              refine ⟨6783156429956551371543959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522104286637700914362639 6783156429956551371543959)
              ·
                refine ⟨10174734644934827057315939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783156429956551371543959 10174734644934827057315939)
                ·
                  refine ⟨15262101967402240585973909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10174734644934827057315939 15262101967402240585973909)
                  ·
                    refine ⟨715411029721980027467527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15262101967402240585973909 715411029721980027467527)
                    ·
                      rfl

theorem cell22_2089887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_2089887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089887 prefixEnd_2089887 := by exact prefixLift 2089887
  have htrace : WordTrace (prefixWord ++ tailWord_2089887) baseStart_2089887 baseEnd_2089887 := by
    simpa [prefixWord, tailWord_2089887, baseEnd_2089887] using wordTrace_append hprefix tailTrace_2089887
  have hstable : (prefixWord ++ tailWord_2089887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089887).length < 2 ^ (prefixWord ++ tailWord_2089887).sum := by decide
  have hdescent : baseEnd_2089887 < baseStart_2089887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089934 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_2089934 : Nat := 118140960795 + 2089934 * 2 ^ 59
def prefixEnd_2089934 : Nat := 4983230072969 + 3 ^ 40 * 2089934 * 2
def baseEnd_2089934 : Nat := 715427118782487571542383

theorem tailTrace_2089934 : CollatzResearch.WordTrace tailWord_2089934 prefixEnd_2089934 715427118782487571542383 := by
  unfold tailWord_2089934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9528269401316690644434607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50817436807022350103651237 9528269401316690644434607)
  ·
    refine ⟨14292404101975035966651911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9528269401316690644434607 14292404101975035966651911)
    ·
      refine ⟨21438606152962553949977867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14292404101975035966651911 21438606152962553949977867)
      ·
        refine ⟨32157909229443830924966801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21438606152962553949977867 32157909229443830924966801)
        ·
          refine ⟨24118431922082873193725101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32157909229443830924966801 24118431922082873193725101)
          ·
            refine ⟨9044411970781077447646913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24118431922082873193725101 9044411970781077447646913)
            ·
              refine ⟨6783308978085808085735185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9044411970781077447646913 6783308978085808085735185)
              ·
                refine ⟨5087481733564356064301389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6783308978085808085735185 5087481733564356064301389)
                ·
                  refine ⟨1907805650086633524113021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5087481733564356064301389 1907805650086633524113021)
                  ·
                    refine ⟨715427118782487571542383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907805650086633524113021 715427118782487571542383)
                    ·
                      rfl

theorem cell22_2089934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_2089934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089934 prefixEnd_2089934 := by exact prefixLift 2089934
  have htrace : WordTrace (prefixWord ++ tailWord_2089934) baseStart_2089934 baseEnd_2089934 := by
    simpa [prefixWord, tailWord_2089934, baseEnd_2089934] using wordTrace_append hprefix tailTrace_2089934
  have hstable : (prefixWord ++ tailWord_2089934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089934).length < 2 ^ (prefixWord ++ tailWord_2089934).sum := by decide
  have hdescent : baseEnd_2089934 < baseStart_2089934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089977 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_2089977 : Nat := 118140960795 + 2089977 * 2 ^ 59
def prefixEnd_2089977 : Nat := 4983230072969 + 3 ^ 40 * 2089977 * 2
def baseEnd_2089977 : Nat := 715441838561249792717251

theorem tailTrace_2089977 : CollatzResearch.WordTrace tailWord_2089977 prefixEnd_2089977 715441838561249792717251 := by
  unfold tailWord_2089977
  simp only [CollatzResearch.WordTrace]
  refine ⟨76227723549377743499292185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50818482366251828999528123 76227723549377743499292185)
  ·
    refine ⟨57170792662033307624469139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76227723549377743499292185 57170792662033307624469139)
    ·
      refine ⟨85756188993049961436703709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57170792662033307624469139 85756188993049961436703709)
      ·
        refine ⟨32158570872393735538763891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85756188993049961436703709 32158570872393735538763891)
        ·
          refine ⟨48237856308590603308145837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32158570872393735538763891 48237856308590603308145837)
          ·
            refine ⟨18089196115721476240554689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48237856308590603308145837 18089196115721476240554689)
            ·
              refine ⟨13566897086791107180416017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18089196115721476240554689 13566897086791107180416017)
              ·
                refine ⟨10175172815093330385312013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13566897086791107180416017 10175172815093330385312013)
                ·
                  refine ⟨3815689805659998894492005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10175172815093330385312013 3815689805659998894492005)
                  ·
                    refine ⟨715441838561249792717251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815689805659998894492005 715441838561249792717251)
                    ·
                      rfl

theorem cell22_2089977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_2089977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089977 prefixEnd_2089977 := by exact prefixLift 2089977
  have htrace : WordTrace (prefixWord ++ tailWord_2089977) baseStart_2089977 baseEnd_2089977 := by
    simpa [prefixWord, tailWord_2089977, baseEnd_2089977] using wordTrace_append hprefix tailTrace_2089977
  have hstable : (prefixWord ++ tailWord_2089977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089977).length < 2 ^ (prefixWord ++ tailWord_2089977).sum := by decide
  have hdescent : baseEnd_2089977 < baseStart_2089977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089994 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2089994 : Nat := 118140960795 + 2089994 * 2 ^ 59
def prefixEnd_2089994 : Nat := 4983230072969 + 3 ^ 40 * 2089994 * 2
def baseEnd_2089994 : Nat := 715447658008667415042199

theorem tailTrace_2089994 : CollatzResearch.WordTrace tailWord_2089994 prefixEnd_2089994 715447658008667415042199 := by
  unfold tailWord_2089994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19057085897579038850665259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50818895726877436935107357 19057085897579038850665259)
  ·
    refine ⟨28585628846368558275997889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19057085897579038850665259 28585628846368558275997889)
    ·
      refine ⟨21439221634776418706998417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28585628846368558275997889 21439221634776418706998417)
      ·
        refine ⟨16079416226082314030248813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21439221634776418706998417 16079416226082314030248813)
        ·
          refine ⟨6029781084780867761343305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16079416226082314030248813 6029781084780867761343305)
          ·
            refine ⟨4522335813585650821007479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6029781084780867761343305 4522335813585650821007479)
            ·
              refine ⟨6783503720378476231511219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522335813585650821007479 6783503720378476231511219)
              ·
                refine ⟨10175255580567714347266829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783503720378476231511219 10175255580567714347266829)
                ·
                  refine ⟨3815720842712892880225061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10175255580567714347266829 3815720842712892880225061)
                  ·
                    refine ⟨715447658008667415042199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815720842712892880225061 715447658008667415042199)
                    ·
                      rfl

theorem cell22_2089994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2089994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089994 prefixEnd_2089994 := by exact prefixLift 2089994
  have htrace : WordTrace (prefixWord ++ tailWord_2089994) baseStart_2089994 baseEnd_2089994 := by
    simpa [prefixWord, tailWord_2089994, baseEnd_2089994] using wordTrace_append hprefix tailTrace_2089994
  have hstable : (prefixWord ++ tailWord_2089994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089994).length < 2 ^ (prefixWord ++ tailWord_2089994).sum := by decide
  have hdescent : baseEnd_2089994 < baseStart_2089994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090041 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_2090041 : Nat := 118140960795 + 2090041 * 2 ^ 59
def prefixEnd_2090041 : Nat := 4983230072969 + 3 ^ 40 * 2090041 * 2
def baseEnd_2090041 : Nat := 715463747069174959117055

theorem tailTrace_2090041 : CollatzResearch.WordTrace tailWord_2090041 prefixEnd_2090041 715463747069174959117055 := by
  unfold tailWord_2090041
  simp only [CollatzResearch.WordTrace]
  refine ⟨76230057821145882429621977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50820038547430588286414651 76230057821145882429621977)
  ·
    refine ⟨57172543365859411822216483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76230057821145882429621977 57172543365859411822216483)
    ·
      refine ⟨85758815048789117733324725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57172543365859411822216483 85758815048789117733324725)
      ·
        refine ⟨8039888910823979787499193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85758815048789117733324725 8039888910823979787499193)
        ·
          refine ⟨6029916683117984840624395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8039888910823979787499193 6029916683117984840624395)
          ·
            refine ⟨9044875024676977260936593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029916683117984840624395 9044875024676977260936593)
            ·
              refine ⟨6783656268507732945702445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9044875024676977260936593 6783656268507732945702445)
              ·
                refine ⟨2543871100690399854638417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6783656268507732945702445 2543871100690399854638417)
                ·
                  refine ⟨1907903325517799890978813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543871100690399854638417 1907903325517799890978813)
                  ·
                    refine ⟨715463747069174959117055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907903325517799890978813 715463747069174959117055)
                    ·
                      rfl

theorem cell22_2090041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_2090041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090041 prefixEnd_2090041 := by exact prefixLift 2090041
  have htrace : WordTrace (prefixWord ++ tailWord_2090041) baseStart_2090041 baseEnd_2090041 := by
    simpa [prefixWord, tailWord_2090041, baseEnd_2090041] using wordTrace_append hprefix tailTrace_2090041
  have hstable : (prefixWord ++ tailWord_2090041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090041).length < 2 ^ (prefixWord ++ tailWord_2090041).sum := by decide
  have hdescent : baseEnd_2090041 < baseStart_2090041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090069 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_2090069 : Nat := 118140960795 + 2090069 * 2 ^ 59
def prefixEnd_2090069 : Nat := 4983230072969 + 3 ^ 40 * 2090069 * 2
def baseEnd_2090069 : Nat := 715473332041392219416969

theorem tailTrace_2090069 : CollatzResearch.WordTrace tailWord_2090069 prefixEnd_2090069 715473332041392219416969 := by
  unfold tailWord_2090069
  simp only [CollatzResearch.WordTrace]
  refine ⟨76231079065044443211641261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50820719376696295474427507 76231079065044443211641261)
  ·
    refine ⟨28586654649391666204365473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76231079065044443211641261 28586654649391666204365473)
    ·
      refine ⟨21439990987043749653274105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28586654649391666204365473 21439990987043749653274105)
      ·
        refine ⟨16079993240282812239955579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21439990987043749653274105 16079993240282812239955579)
        ·
          refine ⟨24119989860424218359933369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16079993240282812239955579 24119989860424218359933369)
          ·
            refine ⟨18089992395318163769950027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24119989860424218359933369 18089992395318163769950027)
            ·
              refine ⟨27134988592977245654925041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18089992395318163769950027 27134988592977245654925041)
              ·
                refine ⟨20351241444732934241193781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27134988592977245654925041 20351241444732934241193781)
                ·
                  refine ⟨1907928885443712585111917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20351241444732934241193781 1907928885443712585111917)
                  ·
                    refine ⟨715473332041392219416969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907928885443712585111917 715473332041392219416969)
                    ·
                      rfl

theorem cell22_2090069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_2090069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090069 prefixEnd_2090069 := by exact prefixLift 2090069
  have htrace : WordTrace (prefixWord ++ tailWord_2090069) baseStart_2090069 baseEnd_2090069 := by
    simpa [prefixWord, tailWord_2090069, baseEnd_2090069] using wordTrace_append hprefix tailTrace_2090069
  have hstable : (prefixWord ++ tailWord_2090069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090069).length < 2 ^ (prefixWord ++ tailWord_2090069).sum := by decide
  have hdescent : baseEnd_2090069 < baseStart_2090069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090097 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_2090097 : Nat := 118140960795 + 2090097 * 2 ^ 59
def prefixEnd_2090097 : Nat := 4983230072969 + 3 ^ 40 * 2090097 * 2
def baseEnd_2090097 : Nat := 715482917013609479716883

theorem tailTrace_2090097 : CollatzResearch.WordTrace tailWord_2090097 prefixEnd_2090097 715482917013609479716883 := by
  unfold tailWord_2090097
  simp only [CollatzResearch.WordTrace]
  refine ⟨76232100308943003993660545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50821400205962002662440363 76232100308943003993660545)
  ·
    refine ⟨57174075231707252995245409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76232100308943003993660545 57174075231707252995245409)
    ·
      refine ⟨42880556423780439746434057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57174075231707252995245409 42880556423780439746434057)
      ·
        refine ⟨32160417317835329809825543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42880556423780439746434057 32160417317835329809825543)
        ·
          refine ⟨48240625976752994714738315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32160417317835329809825543 48240625976752994714738315)
          ·
            refine ⟨72360938965129492072107473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48240625976752994714738315 72360938965129492072107473)
            ·
              refine ⟨54270704223847119054080605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72360938965129492072107473 54270704223847119054080605)
              ·
                refine ⟨20351514083942669645280227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54270704223847119054080605 20351514083942669645280227)
                ·
                  refine ⟨30527271125914004467920341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20351514083942669645280227 30527271125914004467920341)
                  ·
                    refine ⟨715482917013609479716883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30527271125914004467920341 715482917013609479716883)
                    ·
                      rfl

theorem cell22_2090097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_2090097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090097 prefixEnd_2090097 := by exact prefixLift 2090097
  have htrace : WordTrace (prefixWord ++ tailWord_2090097) baseStart_2090097 baseEnd_2090097 := by
    simpa [prefixWord, tailWord_2090097, baseEnd_2090097] using wordTrace_append hprefix tailTrace_2090097
  have hstable : (prefixWord ++ tailWord_2090097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090097).length < 2 ^ (prefixWord ++ tailWord_2090097).sum := by decide
  have hdescent : baseEnd_2090097 < baseStart_2090097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090176 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_2090176 : Nat := 118140960795 + 2090176 * 2 ^ 59
def prefixEnd_2090176 : Nat := 4983230072969 + 3 ^ 40 * 2090176 * 2
def baseEnd_2090176 : Nat := 715509960328079606991641

theorem tailTrace_2090176 : CollatzResearch.WordTrace tailWord_2090176 prefixEnd_2090176 715509960328079606991641 := by
  unfold tailWord_2090176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38117490837828400242893191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50823321117104533657190921 38117490837828400242893191)
  ·
    refine ⟨57176236256742600364339787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38117490837828400242893191 57176236256742600364339787)
    ·
      refine ⟨85764354385113900546509681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57176236256742600364339787 85764354385113900546509681)
      ·
        refine ⟨64323265788835425409882261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85764354385113900546509681 64323265788835425409882261)
        ·
          refine ⟨3015153083851660566088231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64323265788835425409882261 3015153083851660566088231)
          ·
            refine ⟨4522729625777490849132347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015153083851660566088231 4522729625777490849132347)
            ·
              refine ⟨6784094438666236273698521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522729625777490849132347 6784094438666236273698521)
              ·
                refine ⟨5088070828999677205273891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6784094438666236273698521 5088070828999677205273891)
                ·
                  refine ⟨7632106243499515807910837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088070828999677205273891 7632106243499515807910837)
                  ·
                    refine ⟨715509960328079606991641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7632106243499515807910837 715509960328079606991641)
                    ·
                      rfl

theorem cell22_2090176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_2090176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090176 prefixEnd_2090176 := by exact prefixLift 2090176
  have htrace : WordTrace (prefixWord ++ tailWord_2090176) baseStart_2090176 baseEnd_2090176 := by
    simpa [prefixWord, tailWord_2090176, baseEnd_2090176] using wordTrace_append hprefix tailTrace_2090176
  have hstable : (prefixWord ++ tailWord_2090176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090176).length < 2 ^ (prefixWord ++ tailWord_2090176).sum := by decide
  have hdescent : baseEnd_2090176 < baseStart_2090176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090180 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2090180 : Nat := 118140960795 + 2090180 * 2 ^ 59
def prefixEnd_2090180 : Nat := 4983230072969 + 3 ^ 40 * 2090180 * 2
def baseEnd_2090180 : Nat := 715511329609824929891629

theorem tailTrace_2090180 : CollatzResearch.WordTrace tailWord_2090180 prefixEnd_2090180 715511329609824929891629 := by
  unfold tailWord_2090180
  simp only [CollatzResearch.WordTrace]
  refine ⟨38117563783821154584465997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50823418378428206112621329 38117563783821154584465997)
  ·
    refine ⟨14294086418932932969174749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38117563783821154584465997 14294086418932932969174749)
    ·
      refine ⟨5360282407099849863440531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14294086418932932969174749 5360282407099849863440531)
      ·
        refine ⟨8040423610649774795160797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360282407099849863440531 8040423610649774795160797)
        ·
          refine ⟨3015158853993665548185299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8040423610649774795160797 3015158853993665548185299)
          ·
            refine ⟨4522738280990498322277949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015158853993665548185299 4522738280990498322277949)
            ·
              refine ⟨1696026855371436870854231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4522738280990498322277949 1696026855371436870854231)
              ·
                refine ⟨2544040283057155306281347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696026855371436870854231 2544040283057155306281347)
                ·
                  refine ⟨3816060424585732959422021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544040283057155306281347 3816060424585732959422021)
                  ·
                    refine ⟨715511329609824929891629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3816060424585732959422021 715511329609824929891629)
                    ·
                      rfl

theorem cell22_2090180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2090180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090180 prefixEnd_2090180 := by exact prefixLift 2090180
  have htrace : WordTrace (prefixWord ++ tailWord_2090180) baseStart_2090180 baseEnd_2090180 := by
    simpa [prefixWord, tailWord_2090180, baseEnd_2090180] using wordTrace_append hprefix tailTrace_2090180
  have hstable : (prefixWord ++ tailWord_2090180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090180).length < 2 ^ (prefixWord ++ tailWord_2090180).sum := by decide
  have hdescent : baseEnd_2090180 < baseStart_2090180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090234 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_2090234 : Nat := 118140960795 + 2090234 * 2 ^ 59
def prefixEnd_2090234 : Nat := 4983230072969 + 3 ^ 40 * 2090234 * 2
def baseEnd_2090234 : Nat := 238509938304462263013821

theorem tailTrace_2090234 : CollatzResearch.WordTrace tailWord_2090234 prefixEnd_2090234 238509938304462263013821 := by
  unfold tailWord_2090234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059274277361669097849439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50824731406297784260931837 19059274277361669097849439)
  ·
    refine ⟨28588911416042503646774159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19059274277361669097849439 28588911416042503646774159)
    ·
      refine ⟨42883367124063755470161239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28588911416042503646774159 42883367124063755470161239)
      ·
        refine ⟨64325050686095633205241859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42883367124063755470161239 64325050686095633205241859)
        ·
          refine ⟨96487576029143449807862789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64325050686095633205241859 96487576029143449807862789)
          ·
            refine ⟨18091420505464396838974273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96487576029143449807862789 18091420505464396838974273)
            ·
              refine ⟨13568565379098297629230705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18091420505464396838974273 13568565379098297629230705)
              ·
                refine ⟨10176424034323723221923029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13568565379098297629230705 10176424034323723221923029)
                ·
                  refine ⟨238509938304462263013821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10176424034323723221923029 238509938304462263013821)
                  ·
                    rfl

theorem cell22_2090234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_2090234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090234 prefixEnd_2090234 := by exact prefixLift 2090234
  have htrace : WordTrace (prefixWord ++ tailWord_2090234) baseStart_2090234 baseEnd_2090234 := by
    simpa [prefixWord, tailWord_2090234, baseEnd_2090234] using wordTrace_append hprefix tailTrace_2090234
  have hstable : (prefixWord ++ tailWord_2090234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090234).length < 2 ^ (prefixWord ++ tailWord_2090234).sum := by decide
  have hdescent : baseEnd_2090234 < baseStart_2090234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090249 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_2090249 : Nat := 118140960795 + 2090249 * 2 ^ 59
def prefixEnd_2090249 : Nat := 4983230072969 + 3 ^ 40 * 2090249 * 2
def baseEnd_2090249 : Nat := 715534949719931749916417

theorem tailTrace_2090249 : CollatzResearch.WordTrace tailWord_2090249 prefixEnd_2090249 715534949719931749916417 := by
  unfold tailWord_2090249
  simp only [CollatzResearch.WordTrace]
  refine ⟨76237644204392333953193801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50825096136261555968795867 76237644204392333953193801)
  ·
    refine ⟨57178233153294250464895351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76237644204392333953193801 57178233153294250464895351)
    ·
      refine ⟨85767349729941375697343027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57178233153294250464895351 85767349729941375697343027)
      ·
        refine ⟨128651024594912063546014541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85767349729941375697343027 128651024594912063546014541)
        ·
          refine ⟨48244134223092023829755453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128651024594912063546014541 48244134223092023829755453)
          ·
            refine ⟨18091550333659508936158295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48244134223092023829755453 18091550333659508936158295)
            ·
              refine ⟨27137325500489263404237443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091550333659508936158295 27137325500489263404237443)
              ·
                refine ⟨40705988250733895106356165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27137325500489263404237443 40705988250733895106356165)
                ·
                  refine ⟨7632372797012605332441781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40705988250733895106356165 7632372797012605332441781)
                  ·
                    refine ⟨715534949719931749916417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7632372797012605332441781 715534949719931749916417)
                    ·
                      rfl

theorem cell22_2090249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_2090249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090249 prefixEnd_2090249 := by exact prefixLift 2090249
  have htrace : WordTrace (prefixWord ++ tailWord_2090249) baseStart_2090249 baseEnd_2090249 := by
    simpa [prefixWord, tailWord_2090249, baseEnd_2090249] using wordTrace_append hprefix tailTrace_2090249
  have hstable : (prefixWord ++ tailWord_2090249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090249).length < 2 ^ (prefixWord ++ tailWord_2090249).sum := by decide
  have hdescent : baseEnd_2090249 < baseStart_2090249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090251 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 5]
def baseStart_2090251 : Nat := 118140960795 + 2090251 * 2 ^ 59
def prefixEnd_2090251 : Nat := 4983230072969 + 3 ^ 40 * 2090251 * 2
def baseEnd_2090251 : Nat := 238511878120268137122137

theorem tailTrace_2090251 : CollatzResearch.WordTrace tailWord_2090251 prefixEnd_2090251 238511878120268137122137 := by
  unfold tailWord_2090251
  simp only [CollatzResearch.WordTrace]
  refine ⟨76237717150385088294766607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50825144766923392196511071 76237717150385088294766607)
  ·
    refine ⟨114356575725577632442149911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76237717150385088294766607 114356575725577632442149911)
    ·
      refine ⟨171534863588366448663224867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114356575725577632442149911 171534863588366448663224867)
      ·
        refine ⟨257302295382549672994837301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171534863588366448663224867 257302295382549672994837301)
        ·
          refine ⟨24122090192114031843265997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257302295382549672994837301 24122090192114031843265997)
          ·
            refine ⟨9045783822042761941224749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24122090192114031843265997 9045783822042761941224749)
            ·
              refine ⟨3392168933266035727959281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9045783822042761941224749 3392168933266035727959281)
              ·
                refine ⟨2544126699949526795969461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392168933266035727959281 2544126699949526795969461)
                ·
                  refine ⟨238511878120268137122137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2544126699949526795969461 238511878120268137122137)
                  ·
                    rfl

theorem cell22_2090251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 5].length) (baseStart_2090251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090251 prefixEnd_2090251 := by exact prefixLift 2090251
  have htrace : WordTrace (prefixWord ++ tailWord_2090251) baseStart_2090251 baseEnd_2090251 := by
    simpa [prefixWord, tailWord_2090251, baseEnd_2090251] using wordTrace_append hprefix tailTrace_2090251
  have hstable : (prefixWord ++ tailWord_2090251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090251).length < 2 ^ (prefixWord ++ tailWord_2090251).sum := by decide
  have hdescent : baseEnd_2090251 < baseStart_2090251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090266 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_2090266 : Nat := 118140960795 + 2090266 * 2 ^ 59
def prefixEnd_2090266 : Nat := 4983230072969 + 3 ^ 40 * 2090266 * 2
def baseEnd_2090266 : Nat := 715540769167349372241365

theorem tailTrace_2090266 : CollatzResearch.WordTrace tailWord_2090266 prefixEnd_2090266 715540769167349372241365 := by
  unfold tailWord_2090266
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059566061332686464140663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50825509496887163904375101 19059566061332686464140663)
  ·
    refine ⟨28589349091999029696210995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19059566061332686464140663 28589349091999029696210995)
    ·
      refine ⟨42884023637998544544316493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28589349091999029696210995 42884023637998544544316493)
      ·
        refine ⟨16081508864249454204118685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42884023637998544544316493 16081508864249454204118685)
        ·
          refine ⟨6030565824093545326544507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16081508864249454204118685 6030565824093545326544507)
          ·
            refine ⟨9045848736140317989816761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030565824093545326544507 9045848736140317989816761)
            ·
              refine ⟨6784386552105238492362571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9045848736140317989816761 6784386552105238492362571)
              ·
                refine ⟨10176579828157857738543857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784386552105238492362571 10176579828157857738543857)
                ·
                  refine ⟨7632434871118393303907893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10176579828157857738543857 7632434871118393303907893)
                  ·
                    refine ⟨715540769167349372241365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7632434871118393303907893 715540769167349372241365)
                    ·
                      rfl

theorem cell22_2090266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_2090266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090266 prefixEnd_2090266 := by exact prefixLift 2090266
  have htrace : WordTrace (prefixWord ++ tailWord_2090266) baseStart_2090266 baseEnd_2090266 := by
    simpa [prefixWord, tailWord_2090266, baseEnd_2090266] using wordTrace_append hprefix tailTrace_2090266
  have hstable : (prefixWord ++ tailWord_2090266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090266).length < 2 ^ (prefixWord ++ tailWord_2090266).sum := by decide
  have hdescent : baseEnd_2090266 < baseStart_2090266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090328 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_2090328 : Nat := 118140960795 + 2090328 * 2 ^ 59
def prefixEnd_2090328 : Nat := 4983230072969 + 3 ^ 40 * 2090328 * 2
def baseEnd_2090328 : Nat := 715561993034401877191175

theorem tailTrace_2090328 : CollatzResearch.WordTrace tailWord_2090328 prefixEnd_2090328 715561993034401877191175 := by
  unfold tailWord_2090328
  simp only [CollatzResearch.WordTrace]
  refine ⟨38120262785553065222659819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50827017047404086963546425 38120262785553065222659819)
  ·
    refine ⟨57180394178329597833989729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38120262785553065222659819 57180394178329597833989729)
    ·
      refine ⟨42885295633747198375492297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57180394178329597833989729 42885295633747198375492297)
      ·
        refine ⟨32163971725310398781619223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42885295633747198375492297 32163971725310398781619223)
        ·
          refine ⟨48245957587965598172428835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32163971725310398781619223 48245957587965598172428835)
          ·
            refine ⟨72368936381948397258643253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48245957587965598172428835 72368936381948397258643253)
            ·
              refine ⟨6784587785807662242997805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72368936381948397258643253 6784587785807662242997805)
              ·
                refine ⟨2544220419677873341124177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6784587785807662242997805 2544220419677873341124177)
                ·
                  refine ⟨1908165314758405005843133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544220419677873341124177 1908165314758405005843133)
                  ·
                    refine ⟨715561993034401877191175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908165314758405005843133 715561993034401877191175)
                    ·
                      rfl

theorem cell22_2090328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_2090328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090328 prefixEnd_2090328 := by exact prefixLift 2090328
  have htrace : WordTrace (prefixWord ++ tailWord_2090328) baseStart_2090328 baseEnd_2090328 := by
    simpa [prefixWord, tailWord_2090328, baseEnd_2090328] using wordTrace_append hprefix tailTrace_2090328
  have hstable : (prefixWord ++ tailWord_2090328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090328).length < 2 ^ (prefixWord ++ tailWord_2090328).sum := by decide
  have hdescent : baseEnd_2090328 < baseStart_2090328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090371 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 2, 6]
def baseStart_2090371 : Nat := 118140960795 + 2090371 * 2 ^ 59
def prefixEnd_2090371 : Nat := 4983230072969 + 3 ^ 40 * 2090371 * 2
def baseEnd_2090371 : Nat := 715576712813164098366043

theorem tailTrace_2090371 : CollatzResearch.WordTrace tailWord_2090371 prefixEnd_2090371 715576712813164098366043 := by
  unfold tailWord_2090371
  simp only [CollatzResearch.WordTrace]
  refine ⟨76242093909950348789134967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50828062606633565859423311 76242093909950348789134967)
  ·
    refine ⟨114363140864925523183702451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76242093909950348789134967 114363140864925523183702451)
    ·
      refine ⟨171544711297388284775553677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114363140864925523183702451 171544711297388284775553677)
      ·
        refine ⟨64329266736520606790832629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171544711297388284775553677 64329266736520606790832629)
        ·
          refine ⟨6030868756548806886640559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64329266736520606790832629 6030868756548806886640559)
          ·
            refine ⟨9046303134823210329960839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030868756548806886640559 9046303134823210329960839)
            ·
              refine ⟨13569454702234815494941259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046303134823210329960839 13569454702234815494941259)
              ·
                refine ⟨20354182053352223242411889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569454702234815494941259 20354182053352223242411889)
                ·
                  refine ⟨15265636540014167431808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20354182053352223242411889 15265636540014167431808917)
                  ·
                    refine ⟨715576712813164098366043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15265636540014167431808917 715576712813164098366043)
                    ·
                      rfl

theorem cell22_2090371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_2090371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090371 prefixEnd_2090371 := by exact prefixLift 2090371
  have htrace : WordTrace (prefixWord ++ tailWord_2090371) baseStart_2090371 baseEnd_2090371 := by
    simpa [prefixWord, tailWord_2090371, baseEnd_2090371] using wordTrace_append hprefix tailTrace_2090371
  have hstable : (prefixWord ++ tailWord_2090371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090371).length < 2 ^ (prefixWord ++ tailWord_2090371).sum := by decide
  have hdescent : baseEnd_2090371 < baseStart_2090371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090407 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2090407 : Nat := 118140960795 + 2090407 * 2 ^ 59
def prefixEnd_2090407 : Nat := 4983230072969 + 3 ^ 40 * 2090407 * 2
def baseEnd_2090407 : Nat := 715589036348872004465933

theorem tailTrace_2090407 : CollatzResearch.WordTrace tailWord_2090407 prefixEnd_2090407 715589036348872004465933 := by
  unfold tailWord_2090407
  simp only [CollatzResearch.WordTrace]
  refine ⟨76243406937819926937445475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50828937958546617958296983 76243406937819926937445475)
  ·
    refine ⟨114365110406729890406168213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76243406937819926937445475 114365110406729890406168213)
    ·
      refine ⟨5360864550315463612789135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114365110406729890406168213 5360864550315463612789135)
      ·
        refine ⟨8041296825473195419183703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360864550315463612789135 8041296825473195419183703)
        ·
          refine ⟨12061945238209793128775555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041296825473195419183703 12061945238209793128775555)
          ·
            refine ⟨18092917857314689693163333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061945238209793128775555 18092917857314689693163333)
            ·
              refine ⟨3392422098246504317468125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18092917857314689693163333 3392422098246504317468125)
              ·
                refine ⟨1272158286842439119050547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3392422098246504317468125 1272158286842439119050547)
                ·
                  refine ⟨1908237430263658678575821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272158286842439119050547 1908237430263658678575821)
                  ·
                    refine ⟨715589036348872004465933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908237430263658678575821 715589036348872004465933)
                    ·
                      rfl

theorem cell22_2090407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2090407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090407 prefixEnd_2090407 := by exact prefixLift 2090407
  have htrace : WordTrace (prefixWord ++ tailWord_2090407) baseStart_2090407 baseEnd_2090407 := by
    simpa [prefixWord, tailWord_2090407, baseEnd_2090407] using wordTrace_append hprefix tailTrace_2090407
  have hstable : (prefixWord ++ tailWord_2090407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090407).length < 2 ^ (prefixWord ++ tailWord_2090407).sum := by decide
  have hdescent : baseEnd_2090407 < baseStart_2090407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090416 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_2090416 : Nat := 118140960795 + 2090416 * 2 ^ 59
def prefixEnd_2090416 : Nat := 4983230072969 + 3 ^ 40 * 2090416 * 2
def baseEnd_2090416 : Nat := 715592117232798980990905

theorem tailTrace_2090416 : CollatzResearch.WordTrace tailWord_2090416 prefixEnd_2090416 715592117232798980990905 := by
  unfold tailWord_2090416
  simp only [CollatzResearch.WordTrace]
  refine ⟨38121867597393660737261551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50829156796524880983015401 38121867597393660737261551)
  ·
    refine ⟨57182801396090491105892327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38121867597393660737261551 57182801396090491105892327)
    ·
      refine ⟨85774202094135736658838491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57182801396090491105892327 85774202094135736658838491)
      ·
        refine ⟨128661303141203604988257737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85774202094135736658838491 128661303141203604988257737)
        ·
          refine ⟨96495977355902703741193303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128661303141203604988257737 96495977355902703741193303)
          ·
            refine ⟨144743966033854055611789955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96495977355902703741193303 144743966033854055611789955)
            ·
              refine ⟨217115949050781083417684933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144743966033854055611789955 217115949050781083417684933)
              ·
                refine ⟨40709240447021453140815925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217115949050781083417684933 40709240447021453140815925)
                ·
                  refine ⟨3816491291908261231951493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40709240447021453140815925 3816491291908261231951493)
                  ·
                    refine ⟨715592117232798980990905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3816491291908261231951493 715592117232798980990905)
                    ·
                      rfl

theorem cell22_2090416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_2090416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090416 prefixEnd_2090416 := by exact prefixLift 2090416
  have htrace : WordTrace (prefixWord ++ tailWord_2090416) baseStart_2090416 baseEnd_2090416 := by
    simpa [prefixWord, tailWord_2090416, baseEnd_2090416] using wordTrace_append hprefix tailTrace_2090416
  have hstable : (prefixWord ++ tailWord_2090416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090416).length < 2 ^ (prefixWord ++ tailWord_2090416).sum := by decide
  have hdescent : baseEnd_2090416 < baseStart_2090416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090463 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 6, 3]
def baseStart_2090463 : Nat := 118140960795 + 2090463 * 2 ^ 59
def prefixEnd_2090463 : Nat := 4983230072969 + 3 ^ 40 * 2090463 * 2
def baseEnd_2090463 : Nat := 715608206293306525065761

theorem tailTrace_2090463 : CollatzResearch.WordTrace tailWord_2090463 prefixEnd_2090463 715608206293306525065761 := by
  unfold tailWord_2090463
  simp only [CollatzResearch.WordTrace]
  refine ⟨76245449425617048501484043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50830299617078032334322695 76245449425617048501484043)
  ·
    refine ⟨114368174138425572752226065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76245449425617048501484043 114368174138425572752226065)
    ·
      refine ⟨85776130603819179564169549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114368174138425572752226065 85776130603819179564169549)
      ·
        refine ⟨32166048976432192336563581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85776130603819179564169549 32166048976432192336563581)
        ·
          refine ⟨12062268366162072126211343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32166048976432192336563581 12062268366162072126211343)
          ·
            refine ⟨18093402549243108189317015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062268366162072126211343 18093402549243108189317015)
            ·
              refine ⟨27140103823864662283975523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18093402549243108189317015 27140103823864662283975523)
              ·
                refine ⟨40710155735796993425963285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27140103823864662283975523 40710155735796993425963285)
                ·
                  refine ⟨1908288550115484066842029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40710155735796993425963285 1908288550115484066842029)
                  ·
                    refine ⟨715608206293306525065761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908288550115484066842029 715608206293306525065761)
                    ·
                      rfl

theorem cell22_2090463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_2090463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090463 prefixEnd_2090463 := by exact prefixLift 2090463
  have htrace : WordTrace (prefixWord ++ tailWord_2090463) baseStart_2090463 baseEnd_2090463 := by
    simpa [prefixWord, tailWord_2090463, baseEnd_2090463] using wordTrace_append hprefix tailTrace_2090463
  have hstable : (prefixWord ++ tailWord_2090463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090463).length < 2 ^ (prefixWord ++ tailWord_2090463).sum := by decide
  have hdescent : baseEnd_2090463 < baseStart_2090463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090465 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 4]
def baseStart_2090465 : Nat := 118140960795 + 2090465 * 2 ^ 59
def prefixEnd_2090465 : Nat := 4983230072969 + 3 ^ 40 * 2090465 * 2
def baseEnd_2090465 : Nat := 238536296978059728838585

theorem tailTrace_2090465 : CollatzResearch.WordTrace tailWord_2090465 prefixEnd_2090465 238536296978059728838585 := by
  unfold tailWord_2090465
  simp only [CollatzResearch.WordTrace]
  refine ⟨76245522371609802843056849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50830348247739868562037899 76245522371609802843056849)
  ·
    refine ⟨57184141778707352132292637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76245522371609802843056849 57184141778707352132292637)
    ·
      refine ⟨21444053167015257049609739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57184141778707352132292637 21444053167015257049609739)
      ·
        refine ⟨32166079750522885574414609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21444053167015257049609739 32166079750522885574414609)
        ·
          refine ⟨24124559812892164180810957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32166079750522885574414609 24124559812892164180810957)
          ·
            refine ⟨9046709929834561567804109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24124559812892164180810957 9046709929834561567804109)
            ·
              refine ⟨3392516223687960587926541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9046709929834561567804109 3392516223687960587926541)
              ·
                refine ⟨1272193583882985220472453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3392516223687960587926541 1272193583882985220472453)
                ·
                  refine ⟨238536296978059728838585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272193583882985220472453 238536296978059728838585)
                  ·
                    rfl

theorem cell22_2090465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_2090465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090465 prefixEnd_2090465 := by exact prefixLift 2090465
  have htrace : WordTrace (prefixWord ++ tailWord_2090465) baseStart_2090465 baseEnd_2090465 := by
    simpa [prefixWord, tailWord_2090465, baseEnd_2090465] using wordTrace_append hprefix tailTrace_2090465
  have hstable : (prefixWord ++ tailWord_2090465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090465).length < 2 ^ (prefixWord ++ tailWord_2090465).sum := by decide
  have hdescent : baseEnd_2090465 < baseStart_2090465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090493 : List Nat := [1, 4, 1, 1, 1, 5, 2, 7]
def baseStart_2090493 : Nat := 118140960795 + 2090493 * 2 ^ 59
def prefixEnd_2090493 : Nat := 4983230072969 + 3 ^ 40 * 2090493 * 2
def baseEnd_2090493 : Nat := 79513163989599605201741

theorem tailTrace_2090493 : CollatzResearch.WordTrace tailWord_2090493 prefixEnd_2090493 79513163989599605201741 := by
  unfold tailWord_2090493
  simp only [CollatzResearch.WordTrace]
  refine ⟨76246543615508363625076133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50831029077005575750050755 76246543615508363625076133)
  ·
    refine ⟨14296226927907818179701775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76246543615508363625076133 14296226927907818179701775)
    ·
      refine ⟨21444340391861727269552663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14296226927907818179701775 21444340391861727269552663)
      ·
        refine ⟨32166510587792590904328995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21444340391861727269552663 32166510587792590904328995)
        ·
          refine ⟨48249765881688886356493493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32166510587792590904328995 48249765881688886356493493)
          ·
            refine ⟨4523415551408333095921265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48249765881688886356493493 4523415551408333095921265)
            ·
              refine ⟨3392561663556249821940949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523415551408333095921265 3392561663556249821940949)
              ·
                refine ⟨79513163989599605201741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3392561663556249821940949 79513163989599605201741)
                ·
                  rfl

theorem cell22_2090493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 7].length) (baseStart_2090493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090493 prefixEnd_2090493 := by exact prefixLift 2090493
  have htrace : WordTrace (prefixWord ++ tailWord_2090493) baseStart_2090493 baseEnd_2090493 := by
    simpa [prefixWord, tailWord_2090493, baseEnd_2090493] using wordTrace_append hprefix tailTrace_2090493
  have hstable : (prefixWord ++ tailWord_2090493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090493).length < 2 ^ (prefixWord ++ tailWord_2090493).sum := by decide
  have hdescent : baseEnd_2090493 < baseStart_2090493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090497 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_2090497 : Nat := 118140960795 + 2090497 * 2 ^ 59
def prefixEnd_2090497 : Nat := 4983230072969 + 3 ^ 40 * 2090497 * 2
def baseEnd_2090497 : Nat := 715619845188141769715657

theorem tailTrace_2090497 : CollatzResearch.WordTrace tailWord_2090497 prefixEnd_2090497 715619845188141769715657 := by
  unfold tailWord_2090497
  simp only [CollatzResearch.WordTrace]
  refine ⟨76246689507493872308221745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50831126338329248205481163 76246689507493872308221745)
  ·
    refine ⟨57185017130620404231166309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76246689507493872308221745 57185017130620404231166309)
    ·
      refine ⟨10722190711991325793343683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57185017130620404231166309 10722190711991325793343683)
      ·
        refine ⟨16083286067986988690015525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10722190711991325793343683 16083286067986988690015525)
        ·
          refine ⟨3015616137747560379377911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16083286067986988690015525 3015616137747560379377911)
          ·
            refine ⟨4523424206621340569066867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015616137747560379377911 4523424206621340569066867)
            ·
              refine ⟨6785136309932010853600301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523424206621340569066867 6785136309932010853600301)
              ·
                refine ⟨2544426116224504070100113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6785136309932010853600301 2544426116224504070100113)
                ·
                  refine ⟨1908319587168378052575085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544426116224504070100113 1908319587168378052575085)
                  ·
                    refine ⟨715619845188141769715657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908319587168378052575085 715619845188141769715657)
                    ·
                      rfl

theorem cell22_2090497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_2090497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090497 prefixEnd_2090497 := by exact prefixLift 2090497
  have htrace : WordTrace (prefixWord ++ tailWord_2090497) baseStart_2090497 baseEnd_2090497 := by
    simpa [prefixWord, tailWord_2090497, baseEnd_2090497] using wordTrace_append hprefix tailTrace_2090497
  have hstable : (prefixWord ++ tailWord_2090497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090497).length < 2 ^ (prefixWord ++ tailWord_2090497).sum := by decide
  have hdescent : baseEnd_2090497 < baseStart_2090497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090553 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_2090553 : Nat := 118140960795 + 2090553 * 2 ^ 59
def prefixEnd_2090553 : Nat := 4983230072969 + 3 ^ 40 * 2090553 * 2
def baseEnd_2090553 : Nat := 715639015132576290315485

theorem tailTrace_2090553 : CollatzResearch.WordTrace tailWord_2090553 prefixEnd_2090553 715639015132576290315485 := by
  unfold tailWord_2090553
  simp only [CollatzResearch.WordTrace]
  refine ⟨76248731995290993872260313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50832487996860662581506875 76248731995290993872260313)
  ·
    refine ⟨57186548996468245404195235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76248731995290993872260313 57186548996468245404195235)
    ·
      refine ⟨85779823494702368106292853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57186548996468245404195235 85779823494702368106292853)
      ·
        refine ⟨8041858452628347009964955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85779823494702368106292853 8041858452628347009964955)
        ·
          refine ⟨12062787678942520514947433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041858452628347009964955 12062787678942520514947433)
          ·
            refine ⟨9047090759206890386210575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062787678942520514947433 9047090759206890386210575)
            ·
              refine ⟨13570636138810335579315863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047090759206890386210575 13570636138810335579315863)
              ·
                refine ⟨20355954208215503368973795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570636138810335579315863 20355954208215503368973795)
                ·
                  refine ⟨30533931312323255053460693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20355954208215503368973795 30533931312323255053460693)
                  ·
                    refine ⟨715639015132576290315485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30533931312323255053460693 715639015132576290315485)
                    ·
                      rfl

theorem cell22_2090553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_2090553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090553 prefixEnd_2090553 := by exact prefixLift 2090553
  have htrace : WordTrace (prefixWord ++ tailWord_2090553) baseStart_2090553 baseEnd_2090553 := by
    simpa [prefixWord, tailWord_2090553, baseEnd_2090553] using wordTrace_append hprefix tailTrace_2090553
  have hstable : (prefixWord ++ tailWord_2090553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090553).length < 2 ^ (prefixWord ++ tailWord_2090553).sum := by decide
  have hdescent : baseEnd_2090553 < baseStart_2090553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090600 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_2090600 : Nat := 118140960795 + 2090600 * 2 ^ 59
def prefixEnd_2090600 : Nat := 4983230072969 + 3 ^ 40 * 2090600 * 2
def baseEnd_2090600 : Nat := 238551701397694611463447

theorem tailTrace_2090600 : CollatzResearch.WordTrace tailWord_2090600 prefixEnd_2090600 238551701397694611463447 := by
  unfold tailWord_2090600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38125223113060360449610627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50833630817413813932814169 38125223113060360449610627)
  ·
    refine ⟨57187834669590540674415941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38125223113060360449610627 57187834669590540674415941)
    ·
      refine ⟨10722719000548226376452989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57187834669590540674415941 10722719000548226376452989)
      ·
        refine ⟨4021019625205584891169871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10722719000548226376452989 4021019625205584891169871)
        ·
          refine ⟨6031529437808377336754807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021019625205584891169871 6031529437808377336754807)
          ·
            refine ⟨9047294156712566005132211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031529437808377336754807 9047294156712566005132211)
            ·
              refine ⟨13570941235068849007698317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047294156712566005132211 13570941235068849007698317)
              ·
                refine ⟨5089102963150818377886869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13570941235068849007698317 5089102963150818377886869)
                ·
                  refine ⟨238551701397694611463447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5089102963150818377886869 238551701397694611463447)
                  ·
                    rfl

theorem cell22_2090600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_2090600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090600 prefixEnd_2090600 := by exact prefixLift 2090600
  have htrace : WordTrace (prefixWord ++ tailWord_2090600) baseStart_2090600 baseEnd_2090600 := by
    simpa [prefixWord, tailWord_2090600, baseEnd_2090600] using wordTrace_append hprefix tailTrace_2090600
  have hstable : (prefixWord ++ tailWord_2090600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090600).length < 2 ^ (prefixWord ++ tailWord_2090600).sum := by decide
  have hdescent : baseEnd_2090600 < baseStart_2090600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090634 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_2090634 : Nat := 118140960795 + 2090634 * 2 ^ 59
def prefixEnd_2090634 : Nat := 4983230072969 + 3 ^ 40 * 2090634 * 2
def baseEnd_2090634 : Nat := 238555581029306359680079

theorem tailTrace_2090634 : CollatzResearch.WordTrace tailWord_2090634 prefixEnd_2090634 238555581029306359680079 := by
  unfold tailWord_2090634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19062921576999386176489739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50834457538665029803972637 19062921576999386176489739)
  ·
    refine ⟨28594382365499079264734609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19062921576999386176489739 28594382365499079264734609)
    ·
      refine ⟨21445786774124309448550957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28594382365499079264734609 21445786774124309448550957)
      ·
        refine ⟨8042170040296616043206609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21445786774124309448550957 8042170040296616043206609)
        ·
          refine ⟨6031627530222462032404957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8042170040296616043206609 6031627530222462032404957)
          ·
            refine ⟨2261860323833423262151859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6031627530222462032404957 2261860323833423262151859)
            ·
              refine ⟨3392790485750134893227789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261860323833423262151859 3392790485750134893227789)
              ·
                refine ⟨1272296432156300584960421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3392790485750134893227789 1272296432156300584960421)
                ·
                  refine ⟨238555581029306359680079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272296432156300584960421 238555581029306359680079)
                  ·
                    rfl

theorem cell22_2090634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_2090634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090634 prefixEnd_2090634 := by exact prefixLift 2090634
  have htrace : WordTrace (prefixWord ++ tailWord_2090634) baseStart_2090634 baseEnd_2090634 := by
    simpa [prefixWord, tailWord_2090634, baseEnd_2090634] using wordTrace_append hprefix tailTrace_2090634
  have hstable : (prefixWord ++ tailWord_2090634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090634).length < 2 ^ (prefixWord ++ tailWord_2090634).sum := by decide
  have hdescent : baseEnd_2090634 < baseStart_2090634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090720 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_2090720 : Nat := 118140960795 + 2090720 * 2 ^ 59
def prefixEnd_2090720 : Nat := 4983230072969 + 3 ^ 40 * 2090720 * 2
def baseEnd_2090720 : Nat := 715696182645443521389973

theorem tailTrace_2090720 : CollatzResearch.WordTrace tailWord_2090720 prefixEnd_2090720 715696182645443521389973 := by
  unfold tailWord_2090720
  simp only [CollatzResearch.WordTrace]
  refine ⟨38127411492842990696794807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50836548657123987595726409 38127411492842990696794807)
  ·
    refine ⟨57191117239264486045192211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38127411492842990696794807 57191117239264486045192211)
    ·
      refine ⟨85786675858896729067788317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57191117239264486045192211 85786675858896729067788317)
      ·
        refine ⟨32170003447086273400420619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85786675858896729067788317 32170003447086273400420619)
        ·
          refine ⟨48255005170629410100630929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32170003447086273400420619 48255005170629410100630929)
          ·
            refine ⟨36191253877972057575473197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48255005170629410100630929 36191253877972057575473197)
            ·
              refine ⟨13571720204239521590802449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36191253877972057575473197 13571720204239521590802449)
              ·
                refine ⟨10178790153179641193101837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13571720204239521590802449 10178790153179641193101837)
                ·
                  refine ⟨3817046307442365447413189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10178790153179641193101837 3817046307442365447413189)
                  ·
                    refine ⟨715696182645443521389973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3817046307442365447413189 715696182645443521389973)
                    ·
                      rfl

theorem cell22_2090720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_2090720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090720 prefixEnd_2090720 := by exact prefixLift 2090720
  have htrace : WordTrace (prefixWord ++ tailWord_2090720) baseStart_2090720 baseEnd_2090720 := by
    simpa [prefixWord, tailWord_2090720, baseEnd_2090720] using wordTrace_append hprefix tailTrace_2090720
  have hstable : (prefixWord ++ tailWord_2090720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090720).length < 2 ^ (prefixWord ++ tailWord_2090720).sum := by decide
  have hdescent : baseEnd_2090720 < baseStart_2090720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090735 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 6]
def baseStart_2090735 : Nat := 118140960795 + 2090735 * 2 ^ 59
def prefixEnd_2090735 : Nat := 4983230072969 + 3 ^ 40 * 2090735 * 2
def baseEnd_2090735 : Nat := 238567105817329494088309

theorem tailTrace_2090735 : CollatzResearch.WordTrace tailWord_2090735 prefixEnd_2090735 238567105817329494088309 := by
  unfold tailWord_2090735
  simp only [CollatzResearch.WordTrace]
  refine ⟨76255370080631638955385659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50836913387087759303590439 76255370080631638955385659)
  ·
    refine ⟨114383055120947458433078489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76255370080631638955385659 114383055120947458433078489)
    ·
      refine ⟨85787291340710593824808867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114383055120947458433078489 85787291340710593824808867)
      ·
        refine ⟨128680937011065890737213301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85787291340710593824808867 128680937011065890737213301)
        ·
          refine ⟨12063837844787427256613747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128680937011065890737213301 12063837844787427256613747)
          ·
            refine ⟨18095756767181140884920621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063837844787427256613747 18095756767181140884920621)
            ·
              refine ⟨6785908787692927831845233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18095756767181140884920621 6785908787692927831845233)
              ·
                refine ⟨5089431590769695873883925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6785908787692927831845233 5089431590769695873883925)
                ·
                  refine ⟨238567105817329494088309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5089431590769695873883925 238567105817329494088309)
                  ·
                    rfl

theorem cell22_2090735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 6].length) (baseStart_2090735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090735 prefixEnd_2090735 := by exact prefixLift 2090735
  have htrace : WordTrace (prefixWord ++ tailWord_2090735) baseStart_2090735 baseEnd_2090735 := by
    simpa [prefixWord, tailWord_2090735, baseEnd_2090735] using wordTrace_append hprefix tailTrace_2090735
  have hstable : (prefixWord ++ tailWord_2090735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090735).length < 2 ^ (prefixWord ++ tailWord_2090735).sum := by decide
  have hdescent : baseEnd_2090735 < baseStart_2090735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090754 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2090754 : Nat := 118140960795 + 2090754 * 2 ^ 59
def prefixEnd_2090754 : Nat := 4983230072969 + 3 ^ 40 * 2090754 * 2
def baseEnd_2090754 : Nat := 715707821540278766039869

theorem tailTrace_2090754 : CollatzResearch.WordTrace tailWord_2090754 prefixEnd_2090754 715707821540278766039869 := by
  unfold tailWord_2090754
  simp only [CollatzResearch.WordTrace]
  refine ⟨19064015766890701300081829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50837375378375203466884877 19064015766890701300081829)
  ·
    refine ⟨3574502956292006493765343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19064015766890701300081829 3574502956292006493765343)
    ·
      refine ⟨5361754434438009740648015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574502956292006493765343 5361754434438009740648015)
      ·
        refine ⟨8042631651657014610972023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361754434438009740648015 8042631651657014610972023)
        ·
          refine ⟨12063947477485521916458035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042631651657014610972023 12063947477485521916458035)
          ·
            refine ⟨18095921216228282874687053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063947477485521916458035 18095921216228282874687053)
            ·
              refine ⟨6785970456085606078007645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18095921216228282874687053 6785970456085606078007645)
              ·
                refine ⟨2544738921032102279252867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6785970456085606078007645 2544738921032102279252867)
                ·
                  refine ⟨3817108381548153418879301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544738921032102279252867 3817108381548153418879301)
                  ·
                    refine ⟨715707821540278766039869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3817108381548153418879301 715707821540278766039869)
                    ·
                      rfl

theorem cell22_2090754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2090754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090754 prefixEnd_2090754 := by exact prefixLift 2090754
  have htrace : WordTrace (prefixWord ++ tailWord_2090754) baseStart_2090754 baseEnd_2090754 := by
    simpa [prefixWord, tailWord_2090754, baseEnd_2090754] using wordTrace_append hprefix tailTrace_2090754
  have hstable : (prefixWord ++ tailWord_2090754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090754).length < 2 ^ (prefixWord ++ tailWord_2090754).sum := by decide
  have hdescent : baseEnd_2090754 < baseStart_2090754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090767 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 2, 3]
def baseStart_2090767 : Nat := 118140960795 + 2090767 * 2 ^ 59
def prefixEnd_2090767 : Nat := 4983230072969 + 3 ^ 40 * 2090767 * 2
def baseEnd_2090767 : Nat := 715712271705951065464829

theorem tailTrace_2090767 : CollatzResearch.WordTrace tailWord_2090767 prefixEnd_2090767 715712271705951065464829 := by
  unfold tailWord_2090767
  simp only [CollatzResearch.WordTrace]
  refine ⟨76256537216515708420550555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50837691477677138947033703 76256537216515708420550555)
  ·
    refine ⟨114384805824773562630825833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76256537216515708420550555 114384805824773562630825833)
    ·
      refine ⟨85788604368580171973119375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114384805824773562630825833 85788604368580171973119375)
      ·
        refine ⟨128682906552870257959679063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85788604368580171973119375 128682906552870257959679063)
        ·
          refine ⟨193024359829305386939518595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128682906552870257959679063 193024359829305386939518595)
          ·
            refine ⟨289536539743958080409277893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193024359829305386939518595 289536539743958080409277893)
            ·
              refine ⟨54288101201992140076739605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289536539743958080409277893 54288101201992140076739605)
              ·
                refine ⟨2544754743843381566097169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54288101201992140076739605 2544754743843381566097169)
                ·
                  refine ⟨1908566057882536174572877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544754743843381566097169 1908566057882536174572877)
                  ·
                    refine ⟨715712271705951065464829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908566057882536174572877 715712271705951065464829)
                    ·
                      rfl

theorem cell22_2090767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_2090767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090767 prefixEnd_2090767 := by exact prefixLift 2090767
  have htrace : WordTrace (prefixWord ++ tailWord_2090767) baseStart_2090767 baseEnd_2090767 := by
    simpa [prefixWord, tailWord_2090767, baseEnd_2090767] using wordTrace_append hprefix tailTrace_2090767
  have hstable : (prefixWord ++ tailWord_2090767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090767).length < 2 ^ (prefixWord ++ tailWord_2090767).sum := by decide
  have hdescent : baseEnd_2090767 < baseStart_2090767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090780 : List Nat := [2, 2, 3, 1, 1, 2, 2, 9]
def baseStart_2090780 : Nat := 118140960795 + 2090780 * 2 ^ 59
def prefixEnd_2090780 : Nat := 4983230072969 + 3 ^ 40 * 2090780 * 2
def baseEnd_2090780 : Nat := 79524080207958151654421

theorem tailTrace_2090780 : CollatzResearch.WordTrace tailWord_2090780 prefixEnd_2090780 79524080207958151654421 := by
  unfold tailWord_2090780
  simp only [CollatzResearch.WordTrace]
  refine ⟨38128505682734305820386897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50838007576979074427182529 38128505682734305820386897)
  ·
    refine ⟨28596379262050729365290173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38128505682734305820386897 28596379262050729365290173)
    ·
      refine ⟨10723642223269023511983815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28596379262050729365290173 10723642223269023511983815)
      ·
        refine ⟨16085463334903535267975723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10723642223269023511983815 16085463334903535267975723)
        ·
          refine ⟨24128195002355302901963585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16085463334903535267975723 24128195002355302901963585)
          ·
            refine ⟨18096146251766477176472689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24128195002355302901963585 18096146251766477176472689)
            ·
              refine ⟨13572109688824857882354517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18096146251766477176472689 13572109688824857882354517)
              ·
                refine ⟨79524080207958151654421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13572109688824857882354517 79524080207958151654421)
                ·
                  rfl

theorem cell22_2090780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_2090780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090780 prefixEnd_2090780 := by exact prefixLift 2090780
  have htrace : WordTrace (prefixWord ++ tailWord_2090780) baseStart_2090780 baseEnd_2090780 := by
    simpa [prefixWord, tailWord_2090780, baseEnd_2090780] using wordTrace_append hprefix tailTrace_2090780
  have hstable : (prefixWord ++ tailWord_2090780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090780).length < 2 ^ (prefixWord ++ tailWord_2090780).sum := by decide
  have hdescent : baseEnd_2090780 < baseStart_2090780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090812 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_2090812 : Nat := 118140960795 + 2090812 * 2 ^ 59
def prefixEnd_2090812 : Nat := 4983230072969 + 3 ^ 40 * 2090812 * 2
def baseEnd_2090812 : Nat := 715727676125585948089691

theorem tailTrace_2090812 : CollatzResearch.WordTrace tailWord_2090812 prefixEnd_2090812 715727676125585948089691 := by
  unfold tailWord_2090812
  simp only [CollatzResearch.WordTrace]
  refine ⟨38129089250676340552969345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50838785667568454070625793 38129089250676340552969345)
  ·
    refine ⟨28596816938007255414727009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38129089250676340552969345 28596816938007255414727009)
    ·
      refine ⟨21447612703505441561045257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28596816938007255414727009 21447612703505441561045257)
      ·
        refine ⟨16085709527629081170783943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21447612703505441561045257 16085709527629081170783943)
        ·
          refine ⟨24128564291443621756175915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16085709527629081170783943 24128564291443621756175915)
          ·
            refine ⟨36192846437165432634263873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24128564291443621756175915 36192846437165432634263873)
            ·
              refine ⟨27144634827874074475697905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36192846437165432634263873 27144634827874074475697905)
              ·
                refine ⟨20358476120905555856773429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27144634827874074475697905 20358476120905555856773429)
                ·
                  refine ⟨1908607136334895861572509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20358476120905555856773429 1908607136334895861572509)
                  ·
                    refine ⟨715727676125585948089691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908607136334895861572509 715727676125585948089691)
                    ·
                      rfl

theorem cell22_2090812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_2090812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090812 prefixEnd_2090812 := by exact prefixLift 2090812
  have htrace : WordTrace (prefixWord ++ tailWord_2090812) baseStart_2090812 baseEnd_2090812 := by
    simpa [prefixWord, tailWord_2090812, baseEnd_2090812] using wordTrace_append hprefix tailTrace_2090812
  have hstable : (prefixWord ++ tailWord_2090812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090812).length < 2 ^ (prefixWord ++ tailWord_2090812).sum := by decide
  have hdescent : baseEnd_2090812 < baseStart_2090812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090825 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 7]
def baseStart_2090825 : Nat := 118140960795 + 2090825 * 2 ^ 59
def prefixEnd_2090825 : Nat := 4983230072969 + 3 ^ 40 * 2090825 * 2
def baseEnd_2090825 : Nat := 238577375430419415838217

theorem tailTrace_2090825 : CollatzResearch.WordTrace tailWord_2090825 prefixEnd_2090825 238577375430419415838217 := by
  unfold tailWord_2090825
  simp only [CollatzResearch.WordTrace]
  refine ⟨76258652650305584326161929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50839101766870389550774619 76258652650305584326161929)
  ·
    refine ⟨57193989487729188244621447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76258652650305584326161929 57193989487729188244621447)
    ·
      refine ⟨85790984231593782366932171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57193989487729188244621447 85790984231593782366932171)
      ·
        refine ⟨128686476347390673550398257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85790984231593782366932171 128686476347390673550398257)
        ·
          refine ⟨96514857260543005162798693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128686476347390673550398257 96514857260543005162798693)
          ·
            refine ⟨18096535736351813468024755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96514857260543005162798693 18096535736351813468024755)
            ·
              refine ⟨27144803604527720202037133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18096535736351813468024755 27144803604527720202037133)
              ·
                refine ⟨10179301351697895075763925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27144803604527720202037133 10179301351697895075763925)
                ·
                  refine ⟨238577375430419415838217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10179301351697895075763925 238577375430419415838217)
                  ·
                    rfl

theorem cell22_2090825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_2090825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090825 prefixEnd_2090825 := by exact prefixLift 2090825
  have htrace : WordTrace (prefixWord ++ tailWord_2090825) baseStart_2090825 baseEnd_2090825 := by
    simpa [prefixWord, tailWord_2090825, baseEnd_2090825] using wordTrace_append hprefix tailTrace_2090825
  have hstable : (prefixWord ++ tailWord_2090825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090825).length < 2 ^ (prefixWord ++ tailWord_2090825).sum := by decide
  have hdescent : baseEnd_2090825 < baseStart_2090825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090842 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_2090842 : Nat := 118140960795 + 2090842 * 2 ^ 59
def prefixEnd_2090842 : Nat := 4983230072969 + 3 ^ 40 * 2090842 * 2
def baseEnd_2090842 : Nat := 238579315246225289946533

theorem tailTrace_2090842 : CollatzResearch.WordTrace tailWord_2090842 prefixEnd_2090842 238579315246225289946533 := by
  unfold tailWord_2090842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19064818172810999057382695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50839515127495997486353853 19064818172810999057382695)
  ·
    refine ⟨28597227259216498586074043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19064818172810999057382695 28597227259216498586074043)
    ·
      refine ⟨42895840888824747879111065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28597227259216498586074043 42895840888824747879111065)
      ·
        refine ⟨32171880666618560909333299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42895840888824747879111065 32171880666618560909333299)
        ·
          refine ⟨48257820999927841363999949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32171880666618560909333299 48257820999927841363999949)
          ·
            refine ⟨18096682874972940511499981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48257820999927841363999949 18096682874972940511499981)
            ·
              refine ⟨6786256078114852691812493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18096682874972940511499981 6786256078114852691812493)
              ·
                refine ⟨2544846029293069759429685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6786256078114852691812493 2544846029293069759429685)
                ·
                  refine ⟨238579315246225289946533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2544846029293069759429685 238579315246225289946533)
                  ·
                    rfl

theorem cell22_2090842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_2090842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090842 prefixEnd_2090842 := by exact prefixLift 2090842
  have htrace : WordTrace (prefixWord ++ tailWord_2090842) baseStart_2090842 baseEnd_2090842 := by
    simpa [prefixWord, tailWord_2090842, baseEnd_2090842] using wordTrace_append hprefix tailTrace_2090842
  have hstable : (prefixWord ++ tailWord_2090842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090842).length < 2 ^ (prefixWord ++ tailWord_2090842).sum := by decide
  have hdescent : baseEnd_2090842 < baseStart_2090842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090919 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2090919 : Nat := 118140960795 + 2090919 * 2 ^ 59
def prefixEnd_2090919 : Nat := 4983230072969 + 3 ^ 40 * 2090919 * 2
def baseEnd_2090919 : Nat := 715764304412273335664363

theorem tailTrace_2090919 : CollatzResearch.WordTrace tailWord_2090919 prefixEnd_2090919 715764304412273335664363 := by
  unfold tailWord_2090919
  simp only [CollatzResearch.WordTrace]
  refine ⟨76262081111965038380083811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50841387407976692253389207 76262081111965038380083811)
  ·
    refine ⟨114393121667947557570125717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76262081111965038380083811 114393121667947557570125717)
    ·
      refine ⟨5362177578185041761099643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114393121667947557570125717 5362177578185041761099643)
      ·
        refine ⟨8043266367277562641649465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362177578185041761099643 8043266367277562641649465)
        ·
          refine ⟨6032449775458171981237099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8043266367277562641649465 6032449775458171981237099)
          ·
            refine ⟨9048674663187257971855649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032449775458171981237099 9048674663187257971855649)
            ·
              refine ⟨6786505997390443478891737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048674663187257971855649 6786505997390443478891737)
              ·
                refine ⟨5089879498042832609168803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786505997390443478891737 5089879498042832609168803)
                ·
                  refine ⟨7634819247064248913753205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089879498042832609168803 7634819247064248913753205)
                  ·
                    refine ⟨715764304412273335664363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7634819247064248913753205 715764304412273335664363)
                    ·
                      rfl

theorem cell22_2090919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2090919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090919 prefixEnd_2090919 := by exact prefixLift 2090919
  have htrace : WordTrace (prefixWord ++ tailWord_2090919) baseStart_2090919 baseEnd_2090919 := by
    simpa [prefixWord, tailWord_2090919, baseEnd_2090919] using wordTrace_append hprefix tailTrace_2090919
  have hstable : (prefixWord ++ tailWord_2090919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090919).length < 2 ^ (prefixWord ++ tailWord_2090919).sum := by decide
  have hdescent : baseEnd_2090919 < baseStart_2090919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090966 : List Nat := [5, 2, 1, 1, 3, 1, 1, 8]
def baseStart_2090966 : Nat := 118140960795 + 2090966 * 2 ^ 59
def prefixEnd_2090966 : Nat := 4983230072969 + 3 ^ 40 * 2090966 * 2
def baseEnd_2090966 : Nat := 79531154830308986637691

theorem tailTrace_2090966 : CollatzResearch.WordTrace tailWord_2090966 prefixEnd_2090966 79531154830308986637691 := by
  unfold tailWord_2090966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766487208924672837940297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50842530228529843604696501 4766487208924672837940297)
  ·
    refine ⟨3574865406693504628455223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4766487208924672837940297 3574865406693504628455223)
    ·
      refine ⟨5362298110040256942682835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574865406693504628455223 5362298110040256942682835)
      ·
        refine ⟨8043447165060385414024253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362298110040256942682835 8043447165060385414024253)
        ·
          refine ⟨3016292686897644530259095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8043447165060385414024253 3016292686897644530259095)
          ·
            refine ⟨4524439030346466795388643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016292686897644530259095 4524439030346466795388643)
            ·
              refine ⟨6786658545519700193082965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524439030346466795388643 6786658545519700193082965)
              ·
                refine ⟨79531154830308986637691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6786658545519700193082965 79531154830308986637691)
                ·
                  rfl

theorem cell22_2090966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_2090966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090966 prefixEnd_2090966 := by exact prefixLift 2090966
  have htrace : WordTrace (prefixWord ++ tailWord_2090966) baseStart_2090966 baseEnd_2090966 := by
    simpa [prefixWord, tailWord_2090966, baseEnd_2090966] using wordTrace_append hprefix tailTrace_2090966
  have hstable : (prefixWord ++ tailWord_2090966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090966).length < 2 ^ (prefixWord ++ tailWord_2090966).sum := by decide
  have hdescent : baseEnd_2090966 < baseStart_2090966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090972 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 4]
def baseStart_2090972 : Nat := 118140960795 + 2090972 * 2 ^ 59
def prefixEnd_2090972 : Nat := 4983230072969 + 3 ^ 40 * 2090972 * 2
def baseEnd_2090972 : Nat := 238594149131799621363067

theorem tailTrace_2090972 : CollatzResearch.WordTrace tailWord_2090972 prefixEnd_2090972 238594149131799621363067 := by
  unfold tailWord_2090972
  simp only [CollatzResearch.WordTrace]
  refine ⟨38132007090386514215881585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50842676120515352287842113 38132007090386514215881585)
  ·
    refine ⟨28599005317789885661911189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38132007090386514215881585 28599005317789885661911189)
    ·
      refine ⟨1340578374271400890402087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28599005317789885661911189 1340578374271400890402087)
      ·
        refine ⟨2010867561407101335603131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340578374271400890402087 2010867561407101335603131)
        ·
          refine ⟨3016301342110652003404697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010867561407101335603131 3016301342110652003404697)
          ·
            refine ⟨2262226006582989002553523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3016301342110652003404697 2262226006582989002553523)
            ·
              refine ⟨3393339009874483503830285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262226006582989002553523 3393339009874483503830285)
              ·
                refine ⟨1272502128702931313936357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3393339009874483503830285 1272502128702931313936357)
                ·
                  refine ⟨238594149131799621363067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272502128702931313936357 238594149131799621363067)
                  ·
                    rfl

theorem cell22_2090972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_2090972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090972 prefixEnd_2090972 := by exact prefixLift 2090972
  have htrace : WordTrace (prefixWord ++ tailWord_2090972) baseStart_2090972 baseEnd_2090972 := by
    simpa [prefixWord, tailWord_2090972, baseEnd_2090972] using wordTrace_append hprefix tailTrace_2090972
  have hstable : (prefixWord ++ tailWord_2090972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090972).length < 2 ^ (prefixWord ++ tailWord_2090972).sum := by decide
  have hdescent : baseEnd_2090972 < baseStart_2090972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090977 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 7]
def baseStart_2090977 : Nat := 118140960795 + 2090977 * 2 ^ 59
def prefixEnd_2090977 : Nat := 4983230072969 + 3 ^ 40 * 2090977 * 2
def baseEnd_2090977 : Nat := 238594719665860172571395

theorem tailTrace_2090977 : CollatzResearch.WordTrace tailWord_2090977 prefixEnd_2090977 238594719665860172571395 := by
  unfold tailWord_2090977
  simp only [CollatzResearch.WordTrace]
  refine ⟨76264196545754914285695185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50842797697169942857130123 76264196545754914285695185)
  ·
    refine ⟨57198147409316185714271389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76264196545754914285695185 57198147409316185714271389)
    ·
      refine ⟨21449305278493569642851771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57198147409316185714271389 21449305278493569642851771)
      ·
        refine ⟨32173957917740354464277657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21449305278493569642851771 32173957917740354464277657)
        ·
          refine ⟨24130468438305265848208243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32173957917740354464277657 24130468438305265848208243)
          ·
            refine ⟨36195702657457898772312365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24130468438305265848208243 36195702657457898772312365)
            ·
              refine ⟨13573388496546712039617137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36195702657457898772312365 13573388496546712039617137)
              ·
                refine ⟨10180041372410034029712853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13573388496546712039617137 10180041372410034029712853)
                ·
                  refine ⟨238594719665860172571395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10180041372410034029712853 238594719665860172571395)
                  ·
                    rfl

theorem cell22_2090977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_2090977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090977 prefixEnd_2090977 := by exact prefixLift 2090977
  have htrace : WordTrace (prefixWord ++ tailWord_2090977) baseStart_2090977 baseEnd_2090977 := by
    simpa [prefixWord, tailWord_2090977, baseEnd_2090977] using wordTrace_append hprefix tailTrace_2090977
  have hstable : (prefixWord ++ tailWord_2090977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090977).length < 2 ^ (prefixWord ++ tailWord_2090977).sum := by decide
  have hdescent : baseEnd_2090977 < baseStart_2090977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090992 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_2090992 : Nat := 118140960795 + 2090992 * 2 ^ 59
def prefixEnd_2090992 : Nat := 4983230072969 + 3 ^ 40 * 2090992 * 2
def baseEnd_2090992 : Nat := 715789293804125478589139

theorem tailTrace_2090992 : CollatzResearch.WordTrace tailWord_2090992 prefixEnd_2090992 715789293804125478589139 := by
  unfold tailWord_2090992
  simp only [CollatzResearch.WordTrace]
  refine ⟨38132371820350285923745615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50843162427133714564994153 38132371820350285923745615)
  ·
    refine ⟨57198557730525428885618423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38132371820350285923745615 57198557730525428885618423)
    ·
      refine ⟨85797836595788143328427635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57198557730525428885618423 85797836595788143328427635)
      ·
        refine ⟨128696754893682214992641453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85797836595788143328427635 128696754893682214992641453)
        ·
          refine ⟨48261283085130830622240545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128696754893682214992641453 48261283085130830622240545)
          ·
            refine ⟨36195962313848122966680409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48261283085130830622240545 36195962313848122966680409)
            ·
              refine ⟨27146971735386092225010307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36195962313848122966680409 27146971735386092225010307)
              ·
                refine ⟨40720457603079138337515461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27146971735386092225010307 40720457603079138337515461)
                ·
                  refine ⟨7635085800577338438284149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40720457603079138337515461 7635085800577338438284149)
                  ·
                    refine ⟨715789293804125478589139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7635085800577338438284149 715789293804125478589139)
                    ·
                      rfl

theorem cell22_2090992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_2090992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2090992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2090992 prefixEnd_2090992 := by exact prefixLift 2090992
  have htrace : WordTrace (prefixWord ++ tailWord_2090992) baseStart_2090992 baseEnd_2090992 := by
    simpa [prefixWord, tailWord_2090992, baseEnd_2090992] using wordTrace_append hprefix tailTrace_2090992
  have hstable : (prefixWord ++ tailWord_2090992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090992).length < 2 ^ (prefixWord ++ tailWord_2090992).sum := by decide
  have hdescent : baseEnd_2090992 < baseStart_2090992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091056 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 4]
def baseStart_2091056 : Nat := 118140960795 + 2091056 * 2 ^ 59
def prefixEnd_2091056 : Nat := 4983230072969 + 3 ^ 40 * 2091056 * 2
def baseEnd_2091056 : Nat := 238603734104016881662981

theorem tailTrace_2091056 : CollatzResearch.WordTrace tailWord_2091056 prefixEnd_2091056 238603734104016881662981 := by
  unfold tailWord_2091056
  simp only [CollatzResearch.WordTrace]
  refine ⟨38133538956234355388910511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50844718608312473851880681 38133538956234355388910511)
  ·
    refine ⟨57200308434351533083365767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38133538956234355388910511 57200308434351533083365767)
    ·
      refine ⟨85800462651527299625048651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57200308434351533083365767 85800462651527299625048651)
      ·
        refine ⟨128700693977290949437572977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85800462651527299625048651 128700693977290949437572977)
        ·
          refine ⟨96525520482968212078179733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128700693977290949437572977 96525520482968212078179733)
          ·
            refine ⟨4524633772639134941164675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96525520482968212078179733 4524633772639134941164675)
            ·
              refine ⟨6786950658958702411747013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524633772639134941164675 6786950658958702411747013)
              ·
                refine ⟨1272553248554756702202565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6786950658958702411747013 1272553248554756702202565)
                ·
                  refine ⟨238603734104016881662981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272553248554756702202565 238603734104016881662981)
                  ·
                    rfl

theorem cell22_2091056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_2091056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091056 prefixEnd_2091056 := by exact prefixLift 2091056
  have htrace : WordTrace (prefixWord ++ tailWord_2091056) baseStart_2091056 baseEnd_2091056 := by
    simpa [prefixWord, tailWord_2091056, baseEnd_2091056] using wordTrace_append hprefix tailTrace_2091056
  have hstable : (prefixWord ++ tailWord_2091056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091056).length < 2 ^ (prefixWord ++ tailWord_2091056).sum := by decide
  have hdescent : baseEnd_2091056 < baseStart_2091056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091069 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2091069 : Nat := 118140960795 + 2091069 * 2 ^ 59
def prefixEnd_2091069 : Nat := 4983230072969 + 3 ^ 40 * 2091069 * 2
def baseEnd_2091069 : Nat := 715815652477722944413903

theorem tailTrace_2091069 : CollatzResearch.WordTrace tailWord_2091069 prefixEnd_2091069 715815652477722944413903 := by
  unfold tailWord_2091069
  simp only [CollatzResearch.WordTrace]
  refine ⟨76267552061421613998044261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50845034707614409332029507 76267552061421613998044261)
  ·
    refine ⟨14300166011516552624633299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76267552061421613998044261 14300166011516552624633299)
    ·
      refine ⟨21450249017274828936949949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300166011516552624633299 21450249017274828936949949)
      ·
        refine ⟨8043843381478060851356231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21450249017274828936949949 8043843381478060851356231)
        ·
          refine ⟨12065765072217091277034347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043843381478060851356231 12065765072217091277034347)
          ·
            refine ⟨18098647608325636915551521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12065765072217091277034347 18098647608325636915551521)
            ·
              refine ⟨13573985706244227686663641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18098647608325636915551521 13573985706244227686663641)
              ·
                refine ⟨10180489279683170764997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13573985706244227686663641 10180489279683170764997731)
                ·
                  refine ⟨15270733919524756147496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180489279683170764997731 15270733919524756147496597)
                  ·
                    refine ⟨715815652477722944413903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15270733919524756147496597 715815652477722944413903)
                    ·
                      rfl

theorem cell22_2091069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2091069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091069 prefixEnd_2091069 := by exact prefixLift 2091069
  have htrace : WordTrace (prefixWord ++ tailWord_2091069) baseStart_2091069 baseEnd_2091069 := by
    simpa [prefixWord, tailWord_2091069, baseEnd_2091069] using wordTrace_append hprefix tailTrace_2091069
  have hstable : (prefixWord ++ tailWord_2091069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091069).length < 2 ^ (prefixWord ++ tailWord_2091069).sum := by decide
  have hdescent : baseEnd_2091069 < baseStart_2091069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091071 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 2, 3]
def baseStart_2091071 : Nat := 118140960795 + 2091071 * 2 ^ 59
def prefixEnd_2091071 : Nat := 4983230072969 + 3 ^ 40 * 2091071 * 2
def baseEnd_2091071 : Nat := 715816337118595605863897

theorem tailTrace_2091071 : CollatzResearch.WordTrace tailWord_2091071 prefixEnd_2091071 715816337118595605863897 := by
  unfold tailWord_2091071
  simp only [CollatzResearch.WordTrace]
  refine ⟨76267625007414368339617067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50845083338276245559744711 76267625007414368339617067)
  ·
    refine ⟨114401437511121552509425601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76267625007414368339617067 114401437511121552509425601)
    ·
      refine ⟨85801078133341164382069201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114401437511121552509425601 85801078133341164382069201)
      ·
        refine ⟨64350808600005873286551901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85801078133341164382069201 64350808600005873286551901)
        ·
          refine ⟨24131553225002202482456963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64350808600005873286551901 24131553225002202482456963)
          ·
            refine ⟨36197329837503303723685445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24131553225002202482456963 36197329837503303723685445)
            ·
              refine ⟨6786999344531869448191021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36197329837503303723685445 6786999344531869448191021)
              ·
                refine ⟨2545124754199451043071633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6786999344531869448191021 2545124754199451043071633)
                ·
                  refine ⟨1908843565649588282303725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2545124754199451043071633 1908843565649588282303725)
                  ·
                    refine ⟨715816337118595605863897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908843565649588282303725 715816337118595605863897)
                    ·
                      rfl

theorem cell22_2091071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_2091071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091071 prefixEnd_2091071 := by exact prefixLift 2091071
  have htrace : WordTrace (prefixWord ++ tailWord_2091071) baseStart_2091071 baseEnd_2091071 := by
    simpa [prefixWord, tailWord_2091071, baseEnd_2091071] using wordTrace_append hprefix tailTrace_2091071
  have hstable : (prefixWord ++ tailWord_2091071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091071).length < 2 ^ (prefixWord ++ tailWord_2091071).sum := by decide
  have hdescent : baseEnd_2091071 < baseStart_2091071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091086 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2091086 : Nat := 118140960795 + 2091086 * 2 ^ 59
def prefixEnd_2091086 : Nat := 4983230072969 + 3 ^ 40 * 2091086 * 2
def baseEnd_2091086 : Nat := 715821471925140566738851

theorem tailTrace_2091086 : CollatzResearch.WordTrace tailWord_2091086 prefixEnd_2091086 715821471925140566738851 := by
  unfold tailWord_2091086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533521512795003237676639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50845448068240017267608741 9533521512795003237676639)
  ·
    refine ⟨14300282269192504856514959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9533521512795003237676639 14300282269192504856514959)
    ·
      refine ⟨21450423403788757284772439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300282269192504856514959 21450423403788757284772439)
      ·
        refine ⟨32175635105683135927158659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21450423403788757284772439 32175635105683135927158659)
        ·
          refine ⟨48263452658524703890737989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175635105683135927158659 48263452658524703890737989)
          ·
            refine ⟨9049397373473381979513373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48263452658524703890737989 9049397373473381979513373)
            ·
              refine ⟨3393524015052518242317515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9049397373473381979513373 3393524015052518242317515)
              ·
                refine ⟨5090286022578777363476273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393524015052518242317515 5090286022578777363476273)
                ·
                  refine ⟨3817714516934083022607205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090286022578777363476273 3817714516934083022607205)
                  ·
                    refine ⟨715821471925140566738851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3817714516934083022607205 715821471925140566738851)
                    ·
                      rfl

theorem cell22_2091086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2091086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091086 prefixEnd_2091086 := by exact prefixLift 2091086
  have htrace : WordTrace (prefixWord ++ tailWord_2091086) baseStart_2091086 baseEnd_2091086 := by
    simpa [prefixWord, tailWord_2091086, baseEnd_2091086] using wordTrace_append hprefix tailTrace_2091086
  have hstable : (prefixWord ++ tailWord_2091086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091086).length < 2 ^ (prefixWord ++ tailWord_2091086).sum := by decide
  have hdescent : baseEnd_2091086 < baseStart_2091086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091101 : List Nat := [1, 4, 4, 1, 1, 2, 9]
def baseStart_2091101 : Nat := 118140960795 + 2091101 * 2 ^ 59
def prefixEnd_2091101 : Nat := 4983230072969 + 3 ^ 40 * 2091101 * 2
def baseEnd_2091101 : Nat := 26512096545617982504215

theorem tailTrace_2091101 : CollatzResearch.WordTrace tailWord_2091101 prefixEnd_2091101 26512096545617982504215 := by
  unfold tailWord_2091101
  simp only [CollatzResearch.WordTrace]
  refine ⟨76268719197305683463209157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50845812798203788975472771 76268719197305683463209157)
  ·
    refine ⟨14300384849494815649351717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76268719197305683463209157 14300384849494815649351717)
    ·
      refine ⟨2681322159280277934253447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14300384849494815649351717 2681322159280277934253447)
      ·
        refine ⟨4021983238920416901380171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681322159280277934253447 4021983238920416901380171)
        ·
          refine ⟨6032974858380625352070257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021983238920416901380171 6032974858380625352070257)
          ·
            refine ⟨4524731143785469014052693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6032974858380625352070257 4524731143785469014052693)
            ·
              refine ⟨26512096545617982504215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4524731143785469014052693 26512096545617982504215)
              ·
                rfl

theorem cell22_2091101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 9].length) (baseStart_2091101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091101 prefixEnd_2091101 := by exact prefixLift 2091101
  have htrace : WordTrace (prefixWord ++ tailWord_2091101) baseStart_2091101 baseEnd_2091101 := by
    simpa [prefixWord, tailWord_2091101, baseEnd_2091101] using wordTrace_append hprefix tailTrace_2091101
  have hstable : (prefixWord ++ tailWord_2091101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091101).length < 2 ^ (prefixWord ++ tailWord_2091101).sum := by decide
  have hdescent : baseEnd_2091101 < baseStart_2091101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091116 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_2091116 : Nat := 118140960795 + 2091116 * 2 ^ 59
def prefixEnd_2091116 : Nat := 4983230072969 + 3 ^ 40 * 2091116 * 2
def baseEnd_2091116 : Nat := 715831741538230488488759

theorem tailTrace_2091116 : CollatzResearch.WordTrace tailWord_2091116 prefixEnd_2091116 715831741538230488488759 := by
  unfold tailWord_2091116
  simp only [CollatzResearch.WordTrace]
  refine ⟨38134633146125670512502601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50846177528167560683336801 38134633146125670512502601)
  ·
    refine ⟨28600974859594252884376951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38134633146125670512502601 28600974859594252884376951)
    ·
      refine ⟨42901462289391379326565427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28600974859594252884376951 42901462289391379326565427)
      ·
        refine ⟨64352193434087068989848141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42901462289391379326565427 64352193434087068989848141)
        ·
          refine ⟨24132072537782650871193053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64352193434087068989848141 24132072537782650871193053)
          ·
            refine ⟨9049527201668494076697395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24132072537782650871193053 9049527201668494076697395)
            ·
              refine ⟨13574290802502741115046093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049527201668494076697395 13574290802502741115046093)
              ·
                refine ⟨5090359050938527918142285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13574290802502741115046093 5090359050938527918142285)
                ·
                  refine ⟨1908884644101947969303357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5090359050938527918142285 1908884644101947969303357)
                  ·
                    refine ⟨715831741538230488488759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908884644101947969303357 715831741538230488488759)
                    ·
                      rfl

theorem cell22_2091116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_2091116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091116 prefixEnd_2091116 := by exact prefixLift 2091116
  have htrace : WordTrace (prefixWord ++ tailWord_2091116) baseStart_2091116 baseEnd_2091116 := by
    simpa [prefixWord, tailWord_2091116, baseEnd_2091116] using wordTrace_append hprefix tailTrace_2091116
  have hstable : (prefixWord ++ tailWord_2091116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091116).length < 2 ^ (prefixWord ++ tailWord_2091116).sum := by decide
  have hdescent : baseEnd_2091116 < baseStart_2091116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091167 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 1, 3]
def baseStart_2091167 : Nat := 118140960795 + 2091167 * 2 ^ 59
def prefixEnd_2091167 : Nat := 4983230072969 + 3 ^ 40 * 2091167 * 2
def baseEnd_2091167 : Nat := 715849199880483355463603

theorem tailTrace_2091167 : CollatzResearch.WordTrace tailWord_2091167 prefixEnd_2091167 715849199880483355463603 := by
  unfold tailWord_2091167
  simp only [CollatzResearch.WordTrace]
  refine ⟨76271126415066576735111755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50847417610044384490074503 76271126415066576735111755)
  ·
    refine ⟨114406689622599865102667633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76271126415066576735111755 114406689622599865102667633)
    ·
      refine ⟨85805017216949898827000725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114406689622599865102667633 85805017216949898827000725)
      ·
        refine ⟨4022110182044526507515659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85805017216949898827000725 4022110182044526507515659)
        ·
          refine ⟨6033165273066789761273489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022110182044526507515659 6033165273066789761273489)
          ·
            refine ⟨4524873954800092320955117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033165273066789761273489 4524873954800092320955117)
            ·
              refine ⟨1696827733050034620358169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4524873954800092320955117 1696827733050034620358169)
              ·
                refine ⟨1272620799787525965268627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696827733050034620358169 1272620799787525965268627)
                ·
                  refine ⟨1908931199681288947902941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272620799787525965268627 1908931199681288947902941)
                  ·
                    refine ⟨715849199880483355463603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908931199681288947902941 715849199880483355463603)
                    ·
                      rfl

theorem cell22_2091167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_2091167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091167 prefixEnd_2091167 := by exact prefixLift 2091167
  have htrace : WordTrace (prefixWord ++ tailWord_2091167) baseStart_2091167 baseEnd_2091167 := by
    simpa [prefixWord, tailWord_2091167, baseEnd_2091167] using wordTrace_append hprefix tailTrace_2091167
  have hstable : (prefixWord ++ tailWord_2091167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091167).length < 2 ^ (prefixWord ++ tailWord_2091167).sum := by decide
  have hdescent : baseEnd_2091167 < baseStart_2091167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091281 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 7]
def baseStart_2091281 : Nat := 118140960795 + 2091281 * 2 ^ 59
def prefixEnd_2091281 : Nat := 4983230072969 + 3 ^ 40 * 2091281 * 2
def baseEnd_2091281 : Nat := 238629408136741686037751

theorem tailTrace_2091281 : CollatzResearch.WordTrace tailWord_2091281 prefixEnd_2091281 238629408136741686037751 := by
  unfold tailWord_2091281
  simp only [CollatzResearch.WordTrace]
  refine ⟨76275284336653574204761697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50850189557769049469841131 76275284336653574204761697)
  ·
    refine ⟨57206463252490180653571273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76275284336653574204761697 57206463252490180653571273)
    ·
      refine ⟨42904847439367635490178455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57206463252490180653571273 42904847439367635490178455)
      ·
        refine ⟨64357271159051453235267683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42904847439367635490178455 64357271159051453235267683)
        ·
          refine ⟨96535906738577179852901525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64357271159051453235267683 96535906738577179852901525)
          ·
            refine ⟨4525120628370805305604759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96535906738577179852901525 4525120628370805305604759)
            ·
              refine ⟨6787680942556207958407139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525120628370805305604759 6787680942556207958407139)
              ·
                refine ⟨10181521413834311937610709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787680942556207958407139 10181521413834311937610709)
                ·
                  refine ⟨238629408136741686037751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10181521413834311937610709 238629408136741686037751)
                  ·
                    rfl

theorem cell22_2091281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_2091281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091281 prefixEnd_2091281 := by exact prefixLift 2091281
  have htrace : WordTrace (prefixWord ++ tailWord_2091281) baseStart_2091281 baseEnd_2091281 := by
    simpa [prefixWord, tailWord_2091281, baseEnd_2091281] using wordTrace_append hprefix tailTrace_2091281
  have hstable : (prefixWord ++ tailWord_2091281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091281).length < 2 ^ (prefixWord ++ tailWord_2091281).sum := by decide
  have hdescent : baseEnd_2091281 < baseStart_2091281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091285 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_2091285 : Nat := 118140960795 + 2091285 * 2 ^ 59
def prefixEnd_2091285 : Nat := 4983230072969 + 3 ^ 40 * 2091285 * 2
def baseEnd_2091285 : Nat := 715889593691970381013241

theorem tailTrace_2091285 : CollatzResearch.WordTrace tailWord_2091285 prefixEnd_2091285 715889593691970381013241 := by
  unfold tailWord_2091285
  simp only [CollatzResearch.WordTrace]
  refine ⟨76275430228639082887907309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50850286819092721925271539 76275430228639082887907309)
  ·
    refine ⟨28603286335739656082965241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76275430228639082887907309 28603286335739656082965241)
    ·
      refine ⟨21452464751804742062223931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28603286335739656082965241 21452464751804742062223931)
      ·
        refine ⟨32178697127707113093335897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21452464751804742062223931 32178697127707113093335897)
        ·
          refine ⟨24134022845780334820001923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32178697127707113093335897 24134022845780334820001923)
          ·
            refine ⟨36201034268670502230002885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24134022845780334820001923 36201034268670502230002885)
            ·
              refine ⟨6787693925375719168125541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36201034268670502230002885 6787693925375719168125541)
              ·
                refine ⟨1272692611007947344023539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6787693925375719168125541 1272692611007947344023539)
                ·
                  refine ⟨1909038916511921016035309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272692611007947344023539 1909038916511921016035309)
                  ·
                    refine ⟨715889593691970381013241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909038916511921016035309 715889593691970381013241)
                    ·
                      rfl

theorem cell22_2091285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_2091285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091285 prefixEnd_2091285 := by exact prefixLift 2091285
  have htrace : WordTrace (prefixWord ++ tailWord_2091285) baseStart_2091285 baseEnd_2091285 := by
    simpa [prefixWord, tailWord_2091285, baseEnd_2091285] using wordTrace_append hprefix tailTrace_2091285
  have hstable : (prefixWord ++ tailWord_2091285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091285).length < 2 ^ (prefixWord ++ tailWord_2091285).sum := by decide
  have hdescent : baseEnd_2091285 < baseStart_2091285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091311 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 3, 4]
def baseStart_2091311 : Nat := 118140960795 + 2091311 * 2 ^ 59
def prefixEnd_2091311 : Nat := 4983230072969 + 3 ^ 40 * 2091311 * 2
def baseEnd_2091311 : Nat := 715898494023314979863161

theorem tailTrace_2091311 : CollatzResearch.WordTrace tailWord_2091311 prefixEnd_2091311 715898494023314979863161 := by
  unfold tailWord_2091311
  simp only [CollatzResearch.WordTrace]
  refine ⟨76276378526544889328353787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50850919017696592885569191 76276378526544889328353787)
  ·
    refine ⟨114414567789817333992530681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76276378526544889328353787 114414567789817333992530681)
    ·
      refine ⟨85810925842363000494398011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114414567789817333992530681 85810925842363000494398011)
      ·
        refine ⟨128716388763544500741597017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85810925842363000494398011 128716388763544500741597017)
        ·
          refine ⟨96537291572658375556197763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128716388763544500741597017 96537291572658375556197763)
          ·
            refine ⟨144805937358987563334296645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96537291572658375556197763 144805937358987563334296645)
            ·
              refine ⟨27151113254810168125180621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144805937358987563334296645 27151113254810168125180621)
              ·
                refine ⟨10181667470553813046942733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27151113254810168125180621 10181667470553813046942733)
                ·
                  refine ⟨3818125301457679892603525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10181667470553813046942733 3818125301457679892603525)
                  ·
                    refine ⟨715898494023314979863161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818125301457679892603525 715898494023314979863161)
                    ·
                      rfl

theorem cell22_2091311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_2091311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091311 prefixEnd_2091311 := by exact prefixLift 2091311
  have htrace : WordTrace (prefixWord ++ tailWord_2091311) baseStart_2091311 baseEnd_2091311 := by
    simpa [prefixWord, tailWord_2091311, baseEnd_2091311] using wordTrace_append hprefix tailTrace_2091311
  have hstable : (prefixWord ++ tailWord_2091311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091311).length < 2 ^ (prefixWord ++ tailWord_2091311).sum := by decide
  have hdescent : baseEnd_2091311 < baseStart_2091311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091362 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2091362 : Nat := 118140960795 + 2091362 * 2 ^ 59
def prefixEnd_2091362 : Nat := 4983230072969 + 3 ^ 40 * 2091362 * 2
def baseEnd_2091362 : Nat := 715915952365567846838005

theorem tailTrace_2091362 : CollatzResearch.WordTrace tailWord_2091362 prefixEnd_2091362 715915952365567846838005 := by
  unfold tailWord_2091362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069559662340031259615085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50852159099573416692306893 19069559662340031259615085)
  ·
    refine ⟨7151084873377511722355657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19069559662340031259615085 7151084873377511722355657)
    ·
      refine ⟨5363313655033133791766743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7151084873377511722355657 5363313655033133791766743)
      ·
        refine ⟨8044970482549700687650115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363313655033133791766743 8044970482549700687650115)
        ·
          refine ⟨12067455723824551031475173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044970482549700687650115 12067455723824551031475173)
          ·
            refine ⟨2262647948217103318401595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12067455723824551031475173 2262647948217103318401595)
            ·
              refine ⟨3393971922325654977602393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262647948217103318401595 3393971922325654977602393)
              ·
                refine ⟨2545478941744241233201795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3393971922325654977602393 2545478941744241233201795)
                ·
                  refine ⟨3818218412616361849802693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545478941744241233201795 3818218412616361849802693)
                  ·
                    refine ⟨715915952365567846838005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818218412616361849802693 715915952365567846838005)
                    ·
                      rfl

theorem cell22_2091362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2091362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091362 prefixEnd_2091362 := by exact prefixLift 2091362
  have htrace : WordTrace (prefixWord ++ tailWord_2091362) baseStart_2091362 baseEnd_2091362 := by
    simpa [prefixWord, tailWord_2091362, baseEnd_2091362] using wordTrace_append hprefix tailTrace_2091362
  have hstable : (prefixWord ++ tailWord_2091362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091362).length < 2 ^ (prefixWord ++ tailWord_2091362).sum := by decide
  have hdescent : baseEnd_2091362 < baseStart_2091362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091394 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2091394 : Nat := 118140960795 + 2091394 * 2 ^ 59
def prefixEnd_2091394 : Nat := 4983230072969 + 3 ^ 40 * 2091394 * 2
def baseEnd_2091394 : Nat := 238642302206510143345969

theorem tailTrace_2091394 : CollatzResearch.WordTrace tailWord_2091394 prefixEnd_2091394 238642302206510143345969 := by
  unfold tailWord_2091394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069851446311048625906309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50852937190162796335750157 19069851446311048625906309)
  ·
    refine ⟨3575597146183321617357433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19069851446311048625906309 3575597146183321617357433)
    ·
      refine ⟨2681697859637491213018075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3575597146183321617357433 2681697859637491213018075)
      ·
        refine ⟨4022546789456236819527113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681697859637491213018075 4022546789456236819527113)
        ·
          refine ⟨3016910092092177614645335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4022546789456236819527113 3016910092092177614645335)
          ·
            refine ⟨4525365138138266421968003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016910092092177614645335 4525365138138266421968003)
            ·
              refine ⟨6788047707207399632952005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525365138138266421968003 6788047707207399632952005)
              ·
                refine ⟨1272758945101387431178501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6788047707207399632952005 1272758945101387431178501)
                ·
                  refine ⟨238642302206510143345969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272758945101387431178501 238642302206510143345969)
                  ·
                    rfl

theorem cell22_2091394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2091394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091394 prefixEnd_2091394 := by exact prefixLift 2091394
  have htrace : WordTrace (prefixWord ++ tailWord_2091394) baseStart_2091394 baseEnd_2091394 := by
    simpa [prefixWord, tailWord_2091394, baseEnd_2091394] using wordTrace_append hprefix tailTrace_2091394
  have hstable : (prefixWord ++ tailWord_2091394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091394).length < 2 ^ (prefixWord ++ tailWord_2091394).sum := by decide
  have hdescent : baseEnd_2091394 < baseStart_2091394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091422 : List Nat := [4, 3, 1, 2, 1, 2, 3, 6]
def baseStart_2091422 : Nat := 118140960795 + 2091422 * 2 ^ 59
def prefixEnd_2091422 : Nat := 4983230072969 + 3 ^ 40 * 2091422 * 2
def baseEnd_2091422 : Nat := 79548499065749743370869

theorem tailTrace_2091422 : CollatzResearch.WordTrace tailWord_2091422 prefixEnd_2091422 79548499065749743370869 := by
  unfold tailWord_2091422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535053378642844410705565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50853618019428503523763013 9535053378642844410705565)
  ·
    refine ⟨3575645016991066654014587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9535053378642844410705565 3575645016991066654014587)
    ·
      refine ⟨5363467525486599981021881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575645016991066654014587 5363467525486599981021881)
      ·
        refine ⟨4022600644114949985766411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5363467525486599981021881 4022600644114949985766411)
        ·
          refine ⟨6033900966172424978649617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022600644114949985766411 6033900966172424978649617)
          ·
            refine ⟨4525425724629318733987213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033900966172424978649617 4525425724629318733987213)
            ·
              refine ⟨1697034646735994525245205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4525425724629318733987213 1697034646735994525245205)
              ·
                refine ⟨79548499065749743370869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1697034646735994525245205 79548499065749743370869)
                ·
                  rfl

theorem cell22_2091422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_2091422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091422 prefixEnd_2091422 := by exact prefixLift 2091422
  have htrace : WordTrace (prefixWord ++ tailWord_2091422) baseStart_2091422 baseEnd_2091422 := by
    simpa [prefixWord, tailWord_2091422, baseEnd_2091422] using wordTrace_append hprefix tailTrace_2091422
  have hstable : (prefixWord ++ tailWord_2091422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091422).length < 2 ^ (prefixWord ++ tailWord_2091422).sum := by decide
  have hdescent : baseEnd_2091422 < baseStart_2091422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091512 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 4]
def baseStart_2091512 : Nat := 118140960795 + 2091512 * 2 ^ 59
def prefixEnd_2091512 : Nat := 4983230072969 + 3 ^ 40 * 2091512 * 2
def baseEnd_2091512 : Nat := 238655766810339151862515

theorem tailTrace_2091512 : CollatzResearch.WordTrace tailWord_2091512 prefixEnd_2091512 238655766810339151862515 := by
  unfold tailWord_2091512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38141854799408350328210395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50855806399211133770947193 38141854799408350328210395)
  ·
    refine ⟨57212782199112525492315593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38141854799408350328210395 57212782199112525492315593)
    ·
      refine ⟨42909586649334394119236695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57212782199112525492315593 42909586649334394119236695)
      ·
        refine ⟨64364379974001591178855043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42909586649334394119236695 64364379974001591178855043)
        ·
          refine ⟨96546569961002386768282565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64364379974001591178855043 96546569961002386768282565)
          ·
            refine ⟨18102481867687947519052981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96546569961002386768282565 18102481867687947519052981)
            ·
              refine ⟨1697107675095745079911217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18102481867687947519052981 1697107675095745079911217)
              ·
                refine ⟨1272830756321808809933413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697107675095745079911217 1272830756321808809933413)
                ·
                  refine ⟨238655766810339151862515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272830756321808809933413 238655766810339151862515)
                  ·
                    rfl

theorem cell22_2091512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_2091512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091512 prefixEnd_2091512 := by exact prefixLift 2091512
  have htrace : WordTrace (prefixWord ++ tailWord_2091512) baseStart_2091512 baseEnd_2091512 := by
    simpa [prefixWord, tailWord_2091512, baseEnd_2091512] using wordTrace_append hprefix tailTrace_2091512
  have hstable : (prefixWord ++ tailWord_2091512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091512).length < 2 ^ (prefixWord ++ tailWord_2091512).sum := by decide
  have hdescent : baseEnd_2091512 < baseStart_2091512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091523 : List Nat := [1, 1, 1, 3, 2, 1, 6, 7]
def baseStart_2091523 : Nat := 118140960795 + 2091523 * 2 ^ 59
def prefixEnd_2091523 : Nat := 4983230072969 + 3 ^ 40 * 2091523 * 2
def baseEnd_2091523 : Nat := 79552340661757454840279

theorem tailTrace_2091523 : CollatzResearch.WordTrace tailWord_2091523 prefixEnd_2091523 79552340661757454840279 := by
  unfold tailWord_2091523
  simp only [CollatzResearch.WordTrace]
  refine ⟨76284110801776849535071223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50856073867851233023380815 76284110801776849535071223)
  ·
    refine ⟨114426166202665274302606835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76284110801776849535071223 114426166202665274302606835)
    ·
      refine ⟨171639249303997911453910253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114426166202665274302606835 171639249303997911453910253)
      ·
        refine ⟨64364718488999216795216345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171639249303997911453910253 64364718488999216795216345)
        ·
          refine ⟨48273538866749412596412259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64364718488999216795216345 48273538866749412596412259)
          ·
            refine ⟨72410308300124118894618389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48273538866749412596412259 72410308300124118894618389)
            ·
              refine ⟨3394233201568318073185237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72410308300124118894618389 3394233201568318073185237)
              ·
                refine ⟨79552340661757454840279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3394233201568318073185237 79552340661757454840279)
                ·
                  rfl

theorem cell22_2091523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 7].length) (baseStart_2091523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091523 prefixEnd_2091523 := by exact prefixLift 2091523
  have htrace : WordTrace (prefixWord ++ tailWord_2091523) baseStart_2091523 baseEnd_2091523 := by
    simpa [prefixWord, tailWord_2091523, baseEnd_2091523] using wordTrace_append hprefix tailTrace_2091523
  have hstable : (prefixWord ++ tailWord_2091523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091523).length < 2 ^ (prefixWord ++ tailWord_2091523).sum := by decide
  have hdescent : baseEnd_2091523 < baseStart_2091523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091568 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_2091568 : Nat := 118140960795 + 2091568 * 2 ^ 59
def prefixEnd_2091568 : Nat := 4983230072969 + 3 ^ 40 * 2091568 * 2
def baseEnd_2091568 : Nat := 238662156791817325395791

theorem tailTrace_2091568 : CollatzResearch.WordTrace tailWord_2091568 prefixEnd_2091568 238662156791817325395791 := by
  unfold tailWord_2091568
  simp only [CollatzResearch.WordTrace]
  refine ⟨38142876043306911110229679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50857168057742548146972905 38142876043306911110229679)
  ·
    refine ⟨57214314064960366665344519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38142876043306911110229679 57214314064960366665344519)
    ·
      refine ⟨85821471097440549998016779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57214314064960366665344519 85821471097440549998016779)
      ·
        refine ⟨128732206646160824997025169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85821471097440549998016779 128732206646160824997025169)
        ·
          refine ⟨96549154984620618747768877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128732206646160824997025169 96549154984620618747768877)
          ·
            refine ⟨36205933119232732030413329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96549154984620618747768877 36205933119232732030413329)
            ·
              refine ⟨27154449839424549022809997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36205933119232732030413329 27154449839424549022809997)
              ·
                refine ⟨10182918689784205883553749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27154449839424549022809997 10182918689784205883553749)
                ·
                  refine ⟨238662156791817325395791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10182918689784205883553749 238662156791817325395791)
                  ·
                    rfl

theorem cell22_2091568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_2091568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091568 prefixEnd_2091568 := by exact prefixLift 2091568
  have htrace : WordTrace (prefixWord ++ tailWord_2091568) baseStart_2091568 baseEnd_2091568 := by
    simpa [prefixWord, tailWord_2091568, baseEnd_2091568] using wordTrace_append hprefix tailTrace_2091568
  have hstable : (prefixWord ++ tailWord_2091568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091568).length < 2 ^ (prefixWord ++ tailWord_2091568).sum := by decide
  have hdescent : baseEnd_2091568 < baseStart_2091568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091662 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_2091662 : Nat := 118140960795 + 2091662 * 2 ^ 59
def prefixEnd_2091662 : Nat := 4983230072969 + 3 ^ 40 * 2091662 * 2
def baseEnd_2091662 : Nat := 716018648496467064337085

theorem tailTrace_2091662 : CollatzResearch.WordTrace tailWord_2091662 prefixEnd_2091662 716018648496467064337085 := by
  unfold tailWord_2091662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536147568534159534297655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50859453698848850849587493 9536147568534159534297655)
  ·
    refine ⟨14304221352801239301446483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9536147568534159534297655 14304221352801239301446483)
    ·
      refine ⟨21456332029201858952169725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14304221352801239301446483 21456332029201858952169725)
      ·
        refine ⟨8046124510950697107063647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21456332029201858952169725 8046124510950697107063647)
        ·
          refine ⟨12069186766426045660595471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046124510950697107063647 12069186766426045660595471)
          ·
            refine ⟨18103780149639068490893207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12069186766426045660595471 18103780149639068490893207)
            ·
              refine ⟨27155670224458602736339811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103780149639068490893207 27155670224458602736339811)
              ·
                refine ⟨40733505336687904104509717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27155670224458602736339811 40733505336687904104509717)
                ·
                  refine ⟨1909383062657245504898893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40733505336687904104509717 1909383062657245504898893)
                  ·
                    refine ⟨716018648496467064337085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909383062657245504898893 716018648496467064337085)
                    ·
                      rfl

theorem cell22_2091662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_2091662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091662 prefixEnd_2091662 := by exact prefixLift 2091662
  have htrace : WordTrace (prefixWord ++ tailWord_2091662) baseStart_2091662 baseEnd_2091662 := by
    simpa [prefixWord, tailWord_2091662, baseEnd_2091662] using wordTrace_append hprefix tailTrace_2091662
  have hstable : (prefixWord ++ tailWord_2091662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091662).length < 2 ^ (prefixWord ++ tailWord_2091662).sum := by decide
  have hdescent : baseEnd_2091662 < baseStart_2091662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091681 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 4]
def baseStart_2091681 : Nat := 118140960795 + 2091681 * 2 ^ 59
def prefixEnd_2091681 : Nat := 4983230072969 + 3 ^ 40 * 2091681 * 2
def baseEnd_2091681 : Nat := 238675050861585782704009

theorem tailTrace_2091681 : CollatzResearch.WordTrace tailWord_2091681 prefixEnd_2091681 238675050861585782704009 := by
  unfold tailWord_2091681
  simp only [CollatzResearch.WordTrace]
  refine ⟨76289873535204442519322897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50859915690136295012881931 76289873535204442519322897)
  ·
    refine ⟨57217405151403331889492173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76289873535204442519322897 57217405151403331889492173)
    ·
      refine ⟨21456526931776249458559565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57217405151403331889492173 21456526931776249458559565)
      ·
        refine ⟨8046197599416093546959837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21456526931776249458559565 8046197599416093546959837)
        ·
          refine ⟨3017324099781035080109939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8046197599416093546959837 3017324099781035080109939)
          ·
            refine ⟨4525986149671552620164909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017324099781035080109939 4525986149671552620164909)
            ·
              refine ⟨1697244806126832232561841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4525986149671552620164909 1697244806126832232561841)
              ·
                refine ⟨1272933604595124174421381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697244806126832232561841 1272933604595124174421381)
                ·
                  refine ⟨238675050861585782704009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272933604595124174421381 238675050861585782704009)
                  ·
                    rfl

theorem cell22_2091681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_2091681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091681 prefixEnd_2091681 := by exact prefixLift 2091681
  have htrace : WordTrace (prefixWord ++ tailWord_2091681) baseStart_2091681 baseEnd_2091681 := by
    simpa [prefixWord, tailWord_2091681, baseEnd_2091681] using wordTrace_append hprefix tailTrace_2091681
  have hstable : (prefixWord ++ tailWord_2091681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091681).length < 2 ^ (prefixWord ++ tailWord_2091681).sum := by decide
  have hdescent : baseEnd_2091681 < baseStart_2091681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091737 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 5]
def baseStart_2091737 : Nat := 118140960795 + 2091737 * 2 ^ 59
def prefixEnd_2091737 : Nat := 4983230072969 + 3 ^ 40 * 2091737 * 2
def baseEnd_2091737 : Nat := 238681440843063956237285

theorem tailTrace_2091737 : CollatzResearch.WordTrace tailWord_2091737 prefixEnd_2091737 238681440843063956237285 := by
  unfold tailWord_2091737
  simp only [CollatzResearch.WordTrace]
  refine ⟨76291916023001564083361465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50861277348667709388907643 76291916023001564083361465)
  ·
    refine ⟨57218937017251173062521099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76291916023001564083361465 57218937017251173062521099)
    ·
      refine ⟨85828405525876759593781649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57218937017251173062521099 85828405525876759593781649)
      ·
        refine ⟨64371304144407569695336237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85828405525876759593781649 64371304144407569695336237)
        ·
          refine ⟨24139239054152838635751089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64371304144407569695336237 24139239054152838635751089)
          ·
            refine ⟨18104429290614628976813317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24139239054152838635751089 18104429290614628976813317)
            ·
              refine ⟨3394580491990242933152497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18104429290614628976813317 3394580491990242933152497)
              ·
                refine ⟨2545935368992682199864373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394580491990242933152497 2545935368992682199864373)
                ·
                  refine ⟨238681440843063956237285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2545935368992682199864373 238681440843063956237285)
                  ·
                    rfl

theorem cell22_2091737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_2091737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091737 prefixEnd_2091737 := by exact prefixLift 2091737
  have htrace : WordTrace (prefixWord ++ tailWord_2091737) baseStart_2091737 baseEnd_2091737 := by
    simpa [prefixWord, tailWord_2091737, baseEnd_2091737] using wordTrace_append hprefix tailTrace_2091737
  have hstable : (prefixWord ++ tailWord_2091737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091737).length < 2 ^ (prefixWord ++ tailWord_2091737).sum := by decide
  have hdescent : baseEnd_2091737 < baseStart_2091737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091767 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 1, 4]
def baseStart_2091767 : Nat := 118140960795 + 2091767 * 2 ^ 59
def prefixEnd_2091767 : Nat := 4983230072969 + 3 ^ 40 * 2091767 * 2
def baseEnd_2091767 : Nat := 716054592142281790461763

theorem tailTrace_2091767 : CollatzResearch.WordTrace tailWord_2091767 prefixEnd_2091767 716054592142281790461763 := by
  unfold tailWord_2091767
  simp only [CollatzResearch.WordTrace]
  refine ⟨76293010212892879206953555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50862006808595252804635703 76293010212892879206953555)
  ·
    refine ⟨114439515319339318810430333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76293010212892879206953555 114439515319339318810430333)
    ·
      refine ⟨42914818244752244553911375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114439515319339318810430333 42914818244752244553911375)
      ·
        refine ⟨64372227367128366830867063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42914818244752244553911375 64372227367128366830867063)
        ·
          refine ⟨96558341050692550246300595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64372227367128366830867063 96558341050692550246300595)
          ·
            refine ⟨144837511576038825369450893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96558341050692550246300595 144837511576038825369450893)
            ·
              refine ⟨54314066841014559513544085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144837511576038825369450893 54314066841014559513544085)
              ·
                refine ⟨2545971883172557477197379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54314066841014559513544085 2545971883172557477197379)
                ·
                  refine ⟨3818957824758836215796069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545971883172557477197379 3818957824758836215796069)
                  ·
                    refine ⟨716054592142281790461763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818957824758836215796069 716054592142281790461763)
                    ·
                      rfl

theorem cell22_2091767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_2091767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091767 prefixEnd_2091767 := by exact prefixLift 2091767
  have htrace : WordTrace (prefixWord ++ tailWord_2091767) baseStart_2091767 baseEnd_2091767 := by
    simpa [prefixWord, tailWord_2091767, baseEnd_2091767] using wordTrace_append hprefix tailTrace_2091767
  have hstable : (prefixWord ++ tailWord_2091767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091767).length < 2 ^ (prefixWord ++ tailWord_2091767).sum := by decide
  have hdescent : baseEnd_2091767 < baseStart_2091767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091784 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_2091784 : Nat := 118140960795 + 2091784 * 2 ^ 59
def prefixEnd_2091784 : Nat := 4983230072969 + 3 ^ 40 * 2091784 * 2
def baseEnd_2091784 : Nat := 716060411589699412786711

theorem tailTrace_2091784 : CollatzResearch.WordTrace tailWord_2091784 prefixEnd_2091784 716060411589699412786711 := by
  unfold tailWord_2091784
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146815126915645555161203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50862420169220860740214937 38146815126915645555161203)
  ·
    refine ⟨57220222690373468332741805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38146815126915645555161203 57220222690373468332741805)
    ·
      refine ⟨21457583508890050624778177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57220222690373468332741805 21457583508890050624778177)
      ·
        refine ⟨16093187631667537968583633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21457583508890050624778177 16093187631667537968583633)
        ·
          refine ⟨12069890723750653476437725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16093187631667537968583633 12069890723750653476437725)
          ·
            refine ⟨4526209021406495053664147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12069890723750653476437725 4526209021406495053664147)
            ·
              refine ⟨6789313532109742580496221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526209021406495053664147 6789313532109742580496221)
              ·
                refine ⟨2545992574541153467686083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6789313532109742580496221 2545992574541153467686083)
                ·
                  refine ⟨3818988861811730201529125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545992574541153467686083 3818988861811730201529125)
                  ·
                    refine ⟨716060411589699412786711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818988861811730201529125 716060411589699412786711)
                    ·
                      rfl

theorem cell22_2091784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_2091784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091784 prefixEnd_2091784 := by exact prefixLift 2091784
  have htrace : WordTrace (prefixWord ++ tailWord_2091784) baseStart_2091784 baseEnd_2091784 := by
    simpa [prefixWord, tailWord_2091784, baseEnd_2091784] using wordTrace_append hprefix tailTrace_2091784
  have hstable : (prefixWord ++ tailWord_2091784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091784).length < 2 ^ (prefixWord ++ tailWord_2091784).sum := by decide
  have hdescent : baseEnd_2091784 < baseStart_2091784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091799 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 6]
def baseStart_2091799 : Nat := 118140960795 + 2091799 * 2 ^ 59
def prefixEnd_2091799 : Nat := 4983230072969 + 3 ^ 40 * 2091799 * 2
def baseEnd_2091799 : Nat := 238688515465414791220555

theorem tailTrace_2091799 : CollatzResearch.WordTrace tailWord_2091799 prefixEnd_2091799 238688515465414791220555 := by
  unfold tailWord_2091799
  simp only [CollatzResearch.WordTrace]
  refine ⟨76294177348776948672118451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50862784899184632448078967 76294177348776948672118451)
  ·
    refine ⟨114441266023165423008177677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76294177348776948672118451 114441266023165423008177677)
    ·
      refine ⟨42915474758687033628066629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114441266023165423008177677 42915474758687033628066629)
      ·
        refine ⟨8046651517253818805262493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42915474758687033628066629 8046651517253818805262493)
        ·
          refine ⟨3017494318970182051973435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8046651517253818805262493 3017494318970182051973435)
          ·
            refine ⟨4526241478455273077960153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017494318970182051973435 4526241478455273077960153)
            ·
              refine ⟨3394681108841454808470115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526241478455273077960153 3394681108841454808470115)
              ·
                refine ⟨5092021663262182212705173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394681108841454808470115 5092021663262182212705173)
                ·
                  refine ⟨238688515465414791220555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5092021663262182212705173 238688515465414791220555)
                  ·
                    rfl

theorem cell22_2091799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 6].length) (baseStart_2091799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091799 prefixEnd_2091799 := by exact prefixLift 2091799
  have htrace : WordTrace (prefixWord ++ tailWord_2091799) baseStart_2091799 baseEnd_2091799 := by
    simpa [prefixWord, tailWord_2091799, baseEnd_2091799] using wordTrace_append hprefix tailTrace_2091799
  have hstable : (prefixWord ++ tailWord_2091799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091799).length < 2 ^ (prefixWord ++ tailWord_2091799).sum := by decide
  have hdescent : baseEnd_2091799 < baseStart_2091799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091818 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2091818 : Nat := 118140960795 + 2091818 * 2 ^ 59
def prefixEnd_2091818 : Nat := 4983230072969 + 3 ^ 40 * 2091818 * 2
def baseEnd_2091818 : Nat := 716072050484534657436607

theorem tailTrace_2091818 : CollatzResearch.WordTrace tailWord_2091818 prefixEnd_2091818 716072050484534657436607 := by
  unfold tailWord_2091818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073717583927028729265027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50863246890472076611373405 19073717583927028729265027)
  ·
    refine ⟨28610576375890543093897541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073717583927028729265027 28610576375890543093897541)
    ·
      refine ⟨5364483070479476830105789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28610576375890543093897541 5364483070479476830105789)
      ·
        refine ⟨2011681151429803811289671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5364483070479476830105789 2011681151429803811289671)
        ·
          refine ⟨3017521727144705716934507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011681151429803811289671 3017521727144705716934507)
          ·
            refine ⟨4526282590717058575401761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017521727144705716934507 4526282590717058575401761)
            ·
              refine ⟨3394711943037793931551321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526282590717058575401761 3394711943037793931551321)
              ·
                refine ⟨2546033957278345448663491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394711943037793931551321 2546033957278345448663491)
                ·
                  refine ⟨3819050935917518172995237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546033957278345448663491 3819050935917518172995237)
                  ·
                    refine ⟨716072050484534657436607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3819050935917518172995237 716072050484534657436607)
                    ·
                      rfl

theorem cell22_2091818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2091818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091818 prefixEnd_2091818 := by exact prefixLift 2091818
  have htrace : WordTrace (prefixWord ++ tailWord_2091818) baseStart_2091818 baseEnd_2091818 := by
    simpa [prefixWord, tailWord_2091818, baseEnd_2091818] using wordTrace_append hprefix tailTrace_2091818
  have hstable : (prefixWord ++ tailWord_2091818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091818).length < 2 ^ (prefixWord ++ tailWord_2091818).sum := by decide
  have hdescent : baseEnd_2091818 < baseStart_2091818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091827 : List Nat := [1, 1, 1, 2, 6, 2, 1, 8]
def baseStart_2091827 : Nat := 118140960795 + 2091827 * 2 ^ 59
def prefixEnd_2091827 : Nat := 4983230072969 + 3 ^ 40 * 2091827 * 2
def baseEnd_2091827 : Nat := 79563903485384625995731

theorem tailTrace_2091827 : CollatzResearch.WordTrace tailWord_2091827 prefixEnd_2091827 79563903485384625995731 := by
  unfold tailWord_2091827
  simp only [CollatzResearch.WordTrace]
  refine ⟨76295198592675509454137735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50863465728450339636091823 76295198592675509454137735)
  ·
    refine ⟨114442797889013264181206603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76295198592675509454137735 114442797889013264181206603)
    ·
      refine ⟨171664196833519896271809905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114442797889013264181206603 171664196833519896271809905)
      ·
        refine ⟨128748147625139922203857429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171664196833519896271809905 128748147625139922203857429)
        ·
          refine ⟨6035069419928433853305817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128748147625139922203857429 6035069419928433853305817)
          ·
            refine ⟨4526302064946325389979363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035069419928433853305817 4526302064946325389979363)
            ·
              refine ⟨6789453097419488084969045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526302064946325389979363 6789453097419488084969045)
              ·
                refine ⟨79563903485384625995731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6789453097419488084969045 79563903485384625995731)
                ·
                  rfl

theorem cell22_2091827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 8].length) (baseStart_2091827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091827 prefixEnd_2091827 := by exact prefixLift 2091827
  have htrace : WordTrace (prefixWord ++ tailWord_2091827) baseStart_2091827 baseEnd_2091827 := by
    simpa [prefixWord, tailWord_2091827, baseEnd_2091827] using wordTrace_append hprefix tailTrace_2091827
  have hstable : (prefixWord ++ tailWord_2091827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091827).length < 2 ^ (prefixWord ++ tailWord_2091827).sum := by decide
  have hdescent : baseEnd_2091827 < baseStart_2091827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091947 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_2091947 : Nat := 118140960795 + 2091947 * 2 ^ 59
def prefixEnd_2091947 : Nat := 4983230072969 + 3 ^ 40 * 2091947 * 2
def baseEnd_2091947 : Nat := 716116209820821320961211

theorem tailTrace_2091947 : CollatzResearch.WordTrace tailWord_2091947 prefixEnd_2091947 716116209820821320961211 := by
  unfold tailWord_2091947
  simp only [CollatzResearch.WordTrace]
  refine ⟨76299575352240769948506095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50866383568160513299004063 76299575352240769948506095)
  ·
    refine ⟨114449363028361154922759143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76299575352240769948506095 114449363028361154922759143)
    ·
      refine ⟨171674044542541732384138715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114449363028361154922759143 171674044542541732384138715)
      ·
        refine ⟨257511066813812598576208073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171674044542541732384138715 257511066813812598576208073)
        ·
          refine ⟨193133300110359448932156055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257511066813812598576208073 193133300110359448932156055)
          ·
            refine ⟨289699950165539173398234083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193133300110359448932156055 289699950165539173398234083)
            ·
              refine ⟨434549925248308760097351125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289699950165539173398234083 434549925248308760097351125)
              ·
                refine ⟨10184763873007236564781667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 434549925248308760097351125 10184763873007236564781667)
                ·
                  refine ⟨15277145809510854847172501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10184763873007236564781667 15277145809510854847172501)
                  ·
                    refine ⟨716116209820821320961211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15277145809510854847172501 716116209820821320961211)
                    ·
                      rfl

theorem cell22_2091947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_2091947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091947 prefixEnd_2091947 := by exact prefixLift 2091947
  have htrace : WordTrace (prefixWord ++ tailWord_2091947) baseStart_2091947 baseEnd_2091947 := by
    simpa [prefixWord, tailWord_2091947, baseEnd_2091947] using wordTrace_append hprefix tailTrace_2091947
  have hstable : (prefixWord ++ tailWord_2091947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091947).length < 2 ^ (prefixWord ++ tailWord_2091947).sum := by decide
  have hdescent : baseEnd_2091947 < baseStart_2091947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091962 : List Nat := [3, 1, 1, 1, 2, 1, 13]
def baseStart_2091962 : Nat := 118140960795 + 2091962 * 2 ^ 59
def prefixEnd_2091962 : Nat := 4983230072969 + 3 ^ 40 * 2091962 * 2
def baseEnd_2091962 : Nat := 26523012763976528956895

theorem tailTrace_2091962 : CollatzResearch.WordTrace tailWord_2091962 prefixEnd_2091962 26523012763976528956895 := by
  unfold tailWord_2091962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075030611796606877575535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50866748298124285006868093 19075030611796606877575535)
  ·
    refine ⟨28612545917694910316363303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19075030611796606877575535 28612545917694910316363303)
    ·
      refine ⟨42918818876542365474544955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28612545917694910316363303 42918818876542365474544955)
      ·
        refine ⟨64378228314813548211817433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42918818876542365474544955 64378228314813548211817433)
        ·
          refine ⟨48283671236110161158863075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64378228314813548211817433 48283671236110161158863075)
          ·
            refine ⟨72425506854165241738294613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48283671236110161158863075 72425506854165241738294613)
            ·
              refine ⟨26523012763976528956895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 72425506854165241738294613 26523012763976528956895)
              ·
                rfl

theorem cell22_2091962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 13].length) (baseStart_2091962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091962 prefixEnd_2091962 := by exact prefixLift 2091962
  have htrace : WordTrace (prefixWord ++ tailWord_2091962) baseStart_2091962 baseEnd_2091962 := by
    simpa [prefixWord, tailWord_2091962, baseEnd_2091962] using wordTrace_append hprefix tailTrace_2091962
  have hstable : (prefixWord ++ tailWord_2091962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091962).length < 2 ^ (prefixWord ++ tailWord_2091962).sum := by decide
  have hdescent : baseEnd_2091962 < baseStart_2091962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091966 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_2091966 : Nat := 118140960795 + 2091966 * 2 ^ 59
def prefixEnd_2091966 : Nat := 4983230072969 + 3 ^ 40 * 2091966 * 2
def baseEnd_2091966 : Nat := 716122713909111604736153

theorem tailTrace_2091966 : CollatzResearch.WordTrace tailWord_2091966 prefixEnd_2091966 716122713909111604736153 := by
  unfold tailWord_2091966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537533542396492024180969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50866845559447957462298501 9537533542396492024180969)
  ·
    refine ⟨7153150156797369018135727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9537533542396492024180969 7153150156797369018135727)
    ·
      refine ⟨10729725235196053527203591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153150156797369018135727 10729725235196053527203591)
      ·
        refine ⟨16094587852794080290805387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729725235196053527203591 16094587852794080290805387)
        ·
          refine ⟨24141881779191120436208081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094587852794080290805387 24141881779191120436208081)
          ·
            refine ⟨18106411334393340327156061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24141881779191120436208081 18106411334393340327156061)
            ·
              refine ⟨6789904250397502622683523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18106411334393340327156061 6789904250397502622683523)
              ·
                refine ⟨10184856375596253934025285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789904250397502622683523 10184856375596253934025285)
                ·
                  refine ⟨1909660570424297612629741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10184856375596253934025285 1909660570424297612629741)
                  ·
                    refine ⟨716122713909111604736153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909660570424297612629741 716122713909111604736153)
                    ·
                      rfl

theorem cell22_2091966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_2091966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091966 prefixEnd_2091966 := by exact prefixLift 2091966
  have htrace : WordTrace (prefixWord ++ tailWord_2091966) baseStart_2091966 baseEnd_2091966 := by
    simpa [prefixWord, tailWord_2091966, baseEnd_2091966] using wordTrace_append hprefix tailTrace_2091966
  have hstable : (prefixWord ++ tailWord_2091966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091966).length < 2 ^ (prefixWord ++ tailWord_2091966).sum := by decide
  have hdescent : baseEnd_2091966 < baseStart_2091966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091974 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2091974 : Nat := 118140960795 + 2091974 * 2 ^ 59
def prefixEnd_2091974 : Nat := 4983230072969 + 3 ^ 40 * 2091974 * 2
def baseEnd_2091974 : Nat := 238708484157534083512043

theorem tailTrace_2091974 : CollatzResearch.WordTrace tailWord_2091974 prefixEnd_2091974 238708484157534083512043 := by
  unfold tailWord_2091974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384392503848217298741843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50867040082095302373159317 2384392503848217298741843)
  ·
    refine ⟨3576588755772325948112765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2384392503848217298741843 3576588755772325948112765)
    ·
      refine ⟨1341220783414622230542287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3576588755772325948112765 1341220783414622230542287)
      ·
        refine ⟨2011831175121933345813431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341220783414622230542287 2011831175121933345813431)
        ·
          refine ⟨3017746762682900018720147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011831175121933345813431 3017746762682900018720147)
          ·
            refine ⟨4526620144024350028080221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017746762682900018720147 4526620144024350028080221)
            ·
              refine ⟨1697482554009131260530083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4526620144024350028080221 1697482554009131260530083)
              ·
                refine ⟨2546223831013696890795125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697482554009131260530083 2546223831013696890795125)
                ·
                  refine ⟨238708484157534083512043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2546223831013696890795125 238708484157534083512043)
                  ·
                    rfl

theorem cell22_2091974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2091974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091974 prefixEnd_2091974 := by exact prefixLift 2091974
  have htrace : WordTrace (prefixWord ++ tailWord_2091974) baseStart_2091974 baseEnd_2091974 := by
    simpa [prefixWord, tailWord_2091974, baseEnd_2091974] using wordTrace_append hprefix tailTrace_2091974
  have hstable : (prefixWord ++ tailWord_2091974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091974).length < 2 ^ (prefixWord ++ tailWord_2091974).sum := by decide
  have hdescent : baseEnd_2091974 < baseStart_2091974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091977 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_2091977 : Nat := 118140960795 + 2091977 * 2 ^ 59
def prefixEnd_2091977 : Nat := 4983230072969 + 3 ^ 40 * 2091977 * 2
def baseEnd_2091977 : Nat := 716126479433911242711119

theorem tailTrace_2091977 : CollatzResearch.WordTrace tailWord_2091977 prefixEnd_2091977 716126479433911242711119 := by
  unfold tailWord_2091977
  simp only [CollatzResearch.WordTrace]
  refine ⟨76300669542132085072098185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50867113028088056714732123 76300669542132085072098185)
  ·
    refine ⟨57225502156599063804073639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76300669542132085072098185 57225502156599063804073639)
    ·
      refine ⟨85838253234898595706110459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57225502156599063804073639 85838253234898595706110459)
      ·
        refine ⟨128757379852347893559165689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85838253234898595706110459 128757379852347893559165689)
        ·
          refine ⟨96568034889260920169374267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128757379852347893559165689 96568034889260920169374267)
          ·
            refine ⟨144852052333891380254061401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96568034889260920169374267 144852052333891380254061401)
            ·
              refine ⟨108639039250418535190546051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144852052333891380254061401 108639039250418535190546051)
              ·
                refine ⟨162958558875627802785819077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108639039250418535190546051 162958558875627802785819077)
                ·
                  refine ⟨30554729789180213022341077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162958558875627802785819077 30554729789180213022341077)
                  ·
                    refine ⟨716126479433911242711119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30554729789180213022341077 716126479433911242711119)
                    ·
                      rfl

theorem cell22_2091977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_2091977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091977 prefixEnd_2091977 := by exact prefixLift 2091977
  have htrace : WordTrace (prefixWord ++ tailWord_2091977) baseStart_2091977 baseEnd_2091977 := by
    simpa [prefixWord, tailWord_2091977, baseEnd_2091977] using wordTrace_append hprefix tailTrace_2091977
  have hstable : (prefixWord ++ tailWord_2091977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091977).length < 2 ^ (prefixWord ++ tailWord_2091977).sum := by decide
  have hdescent : baseEnd_2091977 < baseStart_2091977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091983 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 2, 3]
def baseStart_2091983 : Nat := 118140960795 + 2091983 * 2 ^ 59
def prefixEnd_2091983 : Nat := 4983230072969 + 3 ^ 40 * 2091983 * 2
def baseEnd_2091983 : Nat := 716128533356529227061101

theorem tailTrace_2091983 : CollatzResearch.WordTrace tailWord_2091983 prefixEnd_2091983 716128533356529227061101 := by
  unfold tailWord_2091983
  simp only [CollatzResearch.WordTrace]
  refine ⟨76300888380110348096816603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50867258920073565397877735 76300888380110348096816603)
  ·
    refine ⟨114451332570165522145224905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76300888380110348096816603 114451332570165522145224905)
    ·
      refine ⟨85838499427624141608918679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114451332570165522145224905 85838499427624141608918679)
      ·
        refine ⟨128757749141436212413378019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85838499427624141608918679 128757749141436212413378019)
        ·
          refine ⟨193136623712154318620067029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128757749141436212413378019 193136623712154318620067029)
          ·
            refine ⟨4526639618253616842657821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 193136623712154318620067029 4526639618253616842657821)
            ·
              refine ⟨1697489856845106315996683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4526639618253616842657821 1697489856845106315996683)
              ·
                refine ⟨2546234785267659473995025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697489856845106315996683 2546234785267659473995025)
                ·
                  refine ⟨1909676088950744605496269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546234785267659473995025 1909676088950744605496269)
                  ·
                    refine ⟨716128533356529227061101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909676088950744605496269 716128533356529227061101)
                    ·
                      rfl

theorem cell22_2091983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_2091983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2091983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2091983 prefixEnd_2091983 := by exact prefixLift 2091983
  have htrace : WordTrace (prefixWord ++ tailWord_2091983) baseStart_2091983 baseEnd_2091983 := by
    simpa [prefixWord, tailWord_2091983, baseEnd_2091983] using wordTrace_append hprefix tailTrace_2091983
  have hstable : (prefixWord ++ tailWord_2091983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091983).length < 2 ^ (prefixWord ++ tailWord_2091983).sum := by decide
  have hdescent : baseEnd_2091983 < baseStart_2091983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092024 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_2092024 : Nat := 118140960795 + 2092024 * 2 ^ 59
def prefixEnd_2092024 : Nat := 4983230072969 + 3 ^ 40 * 2092024 * 2
def baseEnd_2092024 : Nat := 238714189498139595595325

theorem tailTrace_2092024 : CollatzResearch.WordTrace tailWord_2092024 prefixEnd_2092024 238714189498139595595325 := by
  unfold tailWord_2092024
  simp only [CollatzResearch.WordTrace]
  refine ⟨38151191886480906049529563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50868255848641208066039417 38151191886480906049529563)
  ·
    refine ⟨57226787829721359074294345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38151191886480906049529563 57226787829721359074294345)
    ·
      refine ⟨42920090872291019305720759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57226787829721359074294345 42920090872291019305720759)
      ·
        refine ⟨64380136308436528958581139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42920090872291019305720759 64380136308436528958581139)
        ·
          refine ⟨96570204462654793437871709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64380136308436528958581139 96570204462654793437871709)
          ·
            refine ⟨36213826673495547539201891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96570204462654793437871709 36213826673495547539201891)
            ·
              refine ⟨54320740010243321308802837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36213826673495547539201891 54320740010243321308802837)
              ·
                refine ⟨2546284687980155686350133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54320740010243321308802837 2546284687980155686350133)
                ·
                  refine ⟨238714189498139595595325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2546284687980155686350133 238714189498139595595325)
                  ·
                    rfl

theorem cell22_2092024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_2092024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092024 prefixEnd_2092024 := by exact prefixLift 2092024
  have htrace : WordTrace (prefixWord ++ tailWord_2092024) baseStart_2092024 baseEnd_2092024 := by
    simpa [prefixWord, tailWord_2092024, baseEnd_2092024] using wordTrace_append hprefix tailTrace_2092024
  have hstable : (prefixWord ++ tailWord_2092024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092024).length < 2 ^ (prefixWord ++ tailWord_2092024).sum := by decide
  have hdescent : baseEnd_2092024 < baseStart_2092024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092028 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_2092028 : Nat := 118140960795 + 2092028 * 2 ^ 59
def prefixEnd_2092028 : Nat := 4983230072969 + 3 ^ 40 * 2092028 * 2
def baseEnd_2092028 : Nat := 716143937776164109685963

theorem tailTrace_2092028 : CollatzResearch.WordTrace tailWord_2092028 prefixEnd_2092028 716143937776164109685963 := by
  unfold tailWord_2092028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38151264832473660391102369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50868353109964880521469825 38151264832473660391102369)
  ·
    refine ⟨28613448624355245293326777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38151264832473660391102369 28613448624355245293326777)
    ·
      refine ⟨21460086468266433969995083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28613448624355245293326777 21460086468266433969995083)
      ·
        refine ⟨32190129702399650954992625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21460086468266433969995083 32190129702399650954992625)
        ·
          refine ⟨24142597276799738216244469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32190129702399650954992625 24142597276799738216244469)
          ·
            refine ⟨2263368494699975457772919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24142597276799738216244469 2263368494699975457772919)
            ·
              refine ⟨3395052742049963186659379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263368494699975457772919 3395052742049963186659379)
              ·
                refine ⟨5092579113074944779989069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395052742049963186659379 5092579113074944779989069)
                ·
                  refine ⟨1909717167403104292495901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5092579113074944779989069 1909717167403104292495901)
                  ·
                    refine ⟨716143937776164109685963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909717167403104292495901 716143937776164109685963)
                    ·
                      rfl

theorem cell22_2092028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_2092028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092028 prefixEnd_2092028 := by exact prefixLift 2092028
  have htrace : WordTrace (prefixWord ++ tailWord_2092028) baseStart_2092028 baseEnd_2092028 := by
    simpa [prefixWord, tailWord_2092028, baseEnd_2092028] using wordTrace_append hprefix tailTrace_2092028
  have hstable : (prefixWord ++ tailWord_2092028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092028).length < 2 ^ (prefixWord ++ tailWord_2092028).sum := by decide
  have hdescent : baseEnd_2092028 < baseStart_2092028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092034 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2092034 : Nat := 118140960795 + 2092034 * 2 ^ 59
def prefixEnd_2092034 : Nat := 4983230072969 + 3 ^ 40 * 2092034 * 2
def baseEnd_2092034 : Nat := 716145991698782094035945

theorem tailTrace_2092034 : CollatzResearch.WordTrace tailWord_2092034 prefixEnd_2092034 716145991698782094035945 := by
  unfold tailWord_2092034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075687125731395951730789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50868499001950389204615437 19075687125731395951730789)
  ·
    refine ⟨3576691336074636740949523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19075687125731395951730789 3576691336074636740949523)
    ·
      refine ⟨5365037004111955111424285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576691336074636740949523 5365037004111955111424285)
      ·
        refine ⟨2011888876541983166784107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5365037004111955111424285 2011888876541983166784107)
        ·
          refine ⟨3017833314812974750176161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011888876541983166784107 3017833314812974750176161)
          ·
            refine ⟨2263374986109731062632121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017833314812974750176161 2263374986109731062632121)
            ·
              refine ⟨1697531239582298296974091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263374986109731062632121 1697531239582298296974091)
              ·
                refine ⟨2546296859373447445461137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697531239582298296974091 2546296859373447445461137)
                ·
                  refine ⟨1909722644530085584095853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546296859373447445461137 1909722644530085584095853)
                  ·
                    refine ⟨716145991698782094035945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909722644530085584095853 716145991698782094035945)
                    ·
                      rfl

theorem cell22_2092034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2092034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092034 prefixEnd_2092034 := by exact prefixLift 2092034
  have htrace : WordTrace (prefixWord ++ tailWord_2092034) baseStart_2092034 baseEnd_2092034 := by
    simpa [prefixWord, tailWord_2092034, baseEnd_2092034] using wordTrace_append hprefix tailTrace_2092034
  have hstable : (prefixWord ++ tailWord_2092034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092034).length < 2 ^ (prefixWord ++ tailWord_2092034).sum := by decide
  have hdescent : baseEnd_2092034 < baseStart_2092034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092039 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2092039 : Nat := 118140960795 + 2092039 * 2 ^ 59
def prefixEnd_2092039 : Nat := 4983230072969 + 3 ^ 40 * 2092039 * 2
def baseEnd_2092039 : Nat := 716147703300963747660929

theorem tailTrace_2092039 : CollatzResearch.WordTrace tailWord_2092039 prefixEnd_2092039 716147703300963747660929 := by
  unfold tailWord_2092039
  simp only [CollatzResearch.WordTrace]
  refine ⟨76302930867907469660855171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50868620578604979773903447 76302930867907469660855171)
  ·
    refine ⟨114454396301861204491282757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76302930867907469660855171 114454396301861204491282757)
    ·
      refine ⟨21460199306598975842115517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114454396301861204491282757 21460199306598975842115517)
      ·
        refine ⟨8047574739974615940793319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21460199306598975842115517 8047574739974615940793319)
        ·
          refine ⟨12071362109961923911189979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047574739974615940793319 12071362109961923911189979)
          ·
            refine ⟨18107043164942885866784969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12071362109961923911189979 18107043164942885866784969)
            ·
              refine ⟨13580282373707164400088727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18107043164942885866784969 13580282373707164400088727)
              ·
                refine ⟨20370423560560746600133091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580282373707164400088727 20370423560560746600133091)
                ·
                  refine ⟨30555635340841119900199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20370423560560746600133091 30555635340841119900199637)
                  ·
                    refine ⟨716147703300963747660929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30555635340841119900199637 716147703300963747660929)
                    ·
                      rfl

theorem cell22_2092039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2092039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092039 prefixEnd_2092039 := by exact prefixLift 2092039
  have htrace : WordTrace (prefixWord ++ tailWord_2092039) baseStart_2092039 baseEnd_2092039 := by
    simpa [prefixWord, tailWord_2092039, baseEnd_2092039] using wordTrace_append hprefix tailTrace_2092039
  have hstable : (prefixWord ++ tailWord_2092039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092039).length < 2 ^ (prefixWord ++ tailWord_2092039).sum := by decide
  have hdescent : baseEnd_2092039 < baseStart_2092039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092099 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_2092099 : Nat := 118140960795 + 2092099 * 2 ^ 59
def prefixEnd_2092099 : Nat := 4983230072969 + 3 ^ 40 * 2092099 * 2
def baseEnd_2092099 : Nat := 716168242527143591160745

theorem tailTrace_2092099 : CollatzResearch.WordTrace tailWord_2092099 prefixEnd_2092099 716168242527143591160745 := by
  unfold tailWord_2092099
  simp only [CollatzResearch.WordTrace]
  refine ⟨76305119247690099908039351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50870079498460066605359567 76305119247690099908039351)
  ·
    refine ⟨114457678871535149862059027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76305119247690099908039351 114457678871535149862059027)
    ·
      refine ⟨171686518307302724793088541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114457678871535149862059027 171686518307302724793088541)
      ·
        refine ⟨64382444365238521797408203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171686518307302724793088541 64382444365238521797408203)
        ·
          refine ⟨96573666547857782696112305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64382444365238521797408203 96573666547857782696112305)
          ·
            refine ⟨72430249910893337022084229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96573666547857782696112305 72430249910893337022084229)
            ·
              refine ⟨13580671858292500691640793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72430249910893337022084229 13580671858292500691640793)
              ·
                refine ⟨10185503893719375518730595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13580671858292500691640793 10185503893719375518730595)
                ·
                  refine ⟨15278255840579063278095893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185503893719375518730595 15278255840579063278095893)
                  ·
                    refine ⟨716168242527143591160745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15278255840579063278095893 716168242527143591160745)
                    ·
                      rfl

theorem cell22_2092099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_2092099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092099 prefixEnd_2092099 := by exact prefixLift 2092099
  have htrace : WordTrace (prefixWord ++ tailWord_2092099) baseStart_2092099 baseEnd_2092099 := by
    simpa [prefixWord, tailWord_2092099, baseEnd_2092099] using wordTrace_append hprefix tailTrace_2092099
  have hstable : (prefixWord ++ tailWord_2092099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092099).length < 2 ^ (prefixWord ++ tailWord_2092099).sum := by decide
  have hdescent : baseEnd_2092099 < baseStart_2092099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092135 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2092135 : Nat := 118140960795 + 2092135 * 2 ^ 59
def prefixEnd_2092135 : Nat := 4983230072969 + 3 ^ 40 * 2092135 * 2
def baseEnd_2092135 : Nat := 716180566062851497260635

theorem tailTrace_2092135 : CollatzResearch.WordTrace tailWord_2092135 prefixEnd_2092135 716180566062851497260635 := by
  unfold tailWord_2092135
  simp only [CollatzResearch.WordTrace]
  refine ⟨76306432275559678056349859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50870954850373118704233239 76306432275559678056349859)
  ·
    refine ⟨114459648413339517084524789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76306432275559678056349859 114459648413339517084524789)
    ·
      refine ⟨10730592038750579726674199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114459648413339517084524789 10730592038750579726674199)
      ·
        refine ⟨16095888058125869590011299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730592038750579726674199 16095888058125869590011299)
        ·
          refine ⟨24143832087188804385016949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16095888058125869590011299 24143832087188804385016949)
          ·
            refine ⟨2263484258173950411095339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24143832087188804385016949 2263484258173950411095339)
            ·
              refine ⟨3395226387260925616643009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263484258173950411095339 3395226387260925616643009)
              ·
                refine ⟨2546419790445694212482257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395226387260925616643009 2546419790445694212482257)
                ·
                  refine ⟨1909814842834270659361693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546419790445694212482257 1909814842834270659361693)
                  ·
                    refine ⟨716180566062851497260635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909814842834270659361693 716180566062851497260635)
                    ·
                      rfl

theorem cell22_2092135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2092135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092135 prefixEnd_2092135 := by exact prefixLift 2092135
  have htrace : WordTrace (prefixWord ++ tailWord_2092135) baseStart_2092135 baseEnd_2092135 := by
    simpa [prefixWord, tailWord_2092135, baseEnd_2092135] using wordTrace_append hprefix tailTrace_2092135
  have hstable : (prefixWord ++ tailWord_2092135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092135).length < 2 ^ (prefixWord ++ tailWord_2092135).sum := by decide
  have hdescent : baseEnd_2092135 < baseStart_2092135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092165 : List Nat := [1, 3, 1, 1, 7, 1, 2, 6]
def baseStart_2092165 : Nat := 118140960795 + 2092165 * 2 ^ 59
def prefixEnd_2092165 : Nat := 4983230072969 + 3 ^ 40 * 2092165 * 2
def baseEnd_2092165 : Nat := 79576759519549046556727

theorem tailTrace_2092165 : CollatzResearch.WordTrace tailWord_2092165 prefixEnd_2092165 79576759519549046556727 := by
  unfold tailWord_2092165
  simp only [CollatzResearch.WordTrace]
  refine ⟨76307526465450993179941949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50871684310300662119961299 76307526465450993179941949)
  ·
    refine ⟨28615322424544122442478231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76307526465450993179941949 28615322424544122442478231)
    ·
      refine ⟨42922983636816183663717347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28615322424544122442478231 42922983636816183663717347)
      ·
        refine ⟨64384475455224275495576021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42922983636816183663717347 64384475455224275495576021)
        ·
          refine ⟨1509011143481818956927563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64384475455224275495576021 1509011143481818956927563)
          ·
            refine ⟨2263516715222728435391345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509011143481818956927563 2263516715222728435391345)
            ·
              refine ⟨1697637536417046326543509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263516715222728435391345 1697637536417046326543509)
              ·
                refine ⟨79576759519549046556727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1697637536417046326543509 79576759519549046556727)
                ·
                  rfl

theorem cell22_2092165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 6].length) (baseStart_2092165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092165 prefixEnd_2092165 := by exact prefixLift 2092165
  have htrace : WordTrace (prefixWord ++ tailWord_2092165) baseStart_2092165 baseEnd_2092165 := by
    simpa [prefixWord, tailWord_2092165, baseEnd_2092165] using wordTrace_append hprefix tailTrace_2092165
  have hstable : (prefixWord ++ tailWord_2092165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092165).length < 2 ^ (prefixWord ++ tailWord_2092165).sum := by decide
  have hdescent : baseEnd_2092165 < baseStart_2092165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092197 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_2092197 : Nat := 118140960795 + 2092197 * 2 ^ 59
def prefixEnd_2092197 : Nat := 4983230072969 + 3 ^ 40 * 2092197 * 2
def baseEnd_2092197 : Nat := 716201789929904002210445

theorem tailTrace_2092197 : CollatzResearch.WordTrace tailWord_2092197 prefixEnd_2092197 716201789929904002210445 := by
  unfold tailWord_2092197
  simp only [CollatzResearch.WordTrace]
  refine ⟨76308693601335062645106845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50872462400890041763404563 76308693601335062645106845)
  ·
    refine ⟨28615760100500648491915067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76308693601335062645106845 28615760100500648491915067)
    ·
      refine ⟨42923640150750972737872601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28615760100500648491915067 42923640150750972737872601)
      ·
        refine ⟨32192730113063229553404451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42923640150750972737872601 32192730113063229553404451)
        ·
          refine ⟨48289095169594844330106677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32192730113063229553404451 48289095169594844330106677)
          ·
            refine ⟨4527102672149516655947501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48289095169594844330106677 4527102672149516655947501)
            ·
              refine ⟨1697663502056068745980313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4527102672149516655947501 1697663502056068745980313)
              ·
                refine ⟨1273247626542051559485235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697663502056068745980313 1273247626542051559485235)
                ·
                  refine ⟨1909871439813077339227853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273247626542051559485235 1909871439813077339227853)
                  ·
                    refine ⟨716201789929904002210445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909871439813077339227853 716201789929904002210445)
                    ·
                      rfl

theorem cell22_2092197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_2092197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092197 prefixEnd_2092197 := by exact prefixLift 2092197
  have htrace : WordTrace (prefixWord ++ tailWord_2092197) baseStart_2092197 baseEnd_2092197 := by
    simpa [prefixWord, tailWord_2092197, baseEnd_2092197] using wordTrace_append hprefix tailTrace_2092197
  have hstable : (prefixWord ++ tailWord_2092197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092197).length < 2 ^ (prefixWord ++ tailWord_2092197).sum := by decide
  have hdescent : baseEnd_2092197 < baseStart_2092197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092210 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_2092210 : Nat := 118140960795 + 2092210 * 2 ^ 59
def prefixEnd_2092210 : Nat := 4983230072969 + 3 ^ 40 * 2092210 * 2
def baseEnd_2092210 : Nat := 238735413365192100545135

theorem tailTrace_2092210 : CollatzResearch.WordTrace tailWord_2092210 prefixEnd_2092210 238735413365192100545135 := by
  unfold tailWord_2092210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19077291937571991466332521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50872778500191977243553389 19077291937571991466332521)
  ·
    refine ⟨14307968953178993599749391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19077291937571991466332521 14307968953178993599749391)
    ·
      refine ⟨21461953429768490399624087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14307968953178993599749391 21461953429768490399624087)
      ·
        refine ⟨32192930144652735599436131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21461953429768490399624087 32192930144652735599436131)
        ·
          refine ⟨48289395216979103399154197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32192930144652735599436131 48289395216979103399154197)
          ·
            refine ⟨2263565400795895471835353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48289395216979103399154197 2263565400795895471835353)
            ·
              refine ⟨1697674050596921603876515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263565400795895471835353 1697674050596921603876515)
              ·
                refine ⟨2546511075895382405814773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697674050596921603876515 2546511075895382405814773)
                ·
                  refine ⟨238735413365192100545135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2546511075895382405814773 238735413365192100545135)
                  ·
                    rfl

theorem cell22_2092210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_2092210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092210 prefixEnd_2092210 := by exact prefixLift 2092210
  have htrace : WordTrace (prefixWord ++ tailWord_2092210) baseStart_2092210 baseEnd_2092210 := by
    simpa [prefixWord, tailWord_2092210, baseEnd_2092210] using wordTrace_append hprefix tailTrace_2092210
  have hstable : (prefixWord ++ tailWord_2092210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092210).length < 2 ^ (prefixWord ++ tailWord_2092210).sum := by decide
  have hdescent : baseEnd_2092210 < baseStart_2092210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092221 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2092221 : Nat := 118140960795 + 2092221 * 2 ^ 59
def prefixEnd_2092221 : Nat := 4983230072969 + 3 ^ 40 * 2092221 * 2
def baseEnd_2092221 : Nat := 238736668540125313203457

theorem tailTrace_2092221 : CollatzResearch.WordTrace tailWord_2092221 prefixEnd_2092221 238736668540125313203457 := by
  unfold tailWord_2092221
  simp only [CollatzResearch.WordTrace]
  refine ⟨76309568953248114743980517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50873045968832076495987011 76309568953248114743980517)
  ·
    refine ⟨14308044178734021514496347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76309568953248114743980517 14308044178734021514496347)
    ·
      refine ⟨21462066268101032271744521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14308044178734021514496347 21462066268101032271744521)
      ·
        refine ⟨16096549701075774203808391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21462066268101032271744521 16096549701075774203808391)
        ·
          refine ⟨24144824551613661305712587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096549701075774203808391 24144824551613661305712587)
          ·
            refine ⟨36217236827420491958568881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24144824551613661305712587 36217236827420491958568881)
            ·
              refine ⟨27162927620565368968926661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36217236827420491958568881 27162927620565368968926661)
              ·
                refine ⟨5093048928856006681673749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27162927620565368968926661 5093048928856006681673749)
                ·
                  refine ⟨238736668540125313203457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5093048928856006681673749 238736668540125313203457)
                  ·
                    rfl

theorem cell22_2092221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2092221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092221 prefixEnd_2092221 := by exact prefixLift 2092221
  have htrace : WordTrace (prefixWord ++ tailWord_2092221) baseStart_2092221 baseEnd_2092221 := by
    simpa [prefixWord, tailWord_2092221, baseEnd_2092221] using wordTrace_append hprefix tailTrace_2092221
  have hstable : (prefixWord ++ tailWord_2092221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092221).length < 2 ^ (prefixWord ++ tailWord_2092221).sum := by decide
  have hdescent : baseEnd_2092221 < baseStart_2092221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092223 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 1, 4]
def baseStart_2092223 : Nat := 118140960795 + 2092223 * 2 ^ 59
def prefixEnd_2092223 : Nat := 4983230072969 + 3 ^ 40 * 2092223 * 2
def baseEnd_2092223 : Nat := 716210690261248601060365

theorem tailTrace_2092223 : CollatzResearch.WordTrace tailWord_2092223 prefixEnd_2092223 716210690261248601060365 := by
  unfold tailWord_2092223
  simp only [CollatzResearch.WordTrace]
  refine ⟨76309641899240869085553323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50873094599493912723702215 76309641899240869085553323)
  ·
    refine ⟨114464462848861303628329985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76309641899240869085553323 114464462848861303628329985)
    ·
      refine ⟨85848347136645977721247489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114464462848861303628329985 85848347136645977721247489)
      ·
        refine ⟨64386260352484483290935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85848347136645977721247489 64386260352484483290935617)
        ·
          refine ⟨48289695264363362468201713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64386260352484483290935617 48289695264363362468201713)
          ·
            refine ⟨36217271448272521851151285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48289695264363362468201713 36217271448272521851151285)
            ·
              refine ⟨3395369198275548923545433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36217271448272521851151285 3395369198275548923545433)
              ·
                refine ⟨2546526898706661692659075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395369198275548923545433 2546526898706661692659075)
                ·
                  refine ⟨3819790348059992538988613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546526898706661692659075 3819790348059992538988613)
                  ·
                    refine ⟨716210690261248601060365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3819790348059992538988613 716210690261248601060365)
                    ·
                      rfl

theorem cell22_2092223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_2092223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092223 prefixEnd_2092223 := by exact prefixLift 2092223
  have htrace : WordTrace (prefixWord ++ tailWord_2092223) baseStart_2092223 baseEnd_2092223 := by
    simpa [prefixWord, tailWord_2092223, baseEnd_2092223] using wordTrace_append hprefix tailTrace_2092223
  have hstable : (prefixWord ++ tailWord_2092223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092223).length < 2 ^ (prefixWord ++ tailWord_2092223).sum := by decide
  have hdescent : baseEnd_2092223 < baseStart_2092223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092255 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 4]
def baseStart_2092255 : Nat := 118140960795 + 2092255 * 2 ^ 59
def prefixEnd_2092255 : Nat := 4983230072969 + 3 ^ 40 * 2092255 * 2
def baseEnd_2092255 : Nat := 238740548171737061420089

theorem tailTrace_2092255 : CollatzResearch.WordTrace tailWord_2092255 prefixEnd_2092255 238740548171737061420089 := by
  unfold tailWord_2092255
  simp only [CollatzResearch.WordTrace]
  refine ⟨76310809035124938550718219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50873872690083292367145479 76310809035124938550718219)
  ·
    refine ⟨114466213552687407826077329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76310809035124938550718219 114466213552687407826077329)
    ·
      refine ⟨85849660164515555869557997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114466213552687407826077329 85849660164515555869557997)
      ·
        refine ⟨32193622561693333451084249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85849660164515555869557997 32193622561693333451084249)
        ·
          refine ⟨24145216921270000088313187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32193622561693333451084249 24145216921270000088313187)
          ·
            refine ⟨36217825381905000132469781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24145216921270000088313187 36217825381905000132469781)
            ·
              refine ⟨1697710564776796881209521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36217825381905000132469781 1697710564776796881209521)
              ·
                refine ⟨1273282923582597660907141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697710564776796881209521 1273282923582597660907141)
                ·
                  refine ⟨238740548171737061420089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273282923582597660907141 238740548171737061420089)
                  ·
                    rfl

theorem cell22_2092255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 4].length) (baseStart_2092255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092255 prefixEnd_2092255 := by exact prefixLift 2092255
  have htrace : WordTrace (prefixWord ++ tailWord_2092255) baseStart_2092255 baseEnd_2092255 := by
    simpa [prefixWord, tailWord_2092255, baseEnd_2092255] using wordTrace_append hprefix tailTrace_2092255
  have hstable : (prefixWord ++ tailWord_2092255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092255).length < 2 ^ (prefixWord ++ tailWord_2092255).sum := by decide
  have hdescent : baseEnd_2092255 < baseStart_2092255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092270 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2092270 : Nat := 118140960795 + 2092270 * 2 ^ 59
def prefixEnd_2092270 : Nat := 4983230072969 + 3 ^ 40 * 2092270 * 2
def baseEnd_2092270 : Nat := 716226779321756145135221

theorem tailTrace_2092270 : CollatzResearch.WordTrace tailWord_2092270 prefixEnd_2092270 716226779321756145135221 := by
  unfold tailWord_2092270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538919516258824514064283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50874237420047064075009509 9538919516258824514064283)
  ·
    refine ⟨14308379274388236771096425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9538919516258824514064283 14308379274388236771096425)
    ·
      refine ⟨10731284455791177578322319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14308379274388236771096425 10731284455791177578322319)
      ·
        refine ⟨16096926683686766367483479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731284455791177578322319 16096926683686766367483479)
        ·
          refine ⟨24145390025530149551225219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096926683686766367483479 24145390025530149551225219)
          ·
            refine ⟨36218085038295224326837829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24145390025530149551225219 36218085038295224326837829)
            ·
              refine ⟨6790890944680354561282093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36218085038295224326837829 6790890944680354561282093)
              ·
                refine ⟨2546584104255132960480785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6790890944680354561282093 2546584104255132960480785)
                ·
                  refine ⟨1909938078191349720360589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546584104255132960480785 1909938078191349720360589)
                  ·
                    refine ⟨716226779321756145135221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909938078191349720360589 716226779321756145135221)
                    ·
                      rfl

theorem cell22_2092270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2092270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092270 prefixEnd_2092270 := by exact prefixLift 2092270
  have htrace : WordTrace (prefixWord ++ tailWord_2092270) baseStart_2092270 baseEnd_2092270 := by
    simpa [prefixWord, tailWord_2092270, baseEnd_2092270] using wordTrace_append hprefix tailTrace_2092270
  have hstable : (prefixWord ++ tailWord_2092270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092270).length < 2 ^ (prefixWord ++ tailWord_2092270).sum := by decide
  have hdescent : baseEnd_2092270 < baseStart_2092270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092298 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_2092298 : Nat := 118140960795 + 2092298 * 2 ^ 59
def prefixEnd_2092298 : Nat := 4983230072969 + 3 ^ 40 * 2092298 * 2
def baseEnd_2092298 : Nat := 716236364293973405435135

theorem tailTrace_2092298 : CollatzResearch.WordTrace tailWord_2092298 prefixEnd_2092298 716236364293973405435135 := by
  unfold tailWord_2092298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078094343492289223633387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50874918249312771263022365 19078094343492289223633387)
  ·
    refine ⟨28617141515238433835450081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19078094343492289223633387 28617141515238433835450081)
    ·
      refine ⟨21462856136428825376587561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28617141515238433835450081 21462856136428825376587561)
      ·
        refine ⟨16097142102321619032440671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21462856136428825376587561 16097142102321619032440671)
        ·
          refine ⟨24145713153482428548661007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097142102321619032440671 24145713153482428548661007)
          ·
            refine ⟨36218569730223642822991511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24145713153482428548661007 36218569730223642822991511)
            ·
              refine ⟨54327854595335464234487267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36218569730223642822991511 54327854595335464234487267)
              ·
                refine ⟨81491781893003196351730901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54327854595335464234487267 81491781893003196351730901)
                ·
                  refine ⟨1909963638117262414493693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 81491781893003196351730901 1909963638117262414493693)
                  ·
                    refine ⟨716236364293973405435135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909963638117262414493693 716236364293973405435135)
                    ·
                      rfl

theorem cell22_2092298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_2092298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092298 prefixEnd_2092298 := by exact prefixLift 2092298
  have htrace : WordTrace (prefixWord ++ tailWord_2092298) baseStart_2092298 baseEnd_2092298 := by
    simpa [prefixWord, tailWord_2092298, baseEnd_2092298] using wordTrace_append hprefix tailTrace_2092298
  have hstable : (prefixWord ++ tailWord_2092298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092298).length < 2 ^ (prefixWord ++ tailWord_2092298).sum := by decide
  have hdescent : baseEnd_2092298 < baseStart_2092298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092420 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2092420 : Nat := 118140960795 + 2092420 * 2 ^ 59
def prefixEnd_2092420 : Nat := 4983230072969 + 3 ^ 40 * 2092420 * 2
def baseEnd_2092420 : Nat := 716278127387205753884761

theorem tailTrace_2092420 : CollatzResearch.WordTrace tailWord_2092420 prefixEnd_2092420 716278127387205753884761 := by
  unfold tailWord_2092420
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158413539763585865237357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50877884719684781153649809 38158413539763585865237357)
  ·
    refine ⟨14309405077411344699464009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38158413539763585865237357 14309405077411344699464009)
    ·
      refine ⟨10732053808058508524598007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14309405077411344699464009 10732053808058508524598007)
      ·
        refine ⟨16098080712087762786897011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732053808058508524598007 16098080712087762786897011)
        ·
          refine ⟨24147121068131644180345517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16098080712087762786897011 24147121068131644180345517)
          ·
            refine ⟨9055170400549366567629569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24147121068131644180345517 9055170400549366567629569)
            ·
              refine ⟨6791377800412024925722177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9055170400549366567629569 6791377800412024925722177)
              ·
                refine ⟨5093533350309018694291633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6791377800412024925722177 5093533350309018694291633)
                ·
                  refine ⟨3820150012731764020718725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093533350309018694291633 3820150012731764020718725)
                  ·
                    refine ⟨716278127387205753884761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820150012731764020718725 716278127387205753884761)
                    ·
                      rfl

theorem cell22_2092420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2092420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092420 prefixEnd_2092420 := by exact prefixLift 2092420
  have htrace : WordTrace (prefixWord ++ tailWord_2092420) baseStart_2092420 baseEnd_2092420 := by
    simpa [prefixWord, tailWord_2092420, baseEnd_2092420] using wordTrace_append hprefix tailTrace_2092420
  have hstable : (prefixWord ++ tailWord_2092420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092420).length < 2 ^ (prefixWord ++ tailWord_2092420).sum := by decide
  have hdescent : baseEnd_2092420 < baseStart_2092420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092424 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 4]
def baseStart_2092424 : Nat := 118140960795 + 2092424 * 2 ^ 59
def prefixEnd_2092424 : Nat := 4983230072969 + 3 ^ 40 * 2092424 * 2
def baseEnd_2092424 : Nat := 238759832222983692261583

theorem tailTrace_2092424 : CollatzResearch.WordTrace tailWord_2092424 prefixEnd_2092424 238759832222983692261583 := by
  unfold tailWord_2092424
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158486485756340206810163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50877981981008453609080217 38158486485756340206810163)
  ·
    refine ⟨57237729728634510310215245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38158486485756340206810163 57237729728634510310215245)
    ·
      refine ⟨21464148648237941366330717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57237729728634510310215245 21464148648237941366330717)
      ·
        refine ⟨8049055743089228012374019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21464148648237941366330717 8049055743089228012374019)
        ·
          refine ⟨12073583614633842018561029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049055743089228012374019 12073583614633842018561029)
          ·
            refine ⟨2263796927743845378480193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12073583614633842018561029 2263796927743845378480193)
            ·
              refine ⟨1697847695807884033860145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263796927743845378480193 1697847695807884033860145)
              ·
                refine ⟨1273385771855913025395109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697847695807884033860145 1273385771855913025395109)
                ·
                  refine ⟨238759832222983692261583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273385771855913025395109 238759832222983692261583)
                  ·
                    rfl

theorem cell22_2092424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_2092424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092424 prefixEnd_2092424 := by exact prefixLift 2092424
  have htrace : WordTrace (prefixWord ++ tailWord_2092424) baseStart_2092424 baseEnd_2092424 := by
    simpa [prefixWord, tailWord_2092424, baseEnd_2092424] using wordTrace_append hprefix tailTrace_2092424
  have hstable : (prefixWord ++ tailWord_2092424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092424).length < 2 ^ (prefixWord ++ tailWord_2092424).sum := by decide
  have hdescent : baseEnd_2092424 < baseStart_2092424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092448 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_2092448 : Nat := 118140960795 + 2092448 * 2 ^ 59
def prefixEnd_2092448 : Nat := 4983230072969 + 3 ^ 40 * 2092448 * 2
def baseEnd_2092448 : Nat := 716287712359423014184675

theorem tailTrace_2092448 : CollatzResearch.WordTrace tailWord_2092448 prefixEnd_2092448 716287712359423014184675 := by
  unfold tailWord_2092448
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158924161712866256246999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50878565548950488341662665 38158924161712866256246999)
  ·
    refine ⟨57238386242569299384370499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38158924161712866256246999 57238386242569299384370499)
    ·
      refine ⟨85857579363853949076555749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57238386242569299384370499 85857579363853949076555749)
      ·
        refine ⟨16098296130722615451854203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85857579363853949076555749 16098296130722615451854203)
        ·
          refine ⟨24147444196083923177781305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16098296130722615451854203 24147444196083923177781305)
          ·
            refine ⟨18110583147062942383335979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24147444196083923177781305 18110583147062942383335979)
            ·
              refine ⟨27165874720594413575003969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18110583147062942383335979 27165874720594413575003969)
              ·
                refine ⟨20374406040445810181252977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27165874720594413575003969 20374406040445810181252977)
                ·
                  refine ⟨15280804530334357635939733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20374406040445810181252977 15280804530334357635939733)
                  ·
                    refine ⟨716287712359423014184675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15280804530334357635939733 716287712359423014184675)
                    ·
                      rfl

theorem cell22_2092448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_2092448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092448 prefixEnd_2092448 := by exact prefixLift 2092448
  have htrace : WordTrace (prefixWord ++ tailWord_2092448) baseStart_2092448 baseEnd_2092448 := by
    simpa [prefixWord, tailWord_2092448, baseEnd_2092448] using wordTrace_append hprefix tailTrace_2092448
  have hstable : (prefixWord ++ tailWord_2092448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092448).length < 2 ^ (prefixWord ++ tailWord_2092448).sum := by decide
  have hdescent : baseEnd_2092448 < baseStart_2092448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092480 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_2092480 : Nat := 118140960795 + 2092480 * 2 ^ 59
def prefixEnd_2092480 : Nat := 4983230072969 + 3 ^ 40 * 2092480 * 2
def baseEnd_2092480 : Nat := 238766222204461865794859

theorem tailTrace_2092480 : CollatzResearch.WordTrace tailWord_2092480 prefixEnd_2092480 238766222204461865794859 := by
  unfold tailWord_2092480
  simp only [CollatzResearch.WordTrace]
  refine ⟨38159507729654900988829447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50879343639539867985105929 38159507729654900988829447)
  ·
    refine ⟨57239261594482351483244171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38159507729654900988829447 57239261594482351483244171)
    ·
      refine ⟨85858892391723527224866257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57239261594482351483244171 85858892391723527224866257)
      ·
        refine ⟨64394169293792645418649693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85858892391723527224866257 64394169293792645418649693)
        ·
          refine ⟨24147813485172242031993635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64394169293792645418649693 24147813485172242031993635)
          ·
            refine ⟨36221720227758363047990453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24147813485172242031993635 36221720227758363047990453)
            ·
              refine ⟨3395786271352346535749105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36221720227758363047990453 3395786271352346535749105)
              ·
                refine ⟨2546839703514259901811829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395786271352346535749105 2546839703514259901811829)
                ·
                  refine ⟨238766222204461865794859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2546839703514259901811829 238766222204461865794859)
                  ·
                    rfl

theorem cell22_2092480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_2092480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092480 prefixEnd_2092480 := by exact prefixLift 2092480
  have htrace : WordTrace (prefixWord ++ tailWord_2092480) baseStart_2092480 baseEnd_2092480 := by
    simpa [prefixWord, tailWord_2092480, baseEnd_2092480] using wordTrace_append hprefix tailTrace_2092480
  have hstable : (prefixWord ++ tailWord_2092480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092480).length < 2 ^ (prefixWord ++ tailWord_2092480).sum := by decide
  have hdescent : baseEnd_2092480 < baseStart_2092480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092484 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2092484 : Nat := 118140960795 + 2092484 * 2 ^ 59
def prefixEnd_2092484 : Nat := 4983230072969 + 3 ^ 40 * 2092484 * 2
def baseEnd_2092484 : Nat := 716300035895130920284565

theorem tailTrace_2092484 : CollatzResearch.WordTrace tailWord_2092484 prefixEnd_2092484 716300035895130920284565 := by
  unfold tailWord_2092484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38159580675647655330402253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50879440900863540440536337 38159580675647655330402253)
  ·
    refine ⟨14309842753367870748900845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38159580675647655330402253 14309842753367870748900845)
    ·
      refine ⟨5366191032512951530837817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14309842753367870748900845 5366191032512951530837817)
      ·
        refine ⟨4024643274384713648128363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5366191032512951530837817 4024643274384713648128363)
        ·
          refine ⟨6036964911577070472192545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024643274384713648128363 6036964911577070472192545)
          ·
            refine ⟨4527723683682802854144409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036964911577070472192545 4527723683682802854144409)
            ·
              refine ⟨3395792762762102140608307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527723683682802854144409 3395792762762102140608307)
              ·
                refine ⟨5093689144143153210912461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395792762762102140608307 5093689144143153210912461)
                ·
                  refine ⟨1910133429053682454092173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5093689144143153210912461 1910133429053682454092173)
                  ·
                    refine ⟨716300035895130920284565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910133429053682454092173 716300035895130920284565)
                    ·
                      rfl

theorem cell22_2092484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2092484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092484 prefixEnd_2092484 := by exact prefixLift 2092484
  have htrace : WordTrace (prefixWord ++ tailWord_2092484) baseStart_2092484 baseEnd_2092484 := by
    simpa [prefixWord, tailWord_2092484, baseEnd_2092484] using wordTrace_append hprefix tailTrace_2092484
  have hstable : (prefixWord ++ tailWord_2092484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092484).length < 2 ^ (prefixWord ++ tailWord_2092484).sum := by decide
  have hdescent : baseEnd_2092484 < baseStart_2092484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092572 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2092572 : Nat := 118140960795 + 2092572 * 2 ^ 59
def prefixEnd_2092572 : Nat := 4983230072969 + 3 ^ 40 * 2092572 * 2
def baseEnd_2092572 : Nat := 716330160093528024084295

theorem tailTrace_2092572 : CollatzResearch.WordTrace tailWord_2092572 prefixEnd_2092572 716330160093528024084295 := by
  unfold tailWord_2092572
  simp only [CollatzResearch.WordTrace]
  refine ⟨38161185487488250845003985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50881580649984334460005313 38161185487488250845003985)
  ·
    refine ⟨28620889115616188133752989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38161185487488250845003985 28620889115616188133752989)
    ·
      refine ⟨10732833418356070550157371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28620889115616188133752989 10732833418356070550157371)
      ·
        refine ⟨16099250127534105825236057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732833418356070550157371 16099250127534105825236057)
        ·
          refine ⟨12074437595650579368927043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16099250127534105825236057 12074437595650579368927043)
          ·
            refine ⟨18111656393475869053390565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12074437595650579368927043 18111656393475869053390565)
            ·
              refine ⟨3395935573776725447510731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18111656393475869053390565 3395935573776725447510731)
              ·
                refine ⟨5093903360665088171266097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395935573776725447510731 5093903360665088171266097)
                ·
                  refine ⟨3820427520498816128449573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093903360665088171266097 3820427520498816128449573)
                  ·
                    refine ⟨716330160093528024084295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820427520498816128449573 716330160093528024084295)
                    ·
                      rfl

theorem cell22_2092572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2092572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092572 prefixEnd_2092572 := by exact prefixLift 2092572
  have htrace : WordTrace (prefixWord ++ tailWord_2092572) baseStart_2092572 baseEnd_2092572 := by
    simpa [prefixWord, tailWord_2092572, baseEnd_2092572] using wordTrace_append hprefix tailTrace_2092572
  have hstable : (prefixWord ++ tailWord_2092572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092572).length < 2 ^ (prefixWord ++ tailWord_2092572).sum := by decide
  have hdescent : baseEnd_2092572 < baseStart_2092572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092600 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_2092600 : Nat := 118140960795 + 2092600 * 2 ^ 59
def prefixEnd_2092600 : Nat := 4983230072969 + 3 ^ 40 * 2092600 * 2
def baseEnd_2092600 : Nat := 716339745065745284384209

theorem tailTrace_2092600 : CollatzResearch.WordTrace tailWord_2092600 prefixEnd_2092600 716339745065745284384209 := by
  unfold tailWord_2092600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38161696109437531236013627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50882261479250041648018169 38161696109437531236013627)
  ·
    refine ⟨57242544164156296854020441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38161696109437531236013627 57242544164156296854020441)
    ·
      refine ⟨42931908123117222640515331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57242544164156296854020441 42931908123117222640515331)
      ·
        refine ⟨64397862184675833960772997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42931908123117222640515331 64397862184675833960772997)
        ·
          refine ⟨12074599159626718867644937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64397862184675833960772997 12074599159626718867644937)
          ·
            refine ⟨9055949369720039150733703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12074599159626718867644937 9055949369720039150733703)
            ·
              refine ⟨13583924054580058726100555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055949369720039150733703 13583924054580058726100555)
              ·
                refine ⟨20375886081870088089150833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583924054580058726100555 20375886081870088089150833)
                ·
                  refine ⟨15281914561402566066863125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20375886081870088089150833 15281914561402566066863125)
                  ·
                    refine ⟨716339745065745284384209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15281914561402566066863125 716339745065745284384209)
                    ·
                      rfl

theorem cell22_2092600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_2092600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092600 prefixEnd_2092600 := by exact prefixLift 2092600
  have htrace : WordTrace (prefixWord ++ tailWord_2092600) baseStart_2092600 baseEnd_2092600 := by
    simpa [prefixWord, tailWord_2092600, baseEnd_2092600] using wordTrace_append hprefix tailTrace_2092600
  have hstable : (prefixWord ++ tailWord_2092600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092600).length < 2 ^ (prefixWord ++ tailWord_2092600).sum := by decide
  have hdescent : baseEnd_2092600 < baseStart_2092600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092602 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_2092602 : Nat := 118140960795 + 2092602 * 2 ^ 59
def prefixEnd_2092602 : Nat := 4983230072969 + 3 ^ 40 * 2092602 * 2
def baseEnd_2092602 : Nat := 716340429706617945834203

theorem tailTrace_2092602 : CollatzResearch.WordTrace tailWord_2092602 prefixEnd_2092602 716340429706617945834203 := by
  unfold tailWord_2092602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19080866291216954203400015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50882310109911877875733373 19080866291216954203400015)
  ·
    refine ⟨28621299436825431305100023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19080866291216954203400015 28621299436825431305100023)
    ·
      refine ⟨42931949155238146957650035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28621299436825431305100023 42931949155238146957650035)
      ·
        refine ⟨64397923732857220436475053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42931949155238146957650035 64397923732857220436475053)
        ·
          refine ⟨24149221399821457663678145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64397923732857220436475053 24149221399821457663678145)
          ·
            refine ⟨18111916049866093247758609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24149221399821457663678145 18111916049866093247758609)
            ·
              refine ⟨13583937037399569935818957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18111916049866093247758609 13583937037399569935818957)
              ·
                refine ⟨5093976389024838725932109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13583937037399569935818957 5093976389024838725932109)
                ·
                  refine ⟨1910241145884314522224541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5093976389024838725932109 1910241145884314522224541)
                  ·
                    refine ⟨716340429706617945834203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910241145884314522224541 716340429706617945834203)
                    ·
                      rfl

theorem cell22_2092602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_2092602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092602 prefixEnd_2092602 := by exact prefixLift 2092602
  have htrace : WordTrace (prefixWord ++ tailWord_2092602) baseStart_2092602 baseEnd_2092602 := by
    simpa [prefixWord, tailWord_2092602, baseEnd_2092602] using wordTrace_append hprefix tailTrace_2092602
  have hstable : (prefixWord ++ tailWord_2092602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092602).length < 2 ^ (prefixWord ++ tailWord_2092602).sum := by decide
  have hdescent : baseEnd_2092602 < baseStart_2092602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092604 : List Nat := [2, 2, 2, 2, 5, 1, 1, 7]
def baseStart_2092604 : Nat := 118140960795 + 2092604 * 2 ^ 59
def prefixEnd_2092604 : Nat := 4983230072969 + 3 ^ 40 * 2092604 * 2
def baseEnd_2092604 : Nat := 79593457149721178587133

theorem tailTrace_2092604 : CollatzResearch.WordTrace tailWord_2092604 prefixEnd_2092604 79593457149721178587133 := by
  unfold tailWord_2092604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38161769055430285577586433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50882358740573714103448577 38161769055430285577586433)
  ·
    refine ⟨28621326791572714183189825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38161769055430285577586433 28621326791572714183189825)
    ·
      refine ⟨21465995093679535637392369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28621326791572714183189825 21465995093679535637392369)
      ·
        refine ⟨16099496320259651728044277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21465995093679535637392369 16099496320259651728044277)
        ·
          refine ⟨1509327780024342349504151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16099496320259651728044277 1509327780024342349504151)
          ·
            refine ⟨2263991670036513524256227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509327780024342349504151 2263991670036513524256227)
            ·
              refine ⟨3395987505054770286384341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263991670036513524256227 3395987505054770286384341)
              ·
                refine ⟨79593457149721178587133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3395987505054770286384341 79593457149721178587133)
                ·
                  rfl

theorem cell22_2092604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 7].length) (baseStart_2092604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092604 prefixEnd_2092604 := by exact prefixLift 2092604
  have htrace : WordTrace (prefixWord ++ tailWord_2092604) baseStart_2092604 baseEnd_2092604 := by
    simpa [prefixWord, tailWord_2092604, baseEnd_2092604] using wordTrace_append hprefix tailTrace_2092604
  have hstable : (prefixWord ++ tailWord_2092604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092604).length < 2 ^ (prefixWord ++ tailWord_2092604).sum := by decide
  have hdescent : baseEnd_2092604 < baseStart_2092604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092636 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2092636 : Nat := 118140960795 + 2092636 * 2 ^ 59
def prefixEnd_2092636 : Nat := 4983230072969 + 3 ^ 40 * 2092636 * 2
def baseEnd_2092636 : Nat := 716352068601453190484099

theorem tailTrace_2092636 : CollatzResearch.WordTrace tailWord_2092636 prefixEnd_2092636 716352068601453190484099 := by
  unfold tailWord_2092636
  simp only [CollatzResearch.WordTrace]
  refine ⟨38162352623372320310168881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50883136831163093746891841 38162352623372320310168881)
  ·
    refine ⟨28621764467529240232626661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38162352623372320310168881 28621764467529240232626661)
    ·
      refine ⟨5366580837661732543617499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28621764467529240232626661 5366580837661732543617499)
      ·
        refine ⟨8049871256492598815426249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366580837661732543617499 8049871256492598815426249)
        ·
          refine ⟨6037403442369449111569687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8049871256492598815426249 6037403442369449111569687)
          ·
            refine ⟨9056105163554173667354531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037403442369449111569687 9056105163554173667354531)
            ·
              refine ⟨13584157745331260501031797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056105163554173667354531 13584157745331260501031797)
              ·
                refine ⟨1273514788624805671971731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13584157745331260501031797 1273514788624805671971731)
                ·
                  refine ⟨1910272182937208507957597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273514788624805671971731 1910272182937208507957597)
                  ·
                    refine ⟨716352068601453190484099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910272182937208507957597 716352068601453190484099)
                    ·
                      rfl

theorem cell22_2092636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2092636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092636 prefixEnd_2092636 := by exact prefixLift 2092636
  have htrace : WordTrace (prefixWord ++ tailWord_2092636) baseStart_2092636 baseEnd_2092636 := by
    simpa [prefixWord, tailWord_2092636, baseEnd_2092636] using wordTrace_append hprefix tailTrace_2092636
  have hstable : (prefixWord ++ tailWord_2092636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092636).length < 2 ^ (prefixWord ++ tailWord_2092636).sum := by decide
  have hdescent : baseEnd_2092636 < baseStart_2092636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092679 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2092679 : Nat := 118140960795 + 2092679 * 2 ^ 59
def prefixEnd_2092679 : Nat := 4983230072969 + 3 ^ 40 * 2092679 * 2
def baseEnd_2092679 : Nat := 716366788380215411658967

theorem tailTrace_2092679 : CollatzResearch.WordTrace tailWord_2092679 prefixEnd_2092679 716366788380215411658967 := by
  unfold tailWord_2092679
  simp only [CollatzResearch.WordTrace]
  refine ⟨76326273585588858964153091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50884182390392572642768727 76326273585588858964153091)
  ·
    refine ⟨114489410378383288446229637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76326273585588858964153091 114489410378383288446229637)
    ·
      refine ⟨21466764445946866583668057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114489410378383288446229637 21466764445946866583668057)
      ·
        refine ⟨16100073334460149937751043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21466764445946866583668057 16100073334460149937751043)
        ·
          refine ⟨24150110001690224906626565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100073334460149937751043 24150110001690224906626565)
          ·
            refine ⟨4528145625316917169992481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24150110001690224906626565 4528145625316917169992481)
            ·
              refine ⟨3396109218987687877494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528145625316917169992481 3396109218987687877494361)
              ·
                refine ⟨2547081914240765908120771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396109218987687877494361 2547081914240765908120771)
                ·
                  refine ⟨3820622871361148862181157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547081914240765908120771 3820622871361148862181157)
                  ·
                    refine ⟨716366788380215411658967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820622871361148862181157 716366788380215411658967)
                    ·
                      rfl

theorem cell22_2092679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2092679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092679 prefixEnd_2092679 := by exact prefixLift 2092679
  have htrace : WordTrace (prefixWord ++ tailWord_2092679) baseStart_2092679 baseEnd_2092679 := by
    simpa [prefixWord, tailWord_2092679, baseEnd_2092679] using wordTrace_append hprefix tailTrace_2092679
  have hstable : (prefixWord ++ tailWord_2092679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092679).length < 2 ^ (prefixWord ++ tailWord_2092679).sum := by decide
  have hdescent : baseEnd_2092679 < baseStart_2092679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092707 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 2, 4]
def baseStart_2092707 : Nat := 118140960795 + 2092707 * 2 ^ 59
def prefixEnd_2092707 : Nat := 4983230072969 + 3 ^ 40 * 2092707 * 2
def baseEnd_2092707 : Nat := 716376373352432671958881

theorem tailTrace_2092707 : CollatzResearch.WordTrace tailWord_2092707 prefixEnd_2092707 716376373352432671958881 := by
  unfold tailWord_2092707
  simp only [CollatzResearch.WordTrace]
  refine ⟨76327294829487419746172375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50884863219658279830781583 76327294829487419746172375)
  ·
    refine ⟨114490942244231129619258563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76327294829487419746172375 114490942244231129619258563)
    ·
      refine ⟨171736413366346694428887845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114490942244231129619258563 171736413366346694428887845)
      ·
        refine ⟨32200577506190005205416471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171736413366346694428887845 32200577506190005205416471)
        ·
          refine ⟨48300866259285007808124707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32200577506190005205416471 48300866259285007808124707)
          ·
            refine ⟨72451299388927511712187061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48300866259285007808124707 72451299388927511712187061)
            ·
              refine ⟨6792309317711954223017537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72451299388927511712187061 6792309317711954223017537)
              ·
                refine ⟨5094231988283965667263153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792309317711954223017537 5094231988283965667263153)
                ·
                  refine ⟨3820673991212974250447365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094231988283965667263153 3820673991212974250447365)
                  ·
                    refine ⟨716376373352432671958881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820673991212974250447365 716376373352432671958881)
                    ·
                      rfl

theorem cell22_2092707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_2092707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092707 prefixEnd_2092707 := by exact prefixLift 2092707
  have htrace : WordTrace (prefixWord ++ tailWord_2092707) baseStart_2092707 baseEnd_2092707 := by
    simpa [prefixWord, tailWord_2092707, baseEnd_2092707] using wordTrace_append hprefix tailTrace_2092707
  have hstable : (prefixWord ++ tailWord_2092707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092707).length < 2 ^ (prefixWord ++ tailWord_2092707).sum := by decide
  have hdescent : baseEnd_2092707 < baseStart_2092707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092788 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2092788 : Nat := 118140960795 + 2092788 * 2 ^ 59
def prefixEnd_2092788 : Nat := 4983230072969 + 3 ^ 40 * 2092788 * 2
def baseEnd_2092788 : Nat := 716404101307775460683633

theorem tailTrace_2092788 : CollatzResearch.WordTrace tailWord_2092788 prefixEnd_2092788 716404101307775460683633 := by
  unfold tailWord_2092788
  simp only [CollatzResearch.WordTrace]
  refine ⟨38165124571096985289935509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50886832761462647053247345 38165124571096985289935509)
  ·
    refine ⟨1788990214270171185465727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38165124571096985289935509 1788990214270171185465727)
    ·
      refine ⟨2683485321405256778198591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788990214270171185465727 2683485321405256778198591)
      ·
        refine ⟨4025227982107885167297887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683485321405256778198591 4025227982107885167297887)
        ·
          refine ⟨6037841973161827750946831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025227982107885167297887 6037841973161827750946831)
          ·
            refine ⟨9056762959742741626420247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037841973161827750946831 9056762959742741626420247)
            ·
              refine ⟨13585144439614112439630371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056762959742741626420247 13585144439614112439630371)
              ·
                refine ⟨20377716659421168659445557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13585144439614112439630371 20377716659421168659445557)
                ·
                  refine ⟨1910410936820734561823021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20377716659421168659445557 1910410936820734561823021)
                  ·
                    refine ⟨716404101307775460683633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910410936820734561823021 716404101307775460683633)
                    ·
                      rfl

theorem cell22_2092788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2092788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092788 prefixEnd_2092788 := by exact prefixLift 2092788
  have htrace : WordTrace (prefixWord ++ tailWord_2092788) baseStart_2092788 baseEnd_2092788 := by
    simpa [prefixWord, tailWord_2092788, baseEnd_2092788] using wordTrace_append hprefix tailTrace_2092788
  have hstable : (prefixWord ++ tailWord_2092788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092788).length < 2 ^ (prefixWord ++ tailWord_2092788).sum := by decide
  have hdescent : baseEnd_2092788 < baseStart_2092788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092818 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_2092818 : Nat := 118140960795 + 2092818 * 2 ^ 59
def prefixEnd_2092818 : Nat := 4983230072969 + 3 ^ 40 * 2092818 * 2
def baseEnd_2092818 : Nat := 238804790306955127477847

theorem tailTrace_2092818 : CollatzResearch.WordTrace tailWord_2092818 prefixEnd_2092818 238804790306955127477847 := by
  unfold tailWord_2092818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19082835833021321425865777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50887562221390190468975405 19082835833021321425865777)
  ·
    refine ⟨14312126874765991069399333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19082835833021321425865777 14312126874765991069399333)
    ·
      refine ⟨2683523789018623325512375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14312126874765991069399333 2683523789018623325512375)
      ·
        refine ⟨4025285683527934988268563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683523789018623325512375 4025285683527934988268563)
        ·
          refine ⟨6037928525291902482402845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025285683527934988268563 6037928525291902482402845)
          ·
            refine ⟨2264223196984463430901067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6037928525291902482402845 2264223196984463430901067)
            ·
              refine ⟨3396334795476695146351601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264223196984463430901067 3396334795476695146351601)
              ·
                refine ⟨2547251096607521359763701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396334795476695146351601 2547251096607521359763701)
                ·
                  refine ⟨238804790306955127477847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2547251096607521359763701 238804790306955127477847)
                  ·
                    rfl

theorem cell22_2092818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_2092818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092818 prefixEnd_2092818 := by exact prefixLift 2092818
  have htrace : WordTrace (prefixWord ++ tailWord_2092818) baseStart_2092818 baseEnd_2092818 := by
    simpa [prefixWord, tailWord_2092818, baseEnd_2092818] using wordTrace_append hprefix tailTrace_2092818
  have hstable : (prefixWord ++ tailWord_2092818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092818).length < 2 ^ (prefixWord ++ tailWord_2092818).sum := by decide
  have hdescent : baseEnd_2092818 < baseStart_2092818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092844 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_2092844 : Nat := 118140960795 + 2092844 * 2 ^ 59
def prefixEnd_2092844 : Nat := 4983230072969 + 3 ^ 40 * 2092844 * 2
def baseEnd_2092844 : Nat := 716423271252209981283461

theorem tailTrace_2092844 : CollatzResearch.WordTrace tailWord_2092844 prefixEnd_2092844 716423271252209981283461 := by
  unfold tailWord_2092844
  simp only [CollatzResearch.WordTrace]
  refine ⟨38166145814995546071954793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50888194419994061429273057 38166145814995546071954793)
  ·
    refine ⟨28624609361246659553966095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38166145814995546071954793 28624609361246659553966095)
    ·
      refine ⟨42936914041869989330949143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28624609361246659553966095 42936914041869989330949143)
      ·
        refine ⟨64405371062804983996423715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42936914041869989330949143 64405371062804983996423715)
        ·
          refine ⟨96608056594207475994635573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64405371062804983996423715 96608056594207475994635573)
          ·
            refine ⟨9057005305706950874497085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96608056594207475994635573 9057005305706950874497085)
            ·
              refine ⟨3396376989640106577936407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9057005305706950874497085 3396376989640106577936407)
              ·
                refine ⟨5094565484460159866904611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396376989640106577936407 5094565484460159866904611)
                ·
                  refine ⟨7641848226690239800356917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094565484460159866904611 7641848226690239800356917)
                  ·
                    refine ⟨716423271252209981283461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7641848226690239800356917 716423271252209981283461)
                    ·
                      rfl

theorem cell22_2092844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_2092844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092844 prefixEnd_2092844 := by exact prefixLift 2092844
  have htrace : WordTrace (prefixWord ++ tailWord_2092844) baseStart_2092844 baseEnd_2092844 := by
    simpa [prefixWord, tailWord_2092844, baseEnd_2092844] using wordTrace_append hprefix tailTrace_2092844
  have hstable : (prefixWord ++ tailWord_2092844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092844).length < 2 ^ (prefixWord ++ tailWord_2092844).sum := by decide
  have hdescent : baseEnd_2092844 < baseStart_2092844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092861 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_2092861 : Nat := 118140960795 + 2092861 * 2 ^ 59
def prefixEnd_2092861 : Nat := 4983230072969 + 3 ^ 40 * 2092861 * 2
def baseEnd_2092861 : Nat := 716429090699627603608409

theorem tailTrace_2092861 : CollatzResearch.WordTrace tailWord_2092861 prefixEnd_2092861 716429090699627603608409 := by
  unfold tailWord_2092861
  simp only [CollatzResearch.WordTrace]
  refine ⟨76332911670929504047278437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50888607780619669364852291 76332911670929504047278437)
  ·
    refine ⟨14312420938299282008864707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76332911670929504047278437 14312420938299282008864707)
    ·
      refine ⟨21468631407448923013297061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14312420938299282008864707 21468631407448923013297061)
      ·
        refine ⟨4025368388896673064993199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21468631407448923013297061 4025368388896673064993199)
        ·
          refine ⟨6038052583345009597489799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025368388896673064993199 6038052583345009597489799)
          ·
            refine ⟨9057078875017514396234699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038052583345009597489799 9057078875017514396234699)
            ·
              refine ⟨13585618312526271594352049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057078875017514396234699 13585618312526271594352049)
              ·
                refine ⟨10189213734394703695764037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13585618312526271594352049 10189213734394703695764037)
                ·
                  refine ⟨1910477575199006942955757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10189213734394703695764037 1910477575199006942955757)
                  ·
                    refine ⟨716429090699627603608409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910477575199006942955757 716429090699627603608409)
                    ·
                      rfl

theorem cell22_2092861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_2092861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092861 prefixEnd_2092861 := by exact prefixLift 2092861
  have htrace : WordTrace (prefixWord ++ tailWord_2092861) baseStart_2092861 baseEnd_2092861 := by
    simpa [prefixWord, tailWord_2092861, baseEnd_2092861] using wordTrace_append hprefix tailTrace_2092861
  have hstable : (prefixWord ++ tailWord_2092861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092861).length < 2 ^ (prefixWord ++ tailWord_2092861).sum := by decide
  have hdescent : baseEnd_2092861 < baseStart_2092861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092863 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 4]
def baseStart_2092863 : Nat := 118140960795 + 2092863 * 2 ^ 59
def prefixEnd_2092863 : Nat := 4983230072969 + 3 ^ 40 * 2092863 * 2
def baseEnd_2092863 : Nat := 238809925113500088352801

theorem tailTrace_2092863 : CollatzResearch.WordTrace tailWord_2092863 prefixEnd_2092863 238809925113500088352801 := by
  unfold tailWord_2092863
  simp only [CollatzResearch.WordTrace]
  refine ⟨76332984616922258388851243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50888656411281505592567495 76332984616922258388851243)
  ·
    refine ⟨114499476925383387583276865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76332984616922258388851243 114499476925383387583276865)
    ·
      refine ⟨85874607694037540687457649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114499476925383387583276865 85874607694037540687457649)
      ·
        refine ⟨64405955770528155515593237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85874607694037540687457649 64405955770528155515593237)
        ·
          refine ⟨3019029176743507289793433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64405955770528155515593237 3019029176743507289793433)
          ·
            refine ⟨2264271882557630467345075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3019029176743507289793433 2264271882557630467345075)
            ·
              refine ⟨3396407823836445701017613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264271882557630467345075 3396407823836445701017613)
              ·
                refine ⟨1273652933938667137881605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396407823836445701017613 1273652933938667137881605)
                ·
                  refine ⟨238809925113500088352801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273652933938667137881605 238809925113500088352801)
                  ·
                    rfl

theorem cell22_2092863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 4].length) (baseStart_2092863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092863 prefixEnd_2092863 := by exact prefixLift 2092863
  have htrace : WordTrace (prefixWord ++ tailWord_2092863) baseStart_2092863 baseEnd_2092863 := by
    simpa [prefixWord, tailWord_2092863, baseEnd_2092863] using wordTrace_append hprefix tailTrace_2092863
  have hstable : (prefixWord ++ tailWord_2092863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092863).length < 2 ^ (prefixWord ++ tailWord_2092863).sum := by decide
  have hdescent : baseEnd_2092863 < baseStart_2092863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092876 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_2092876 : Nat := 118140960795 + 2092876 * 2 ^ 59
def prefixEnd_2092876 : Nat := 4983230072969 + 3 ^ 40 * 2092876 * 2
def baseEnd_2092876 : Nat := 716434225506172564483363

theorem tailTrace_2092876 : CollatzResearch.WordTrace tailWord_2092876 prefixEnd_2092876 716434225506172564483363 := by
  unfold tailWord_2092876
  simp only [CollatzResearch.WordTrace]
  refine ⟨38166729382937580804537241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50888972510583441072716321 38166729382937580804537241)
  ·
    refine ⟨28625047037203185603402931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38166729382937580804537241 28625047037203185603402931)
    ·
      refine ⟨42937570555804778405104397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28625047037203185603402931 42937570555804778405104397)
      ·
        refine ⟨16101588958426791901914149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42937570555804778405104397 16101588958426791901914149)
        ·
          refine ⟨3019047929705023481608903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16101588958426791901914149 3019047929705023481608903)
          ·
            refine ⟨4528571894557535222413355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019047929705023481608903 4528571894557535222413355)
            ·
              refine ⟨6792857841836302833620033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528571894557535222413355 6792857841836302833620033)
              ·
                refine ⟨5094643381377227125215025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792857841836302833620033 5094643381377227125215025)
                ·
                  refine ⟨3820982536032920343911269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094643381377227125215025 3820982536032920343911269)
                  ·
                    refine ⟨716434225506172564483363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820982536032920343911269 716434225506172564483363)
                    ·
                      rfl

theorem cell22_2092876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_2092876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092876 prefixEnd_2092876 := by exact prefixLift 2092876
  have htrace : WordTrace (prefixWord ++ tailWord_2092876) baseStart_2092876 baseEnd_2092876 := by
    simpa [prefixWord, tailWord_2092876, baseEnd_2092876] using wordTrace_append hprefix tailTrace_2092876
  have hstable : (prefixWord ++ tailWord_2092876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092876).length < 2 ^ (prefixWord ++ tailWord_2092876).sum := by decide
  have hdescent : baseEnd_2092876 < baseStart_2092876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092949 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2092949 : Nat := 118140960795 + 2092949 * 2 ^ 59
def prefixEnd_2092949 : Nat := 4983230072969 + 3 ^ 40 * 2092949 * 2
def baseEnd_2092949 : Nat := 716459214898024707408139

theorem tailTrace_2092949 : CollatzResearch.WordTrace tailWord_2092949 prefixEnd_2092949 716459214898024707408139 := by
  unfold tailWord_2092949
  simp only [CollatzResearch.WordTrace]
  refine ⟨76336121294610695076481901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50890747529740463384321267 76336121294610695076481901)
  ·
    refine ⟨28626045485479010653680713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76336121294610695076481901 28626045485479010653680713)
    ·
      refine ⟨21469534114109257990260535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28626045485479010653680713 21469534114109257990260535)
      ·
        refine ⟨32204301171163886985390803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21469534114109257990260535 32204301171163886985390803)
        ·
          refine ⟨48306451756745830478086205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32204301171163886985390803 48306451756745830478086205)
          ·
            refine ⟨18114919408779686429282327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48306451756745830478086205 18114919408779686429282327)
            ·
              refine ⟨27172379113169529643923491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18114919408779686429282327 27172379113169529643923491)
              ·
                refine ⟨40758568669754294465885237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27172379113169529643923491 40758568669754294465885237)
                ·
                  refine ⟨3821115812789465106176741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40758568669754294465885237 3821115812789465106176741)
                  ·
                    refine ⟨716459214898024707408139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3821115812789465106176741 716459214898024707408139)
                    ·
                      rfl

theorem cell22_2092949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2092949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092949 prefixEnd_2092949 := by exact prefixLift 2092949
  have htrace : WordTrace (prefixWord ++ tailWord_2092949) baseStart_2092949 baseEnd_2092949 := by
    simpa [prefixWord, tailWord_2092949, baseEnd_2092949] using wordTrace_append hprefix tailTrace_2092949
  have hstable : (prefixWord ++ tailWord_2092949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092949).length < 2 ^ (prefixWord ++ tailWord_2092949).sum := by decide
  have hdescent : baseEnd_2092949 < baseStart_2092949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092964 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_2092964 : Nat := 118140960795 + 2092964 * 2 ^ 59
def prefixEnd_2092964 : Nat := 4983230072969 + 3 ^ 40 * 2092964 * 2
def baseEnd_2092964 : Nat := 238821449901523222761031

theorem tailTrace_2092964 : CollatzResearch.WordTrace tailWord_2092964 prefixEnd_2092964 238821449901523222761031 := by
  unfold tailWord_2092964
  simp only [CollatzResearch.WordTrace]
  refine ⟨38168334194778176319138973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50891112259704235092185297 38168334194778176319138973)
  ·
    refine ⟨14313125323041816119677115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38168334194778176319138973 14313125323041816119677115)
    ·
      refine ⟨21469687984562724179515673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14313125323041816119677115 21469687984562724179515673)
      ·
        refine ⟨16102265988422043134636755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21469687984562724179515673 16102265988422043134636755)
        ·
          refine ⟨24153398982633064701955133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16102265988422043134636755 24153398982633064701955133)
          ·
            refine ⟨9057524618487399263233175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24153398982633064701955133 9057524618487399263233175)
            ·
              refine ⟨13586286927731098894849763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057524618487399263233175 13586286927731098894849763)
              ·
                refine ⟨20379430391596648342274645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13586286927731098894849763 20379430391596648342274645)
                ·
                  refine ⟨238821449901523222761031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20379430391596648342274645 238821449901523222761031)
                  ·
                    rfl

theorem cell22_2092964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_2092964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092964 prefixEnd_2092964 := by exact prefixLift 2092964
  have htrace : WordTrace (prefixWord ++ tailWord_2092964) baseStart_2092964 baseEnd_2092964 := by
    simpa [prefixWord, tailWord_2092964, baseEnd_2092964] using wordTrace_append hprefix tailTrace_2092964
  have hstable : (prefixWord ++ tailWord_2092964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092964).length < 2 ^ (prefixWord ++ tailWord_2092964).sum := by decide
  have hdescent : baseEnd_2092964 < baseStart_2092964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092979 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 1, 5]
def baseStart_2092979 : Nat := 118140960795 + 2092979 * 2 ^ 59
def prefixEnd_2092979 : Nat := 4983230072969 + 3 ^ 40 * 2092979 * 2
def baseEnd_2092979 : Nat := 716469484511114629158047

theorem tailTrace_2092979 : CollatzResearch.WordTrace tailWord_2092979 prefixEnd_2092979 716469484511114629158047 := by
  unfold tailWord_2092979
  simp only [CollatzResearch.WordTrace]
  refine ⟨76337215484502010200073991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50891476989668006800049327 76337215484502010200073991)
  ·
    refine ⟨114505823226753015300110987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76337215484502010200073991 114505823226753015300110987)
    ·
      refine ⟨171758734840129522950166481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114505823226753015300110987 171758734840129522950166481)
      ·
        refine ⟨128819051130097142212624861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171758734840129522950166481 128819051130097142212624861)
        ·
          refine ⟨48307144173786428329734323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128819051130097142212624861 48307144173786428329734323)
          ·
            refine ⟨72460716260679642494601485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48307144173786428329734323 72460716260679642494601485)
            ·
              refine ⟨27172768597754865935475557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72460716260679642494601485 27172768597754865935475557)
              ·
                refine ⟨5094894112079037362901667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27172768597754865935475557 5094894112079037362901667)
                ·
                  refine ⟨7642341168118556044352501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094894112079037362901667 7642341168118556044352501)
                  ·
                    refine ⟨716469484511114629158047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7642341168118556044352501 716469484511114629158047)
                    ·
                      rfl

theorem cell22_2092979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_2092979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2092979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2092979 prefixEnd_2092979 := by exact prefixLift 2092979
  have htrace : WordTrace (prefixWord ++ tailWord_2092979) baseStart_2092979 baseEnd_2092979 := by
    simpa [prefixWord, tailWord_2092979, baseEnd_2092979] using wordTrace_append hprefix tailTrace_2092979
  have hstable : (prefixWord ++ tailWord_2092979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092979).length < 2 ^ (prefixWord ++ tailWord_2092979).sum := by decide
  have hdescent : baseEnd_2092979 < baseStart_2092979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093013 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_2093013 : Nat := 118140960795 + 2093013 * 2 ^ 59
def prefixEnd_2093013 : Nat := 4983230072969 + 3 ^ 40 * 2093013 * 2
def baseEnd_2093013 : Nat := 716481123405949873807943

theorem tailTrace_2093013 : CollatzResearch.WordTrace tailWord_2093013 prefixEnd_2093013 716481123405949873807943 := by
  unfold tailWord_2093013
  simp only [CollatzResearch.WordTrace]
  refine ⟨76338455566378834006811693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50892303710919222671207795 76338455566378834006811693)
  ·
    refine ⟨28626920837392062752554385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76338455566378834006811693 28626920837392062752554385)
    ·
      refine ⟨21470190628044047064415789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28626920837392062752554385 21470190628044047064415789)
      ·
        refine ⟨8051321485516517649155921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21470190628044047064415789 8051321485516517649155921)
        ·
          refine ⟨6038491114137388236866941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8051321485516517649155921 6038491114137388236866941)
          ·
            refine ⟨2264434167801520588825103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6038491114137388236866941 2264434167801520588825103)
            ·
              refine ⟨3396651251702280883237655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264434167801520588825103 3396651251702280883237655)
              ·
                refine ⟨5094976877553421324856483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396651251702280883237655 5094976877553421324856483)
                ·
                  refine ⟨7642465316330131987284725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094976877553421324856483 7642465316330131987284725)
                  ·
                    refine ⟨716481123405949873807943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7642465316330131987284725 716481123405949873807943)
                    ·
                      rfl

theorem cell22_2093013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_2093013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093013 prefixEnd_2093013 := by exact prefixLift 2093013
  have htrace : WordTrace (prefixWord ++ tailWord_2093013) baseStart_2093013 baseEnd_2093013 := by
    simpa [prefixWord, tailWord_2093013, baseEnd_2093013] using wordTrace_append hprefix tailTrace_2093013
  have hstable : (prefixWord ++ tailWord_2093013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093013).length < 2 ^ (prefixWord ++ tailWord_2093013).sum := by decide
  have hdescent : baseEnd_2093013 < baseStart_2093013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093099 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 10]
def baseStart_2093099 : Nat := 118140960795 + 2093099 * 2 ^ 59
def prefixEnd_2093099 : Nat := 4983230072969 + 3 ^ 40 * 2093099 * 2
def baseEnd_2093099 : Nat := 238836854321158105385893

theorem tailTrace_2093099 : CollatzResearch.WordTrace tailWord_2093099 prefixEnd_2093099 238836854321158105385893 := by
  unfold tailWord_2093099
  simp only [CollatzResearch.WordTrace]
  refine ⟨76341592244067270694442351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50894394829378180462961567 76341592244067270694442351)
  ·
    refine ⟨114512388366100906041663527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76341592244067270694442351 114512388366100906041663527)
    ·
      refine ⟨171768582549151359062495291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114512388366100906041663527 171768582549151359062495291)
      ·
        refine ⟨257652873823727038593742937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171768582549151359062495291 257652873823727038593742937)
        ·
          refine ⟨193239655367795278945307203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257652873823727038593742937 193239655367795278945307203)
          ·
            refine ⟨289859483051692918417960805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193239655367795278945307203 289859483051692918417960805)
            ·
              refine ⟨54348653072192422203367651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289859483051692918417960805 54348653072192422203367651)
              ·
                refine ⟨81522979608288633305051477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54348653072192422203367651 81522979608288633305051477)
                ·
                  refine ⟨238836854321158105385893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 81522979608288633305051477 238836854321158105385893)
                  ·
                    rfl

theorem cell22_2093099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_2093099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093099 prefixEnd_2093099 := by exact prefixLift 2093099
  have htrace : WordTrace (prefixWord ++ tailWord_2093099) baseStart_2093099 baseEnd_2093099 := by
    simpa [prefixWord, tailWord_2093099, baseEnd_2093099] using wordTrace_append hprefix tailTrace_2093099
  have hstable : (prefixWord ++ tailWord_2093099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093099).length < 2 ^ (prefixWord ++ tailWord_2093099).sum := by decide
  have hdescent : baseEnd_2093099 < baseStart_2093099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093116 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_2093116 : Nat := 118140960795 + 2093116 * 2 ^ 59
def prefixEnd_2093116 : Nat := 4983230072969 + 3 ^ 40 * 2093116 * 2
def baseEnd_2093116 : Nat := 238838794136963979494209

theorem tailTrace_2093116 : CollatzResearch.WordTrace tailWord_2093116 prefixEnd_2093116 238838794136963979494209 := by
  unfold tailWord_2093116
  simp only [CollatzResearch.WordTrace]
  refine ⟨38171106142502841298905601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50894808190003788398540801 38171106142502841298905601)
  ·
    refine ⟨28628329606877130974179201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38171106142502841298905601 28628329606877130974179201)
    ·
      refine ⟨21471247205157848230634401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28628329606877130974179201 21471247205157848230634401)
      ·
        refine ⟨16103435403868386172975801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21471247205157848230634401 16103435403868386172975801)
        ·
          refine ⟨12077576552901289629731851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16103435403868386172975801 12077576552901289629731851)
          ·
            refine ⟨18116364829351934444597777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077576552901289629731851 18116364829351934444597777)
            ·
              refine ⟨13587273622013950833448333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18116364829351934444597777 13587273622013950833448333)
              ·
                refine ⟨5095227608255231562543125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13587273622013950833448333 5095227608255231562543125)
                ·
                  refine ⟨238838794136963979494209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5095227608255231562543125 238838794136963979494209)
                  ·
                    rfl

theorem cell22_2093116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_2093116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093116 prefixEnd_2093116 := by exact prefixLift 2093116
  have htrace : WordTrace (prefixWord ++ tailWord_2093116) baseStart_2093116 baseEnd_2093116 := by
    simpa [prefixWord, tailWord_2093116, baseEnd_2093116] using wordTrace_append hprefix tailTrace_2093116
  have hstable : (prefixWord ++ tailWord_2093116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093116).length < 2 ^ (prefixWord ++ tailWord_2093116).sum := by decide
  have hdescent : baseEnd_2093116 < baseStart_2093116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093133 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2093133 : Nat := 118140960795 + 2093133 * 2 ^ 59
def prefixEnd_2093133 : Nat := 4983230072969 + 3 ^ 40 * 2093133 * 2
def baseEnd_2093133 : Nat := 238840733952769853602525

theorem tailTrace_2093133 : CollatzResearch.WordTrace tailWord_2093133 prefixEnd_2093133 238840733952769853602525 := by
  unfold tailWord_2093133
  simp only [CollatzResearch.WordTrace]
  refine ⟨76342832325944094501180053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50895221550629396334120035 76342832325944094501180053)
  ·
    refine ⟨3578570265278629429742815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76342832325944094501180053 3578570265278629429742815)
    ·
      refine ⟨5367855397917944144614223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578570265278629429742815 5367855397917944144614223)
      ·
        refine ⟨8051783096876916216921335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367855397917944144614223 8051783096876916216921335)
        ·
          refine ⟨12077674645315374325382003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051783096876916216921335 12077674645315374325382003)
          ·
            refine ⟨18116511967973061488073005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077674645315374325382003 18116511967973061488073005)
            ·
              refine ⟨6793691987989898058027377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18116511967973061488073005 6793691987989898058027377)
              ·
                refine ⟨5095268990992423543520533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793691987989898058027377 5095268990992423543520533)
                ·
                  refine ⟨238840733952769853602525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5095268990992423543520533 238840733952769853602525)
                  ·
                    rfl

theorem cell22_2093133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2093133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093133 prefixEnd_2093133 := by exact prefixLift 2093133
  have htrace : WordTrace (prefixWord ++ tailWord_2093133) baseStart_2093133 baseEnd_2093133 := by
    simpa [prefixWord, tailWord_2093133, baseEnd_2093133] using wordTrace_append hprefix tailTrace_2093133
  have hstable : (prefixWord ++ tailWord_2093133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093133).length < 2 ^ (prefixWord ++ tailWord_2093133).sum := by decide
  have hdescent : baseEnd_2093133 < baseStart_2093133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093146 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_2093146 : Nat := 118140960795 + 2093146 * 2 ^ 59
def prefixEnd_2093146 : Nat := 4983230072969 + 3 ^ 40 * 2093146 * 2
def baseEnd_2093146 : Nat := 716526652023981860232535

theorem tailTrace_2093146 : CollatzResearch.WordTrace tailWord_2093146 prefixEnd_2093146 716526652023981860232535 := by
  unfold tailWord_2093146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19085826618724249430350823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50895537649931331814268861 19085826618724249430350823)
  ·
    refine ⟨28628739928086374145526235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19085826618724249430350823 28628739928086374145526235)
    ·
      refine ⟨42943109892129561218289353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28628739928086374145526235 42943109892129561218289353)
      ·
        refine ⟨32207332419097170913717015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42943109892129561218289353 32207332419097170913717015)
        ·
          refine ⟨48310998628645756370575523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32207332419097170913717015 48310998628645756370575523)
          ·
            refine ⟨72466497942968634555863285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48310998628645756370575523 72466497942968634555863285)
            ·
              refine ⟨6793734182153309489612183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72466497942968634555863285 6793734182153309489612183)
              ·
                refine ⟨10190601273229964234418275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793734182153309489612183 10190601273229964234418275)
                ·
                  refine ⟨15285901909844946351627413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10190601273229964234418275 15285901909844946351627413)
                  ·
                    refine ⟨716526652023981860232535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15285901909844946351627413 716526652023981860232535)
                    ·
                      rfl

theorem cell22_2093146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_2093146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093146 prefixEnd_2093146 := by exact prefixLift 2093146
  have htrace : WordTrace (prefixWord ++ tailWord_2093146) baseStart_2093146 baseEnd_2093146 := by
    simpa [prefixWord, tailWord_2093146, baseEnd_2093146] using wordTrace_append hprefix tailTrace_2093146
  have hstable : (prefixWord ++ tailWord_2093146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093146).length < 2 ^ (prefixWord ++ tailWord_2093146).sum := by decide
  have hdescent : baseEnd_2093146 < baseStart_2093146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093148 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2093148 : Nat := 118140960795 + 2093148 * 2 ^ 59
def prefixEnd_2093148 : Nat := 4983230072969 + 3 ^ 40 * 2093148 * 2
def baseEnd_2093148 : Nat := 716527336664854521682529

theorem tailTrace_2093148 : CollatzResearch.WordTrace tailWord_2093148 prefixEnd_2093148 716527336664854521682529 := by
  unfold tailWord_2093148
  simp only [CollatzResearch.WordTrace]
  refine ⟨38171689710444876031488049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50895586280593168041984065 38171689710444876031488049)
  ·
    refine ⟨28628767282833657023616037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38171689710444876031488049 28628767282833657023616037)
    ·
      refine ⟨5367893865531310691928007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28628767282833657023616037 5367893865531310691928007)
      ·
        refine ⟨8051840798296966037892011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367893865531310691928007 8051840798296966037892011)
        ·
          refine ⟨12077761197445449056838017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051840798296966037892011 12077761197445449056838017)
          ·
            refine ⟨9058320898084086792628513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12077761197445449056838017 9058320898084086792628513)
            ·
              refine ⟨6793740673563065094471385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9058320898084086792628513 6793740673563065094471385)
              ·
                refine ⟨5095305505172298820853539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793740673563065094471385 5095305505172298820853539)
                ·
                  refine ⟨7642958257758448231280309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095305505172298820853539 7642958257758448231280309)
                  ·
                    refine ⟨716527336664854521682529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7642958257758448231280309 716527336664854521682529)
                    ·
                      rfl

theorem cell22_2093148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2093148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093148 prefixEnd_2093148 := by exact prefixLift 2093148
  have htrace : WordTrace (prefixWord ++ tailWord_2093148) baseStart_2093148 baseEnd_2093148 := by
    simpa [prefixWord, tailWord_2093148, baseEnd_2093148] using wordTrace_append hprefix tailTrace_2093148
  have hstable : (prefixWord ++ tailWord_2093148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093148).length < 2 ^ (prefixWord ++ tailWord_2093148).sum := by decide
  have hdescent : baseEnd_2093148 < baseStart_2093148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093191 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2093191 : Nat := 118140960795 + 2093191 * 2 ^ 59
def prefixEnd_2093191 : Nat := 4983230072969 + 3 ^ 40 * 2093191 * 2
def baseEnd_2093191 : Nat := 716542056443616742857397

theorem tailTrace_2093191 : CollatzResearch.WordTrace tailWord_2093191 prefixEnd_2093191 716542056443616742857397 := by
  unfold tailWord_2093191
  simp only [CollatzResearch.WordTrace]
  refine ⟨76344947759733970406791427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50896631839822646937860951 76344947759733970406791427)
  ·
    refine ⟨114517421639600955610187141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76344947759733970406791427 114517421639600955610187141)
    ·
      refine ⟨21472016557425179176910089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114517421639600955610187141 21472016557425179176910089)
      ·
        refine ⟨16104012418068884382682567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21472016557425179176910089 16104012418068884382682567)
        ·
          refine ⟨24156018627103326574023851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16104012418068884382682567 24156018627103326574023851)
          ·
            refine ⟨36234027940654989861035777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24156018627103326574023851 36234027940654989861035777)
            ·
              refine ⟨27175520955491242395776833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36234027940654989861035777 27175520955491242395776833)
              ·
                refine ⟨20381640716618431796832625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27175520955491242395776833 20381640716618431796832625)
                ·
                  refine ⟨15286230537463823847624469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20381640716618431796832625 15286230537463823847624469)
                  ·
                    refine ⟨716542056443616742857397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15286230537463823847624469 716542056443616742857397)
                    ·
                      rfl

theorem cell22_2093191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2093191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093191 prefixEnd_2093191 := by exact prefixLift 2093191
  have htrace : WordTrace (prefixWord ++ tailWord_2093191) baseStart_2093191 baseEnd_2093191 := by
    simpa [prefixWord, tailWord_2093191, baseEnd_2093191] using wordTrace_append hprefix tailTrace_2093191
  have hstable : (prefixWord ++ tailWord_2093191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093191).length < 2 ^ (prefixWord ++ tailWord_2093191).sum := by decide
  have hdescent : baseEnd_2093191 < baseStart_2093191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093193 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_2093193 : Nat := 118140960795 + 2093193 * 2 ^ 59
def prefixEnd_2093193 : Nat := 4983230072969 + 3 ^ 40 * 2093193 * 2
def baseEnd_2093193 : Nat := 716542741084489404307391

theorem tailTrace_2093193 : CollatzResearch.WordTrace tailWord_2093193 prefixEnd_2093193 716542741084489404307391 := by
  unfold tailWord_2093193
  simp only [CollatzResearch.WordTrace]
  refine ⟨76345020705726724748364233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50896680470484483165576155 76345020705726724748364233)
  ·
    refine ⟨57258765529295043561273175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76345020705726724748364233 57258765529295043561273175)
    ·
      refine ⟨85888148293942565341909763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57258765529295043561273175 85888148293942565341909763)
      ·
        refine ⟨128832222440913848012864645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85888148293942565341909763 128832222440913848012864645)
        ·
          refine ⟨24156041707671346502412121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128832222440913848012864645 24156041707671346502412121)
          ·
            refine ⟨18117031280753509876809091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24156041707671346502412121 18117031280753509876809091)
            ·
              refine ⟨27175546921130264815213637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117031280753509876809091 27175546921130264815213637)
              ·
                refine ⟨5095415047711924652852557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27175546921130264815213637 5095415047711924652852557)
                ·
                  refine ⟨1910780642891971744819709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5095415047711924652852557 1910780642891971744819709)
                  ·
                    refine ⟨716542741084489404307391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910780642891971744819709 716542741084489404307391)
                    ·
                      rfl

theorem cell22_2093193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_2093193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093193 prefixEnd_2093193 := by exact prefixLift 2093193
  have htrace : WordTrace (prefixWord ++ tailWord_2093193) baseStart_2093193 baseEnd_2093193 := by
    simpa [prefixWord, tailWord_2093193, baseEnd_2093193] using wordTrace_append hprefix tailTrace_2093193
  have hstable : (prefixWord ++ tailWord_2093193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093193).length < 2 ^ (prefixWord ++ tailWord_2093193).sum := by decide
  have hdescent : baseEnd_2093193 < baseStart_2093193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093319 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 4]
def baseStart_2093319 : Nat := 118140960795 + 2093319 * 2 ^ 59
def prefixEnd_2093319 : Nat := 4983230072969 + 3 ^ 40 * 2093319 * 2
def baseEnd_2093319 : Nat := 238861957819822358552335

theorem tailTrace_2093319 : CollatzResearch.WordTrace tailWord_2093319 prefixEnd_2093319 238861957819822358552335 := by
  unfold tailWord_2093319
  simp only [CollatzResearch.WordTrace]
  refine ⟨76349616303270248267451011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50899744202180165511634007 76349616303270248267451011)
  ·
    refine ⟨114524424454905372401176517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76349616303270248267451011 114524424454905372401176517)
    ·
      refine ⟨21473329585294757325220597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114524424454905372401176517 21473329585294757325220597)
      ·
        refine ⟨2013124648621383499239431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21473329585294757325220597 2013124648621383499239431)
        ·
          refine ⟨3019686972932075248859147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013124648621383499239431 3019686972932075248859147)
          ·
            refine ⟨4529530459398112873288721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019686972932075248859147 4529530459398112873288721)
            ·
              refine ⟨3397147844548584654966541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529530459398112873288721 3397147844548584654966541)
              ·
                refine ⟨1273930441705719245612453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3397147844548584654966541 1273930441705719245612453)
                ·
                  refine ⟨238861957819822358552335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273930441705719245612453 238861957819822358552335)
                  ·
                    rfl

theorem cell22_2093319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 4].length) (baseStart_2093319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093319 prefixEnd_2093319 := by exact prefixLift 2093319
  have htrace : WordTrace (prefixWord ++ tailWord_2093319) baseStart_2093319 baseEnd_2093319 := by
    simpa [prefixWord, tailWord_2093319, baseEnd_2093319] using wordTrace_append hprefix tailTrace_2093319
  have hstable : (prefixWord ++ tailWord_2093319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093319).length < 2 ^ (prefixWord ++ tailWord_2093319).sum := by decide
  have hdescent : baseEnd_2093319 < baseStart_2093319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093345 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_2093345 : Nat := 118140960795 + 2093345 * 2 ^ 59
def prefixEnd_2093345 : Nat := 4983230072969 + 3 ^ 40 * 2093345 * 2
def baseEnd_2093345 : Nat := 716594773790811674506925

theorem tailTrace_2093345 : CollatzResearch.WordTrace tailWord_2093345 prefixEnd_2093345 716594773790811674506925 := by
  unfold tailWord_2093345
  simp only [CollatzResearch.WordTrace]
  refine ⟨76350564601176054707897489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50900376400784036471931659 76350564601176054707897489)
  ·
    refine ⟨57262923450882041030923117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76350564601176054707897489 57262923450882041030923117)
    ·
      refine ⟨21473596294080765386596169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57262923450882041030923117 21473596294080765386596169)
      ·
        refine ⟨16105197220560574039947127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21473596294080765386596169 16105197220560574039947127)
        ·
          refine ⟨24157795830840861059920691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105197220560574039947127 24157795830840861059920691)
          ·
            refine ⟨36236693746261291589881037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24157795830840861059920691 36236693746261291589881037)
            ·
              refine ⟨13588760154847984346205389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36236693746261291589881037 13588760154847984346205389)
              ·
                refine ⟨5095785058067994129827021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13588760154847984346205389 5095785058067994129827021)
                ·
                  refine ⟨1910919396775497798685133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5095785058067994129827021 1910919396775497798685133)
                  ·
                    refine ⟨716594773790811674506925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910919396775497798685133 716594773790811674506925)
                    ·
                      rfl

theorem cell22_2093345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_2093345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093345 prefixEnd_2093345 := by exact prefixLift 2093345
  have htrace : WordTrace (prefixWord ++ tailWord_2093345) baseStart_2093345 baseEnd_2093345 := by
    simpa [prefixWord, tailWord_2093345, baseEnd_2093345] using wordTrace_append hprefix tailTrace_2093345
  have hstable : (prefixWord ++ tailWord_2093345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093345).length < 2 ^ (prefixWord ++ tailWord_2093345).sum := by decide
  have hdescent : baseEnd_2093345 < baseStart_2093345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093351 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2093351 : Nat := 118140960795 + 2093351 * 2 ^ 59
def prefixEnd_2093351 : Nat := 4983230072969 + 3 ^ 40 * 2093351 * 2
def baseEnd_2093351 : Nat := 716596827713429658856907

theorem tailTrace_2093351 : CollatzResearch.WordTrace tailWord_2093351 prefixEnd_2093351 716596827713429658856907 := by
  unfold tailWord_2093351
  simp only [CollatzResearch.WordTrace]
  refine ⟨76350783439154317732615907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50900522292769545155077271 76350783439154317732615907)
  ·
    refine ⟨114526175158731476598923861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76350783439154317732615907 114526175158731476598923861)
    ·
      refine ⟨1342103615141384491393639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 114526175158731476598923861 1342103615141384491393639)
      ·
        refine ⟨2013155422712076737090459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342103615141384491393639 2013155422712076737090459)
        ·
          refine ⟨3019733134068115105635689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013155422712076737090459 3019733134068115105635689)
          ·
            refine ⟨2264799850551086329226767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3019733134068115105635689 2264799850551086329226767)
            ·
              refine ⟨3397199775826629493840151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264799850551086329226767 3397199775826629493840151)
              ·
                refine ⟨5095799663739944240760227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397199775826629493840151 5095799663739944240760227)
                ·
                  refine ⟨7643699495609916361140341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095799663739944240760227 7643699495609916361140341)
                  ·
                    refine ⟨716596827713429658856907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7643699495609916361140341 716596827713429658856907)
                    ·
                      rfl

theorem cell22_2093351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2093351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093351 prefixEnd_2093351 := by exact prefixLift 2093351
  have htrace : WordTrace (prefixWord ++ tailWord_2093351) baseStart_2093351 baseEnd_2093351 := by
    simpa [prefixWord, tailWord_2093351, baseEnd_2093351] using wordTrace_append hprefix tailTrace_2093351
  have hstable : (prefixWord ++ tailWord_2093351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093351).length < 2 ^ (prefixWord ++ tailWord_2093351).sum := by decide
  have hdescent : baseEnd_2093351 < baseStart_2093351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093396 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2093396 : Nat := 118140960795 + 2093396 * 2 ^ 59
def prefixEnd_2093396 : Nat := 4983230072969 + 3 ^ 40 * 2093396 * 2
def baseEnd_2093396 : Nat := 716612232133064541481769

theorem tailTrace_2093396 : CollatzResearch.WordTrace tailWord_2093396 prefixEnd_2093396 716612232133064541481769 := by
  unfold tailWord_2093396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38176212361995645209002021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50901616482660860278669361 38176212361995645209002021)
  ·
    refine ⟨7158039817874183476687879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38176212361995645209002021 7158039817874183476687879)
    ·
      refine ⟨10737059726811275215031819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158039817874183476687879 10737059726811275215031819)
      ·
        refine ⟨16105589590216912822547729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10737059726811275215031819 16105589590216912822547729)
        ·
          refine ⟨12079192192662684616910797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16105589590216912822547729 12079192192662684616910797)
          ·
            refine ⟨4529697072248506731341549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12079192192662684616910797 4529697072248506731341549)
            ·
              refine ⟨1698636402093190024253081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4529697072248506731341549 1698636402093190024253081)
              ·
                refine ⟨1273977301569892518189811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698636402093190024253081 1273977301569892518189811)
                ·
                  refine ⟨1910965952354838777284717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273977301569892518189811 1910965952354838777284717)
                  ·
                    refine ⟨716612232133064541481769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910965952354838777284717 716612232133064541481769)
                    ·
                      rfl

theorem cell22_2093396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2093396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093396 prefixEnd_2093396 := by exact prefixLift 2093396
  have htrace : WordTrace (prefixWord ++ tailWord_2093396) baseStart_2093396 baseEnd_2093396 := by
    simpa [prefixWord, tailWord_2093396, baseEnd_2093396] using wordTrace_append hprefix tailTrace_2093396
  have hstable : (prefixWord ++ tailWord_2093396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093396).length < 2 ^ (prefixWord ++ tailWord_2093396).sum := by decide
  have hdescent : baseEnd_2093396 < baseStart_2093396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093435 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 1, 5]
def baseStart_2093435 : Nat := 118140960795 + 2093435 * 2 ^ 59
def prefixEnd_2093435 : Nat := 4983230072969 + 3 ^ 40 * 2093435 * 2
def baseEnd_2093435 : Nat := 716625582630081439756649

theorem tailTrace_2093435 : CollatzResearch.WordTrace tailWord_2093435 prefixEnd_2093435 716625582630081439756649 := by
  unfold tailWord_2093435
  simp only [CollatzResearch.WordTrace]
  refine ⟨76353847170850000078673759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50902564780566666719115839 76353847170850000078673759)
  ·
    refine ⟨114530770756275000118010639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76353847170850000078673759 114530770756275000118010639)
    ·
      refine ⟨171796156134412500177015959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114530770756275000118010639 171796156134412500177015959)
      ·
        refine ⟨257694234201618750265523939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171796156134412500177015959 257694234201618750265523939)
        ·
          refine ⟨386541351302428125398285909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257694234201618750265523939 386541351302428125398285909)
          ·
            refine ⟨4529781460575329594511163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 386541351302428125398285909 4529781460575329594511163)
            ·
              refine ⟨6794672190862994391766745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529781460575329594511163 6794672190862994391766745)
              ·
                refine ⟨5096004143147245793825059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794672190862994391766745 5096004143147245793825059)
                ·
                  refine ⟨7644006214720868690737589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096004143147245793825059 7644006214720868690737589)
                  ·
                    refine ⟨716625582630081439756649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7644006214720868690737589 716625582630081439756649)
                    ·
                      rfl

theorem cell22_2093435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_2093435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093435 prefixEnd_2093435 := by exact prefixLift 2093435
  have htrace : WordTrace (prefixWord ++ tailWord_2093435) baseStart_2093435 baseEnd_2093435 := by
    simpa [prefixWord, tailWord_2093435, baseEnd_2093435] using wordTrace_append hprefix tailTrace_2093435
  have hstable : (prefixWord ++ tailWord_2093435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093435).length < 2 ^ (prefixWord ++ tailWord_2093435).sum := by decide
  have hdescent : baseEnd_2093435 < baseStart_2093435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093452 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_2093452 : Nat := 118140960795 + 2093452 * 2 ^ 59
def prefixEnd_2093452 : Nat := 4983230072969 + 3 ^ 40 * 2093452 * 2
def baseEnd_2093452 : Nat := 716631402077499062081597

theorem tailTrace_2093452 : CollatzResearch.WordTrace tailWord_2093452 prefixEnd_2093452 716631402077499062081597 := by
  unfold tailWord_2093452
  simp only [CollatzResearch.WordTrace]
  refine ⟨38177233605894205991021305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50902978141192274654695073 38177233605894205991021305)
  ·
    refine ⟨28632925204420654493265979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38177233605894205991021305 28632925204420654493265979)
    ·
      refine ⟨42949387806630981739898969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28632925204420654493265979 42949387806630981739898969)
      ·
        refine ⟨32212040854973236304924227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42949387806630981739898969 32212040854973236304924227)
        ·
          refine ⟨48318061282459854457386341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32212040854973236304924227 48318061282459854457386341)
          ·
            refine ⟨9059636490461222710759939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48318061282459854457386341 9059636490461222710759939)
            ·
              refine ⟨13589454735691834066139909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059636490461222710759939 13589454735691834066139909)
              ·
                refine ⟨2548022762942218887401233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13589454735691834066139909 2548022762942218887401233)
                ·
                  refine ⟨1911017072206664165550925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548022762942218887401233 1911017072206664165550925)
                  ·
                    refine ⟨716631402077499062081597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911017072206664165550925 716631402077499062081597)
                    ·
                      rfl

theorem cell22_2093452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_2093452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093452 prefixEnd_2093452 := by exact prefixLift 2093452
  have htrace : WordTrace (prefixWord ++ tailWord_2093452) baseStart_2093452 baseEnd_2093452 := by
    simpa [prefixWord, tailWord_2093452, baseEnd_2093452] using wordTrace_append hprefix tailTrace_2093452
  have hstable : (prefixWord ++ tailWord_2093452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093452).length < 2 ^ (prefixWord ++ tailWord_2093452).sum := by decide
  have hdescent : baseEnd_2093452 < baseStart_2093452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093454 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_2093454 : Nat := 118140960795 + 2093454 * 2 ^ 59
def prefixEnd_2093454 : Nat := 4983230072969 + 3 ^ 40 * 2093454 * 2
def baseEnd_2093454 : Nat := 238877362239457241177197

theorem tailTrace_2093454 : CollatzResearch.WordTrace tailWord_2093454 prefixEnd_2093454 238877362239457241177197 := by
  unfold tailWord_2093454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9544317519722645790451927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50903026771854110882410277 9544317519722645790451927)
  ·
    refine ⟨14316476279583968685677891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9544317519722645790451927 14316476279583968685677891)
    ·
      refine ⟨21474714419375953028516837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14316476279583968685677891 21474714419375953028516837)
      ·
        refine ⟨4026508953632991192846907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21474714419375953028516837 4026508953632991192846907)
        ·
          refine ⟨6039763430449486789270361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026508953632991192846907 6039763430449486789270361)
          ·
            refine ⟨4529822572837115091952771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039763430449486789270361 4529822572837115091952771)
            ·
              refine ⟨6794733859255672637929157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529822572837115091952771 6794733859255672637929157)
              ·
                refine ⟨1274012598610438619611717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6794733859255672637929157 1274012598610438619611717)
                ·
                  refine ⟨238877362239457241177197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274012598610438619611717 238877362239457241177197)
                  ·
                    rfl

theorem cell22_2093454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_2093454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093454 prefixEnd_2093454 := by exact prefixLift 2093454
  have htrace : WordTrace (prefixWord ++ tailWord_2093454) baseStart_2093454 baseEnd_2093454 := by
    simpa [prefixWord, tailWord_2093454, baseEnd_2093454] using wordTrace_append hprefix tailTrace_2093454
  have hstable : (prefixWord ++ tailWord_2093454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093454).length < 2 ^ (prefixWord ++ tailWord_2093454).sum := by decide
  have hdescent : baseEnd_2093454 < baseStart_2093454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093514 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_2093514 : Nat := 118140960795 + 2093514 * 2 ^ 59
def prefixEnd_2093514 : Nat := 4983230072969 + 3 ^ 40 * 2093514 * 2
def baseEnd_2093514 : Nat := 716652625944551567031407

theorem tailTrace_2093514 : CollatzResearch.WordTrace tailWord_2093514 prefixEnd_2093514 716652625944551567031407 := by
  unfold tailWord_2093514
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089182134390949142699899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50904485691709197713866397 19089182134390949142699899)
  ·
    refine ⟨28633773201586423714049849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19089182134390949142699899 28633773201586423714049849)
    ·
      refine ⟨21475329901189817785537387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28633773201586423714049849 21475329901189817785537387)
      ·
        refine ⟨32212994851784726678306081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21475329901189817785537387 32212994851784726678306081)
        ·
          refine ⟨24159746138838545008729561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32212994851784726678306081 24159746138838545008729561)
          ·
            refine ⟨18119809604128908756547171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24159746138838545008729561 18119809604128908756547171)
            ·
              refine ⟨27179714406193363134820757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18119809604128908756547171 27179714406193363134820757)
              ·
                refine ⟨1274049112790313896944723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27179714406193363134820757 1274049112790313896944723)
                ·
                  refine ⟨1911073669185470845417085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274049112790313896944723 1911073669185470845417085)
                  ·
                    refine ⟨716652625944551567031407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911073669185470845417085 716652625944551567031407)
                    ·
                      rfl

theorem cell22_2093514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_2093514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093514 prefixEnd_2093514 := by exact prefixLift 2093514
  have htrace : WordTrace (prefixWord ++ tailWord_2093514) baseStart_2093514 baseEnd_2093514 := by
    simpa [prefixWord, tailWord_2093514, baseEnd_2093514] using wordTrace_append hprefix tailTrace_2093514
  have hstable : (prefixWord ++ tailWord_2093514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093514).length < 2 ^ (prefixWord ++ tailWord_2093514).sum := by decide
  have hdescent : baseEnd_2093514 < baseStart_2093514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093585 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_2093585 : Nat := 118140960795 + 2093585 * 2 ^ 59
def prefixEnd_2093585 : Nat := 4983230072969 + 3 ^ 40 * 2093585 * 2
def baseEnd_2093585 : Nat := 716676930695531048506189

theorem tailTrace_2093585 : CollatzResearch.WordTrace tailWord_2093585 prefixEnd_2093585 716676930695531048506189 := by
  unfold tailWord_2093585
  simp only [CollatzResearch.WordTrace]
  refine ⟨76359318120306575696634209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50906212080204383797756139 76359318120306575696634209)
  ·
    refine ⟨57269488590229931772475657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76359318120306575696634209 57269488590229931772475657)
    ·
      refine ⟨42952116442672448829356743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57269488590229931772475657 42952116442672448829356743)
      ·
        refine ⟨64428174664008673244035115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42952116442672448829356743 64428174664008673244035115)
        ·
          refine ⟨96642261996013009866052673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64428174664008673244035115 96642261996013009866052673)
          ·
            refine ⟨72481696497009757399539505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96642261996013009866052673 72481696497009757399539505)
            ·
              refine ⟨54361272372757318049654629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72481696497009757399539505 54361272372757318049654629)
              ·
                refine ⟨10192738569891997134310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54361272372757318049654629 10192738569891997134310243)
                ·
                  refine ⟨15289107854837995701465365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192738569891997134310243 15289107854837995701465365)
                  ·
                    refine ⟨716676930695531048506189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15289107854837995701465365 716676930695531048506189)
                    ·
                      rfl

theorem cell22_2093585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_2093585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093585 prefixEnd_2093585 := by exact prefixLift 2093585
  have htrace : WordTrace (prefixWord ++ tailWord_2093585) baseStart_2093585 baseEnd_2093585 := by
    simpa [prefixWord, tailWord_2093585, baseEnd_2093585] using wordTrace_append hprefix tailTrace_2093585
  have hstable : (prefixWord ++ tailWord_2093585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093585).length < 2 ^ (prefixWord ++ tailWord_2093585).sum := by decide
  have hdescent : baseEnd_2093585 < baseStart_2093585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093638 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2093638 : Nat := 118140960795 + 2093638 * 2 ^ 59
def prefixEnd_2093638 : Nat := 4983230072969 + 3 ^ 40 * 2093638 * 2
def baseEnd_2093638 : Nat := 716695073678656576931027

theorem tailTrace_2093638 : CollatzResearch.WordTrace tailWord_2093638 prefixEnd_2093638 716695073678656576931027 := by
  unfold tailWord_2093638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386289099659830179634799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50907500792743043832209045 2386289099659830179634799)
  ·
    refine ⟨3579433649489745269452199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2386289099659830179634799 3579433649489745269452199)
    ·
      refine ⟨5369150474234617904178299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579433649489745269452199 5369150474234617904178299)
      ·
        refine ⟨8053725711351926856267449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369150474234617904178299 8053725711351926856267449)
        ·
          refine ⟨6040294283513945142200587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8053725711351926856267449 6040294283513945142200587)
          ·
            refine ⟨9060441425270917713300881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040294283513945142200587 9060441425270917713300881)
            ·
              refine ⟨6795331068953188284975661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9060441425270917713300881 6795331068953188284975661)
              ·
                refine ⟨2548249150857445606865873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6795331068953188284975661 2548249150857445606865873)
                ·
                  refine ⟨1911186863143084205149405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548249150857445606865873 1911186863143084205149405)
                  ·
                    refine ⟨716695073678656576931027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911186863143084205149405 716695073678656576931027)
                    ·
                      rfl

theorem cell22_2093638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2093638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093638 prefixEnd_2093638 := by exact prefixLift 2093638
  have htrace : WordTrace (prefixWord ++ tailWord_2093638) baseStart_2093638 baseEnd_2093638 := by
    simpa [prefixWord, tailWord_2093638, baseEnd_2093638] using wordTrace_append hprefix tailTrace_2093638
  have hstable : (prefixWord ++ tailWord_2093638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093638).length < 2 ^ (prefixWord ++ tailWord_2093638).sum := by decide
  have hdescent : baseEnd_2093638 < baseStart_2093638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093649 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_2093649 : Nat := 118140960795 + 2093649 * 2 ^ 59
def prefixEnd_2093649 : Nat := 4983230072969 + 3 ^ 40 * 2093649 * 2
def baseEnd_2093649 : Nat := 716698839203456214905993

theorem tailTrace_2093649 : CollatzResearch.WordTrace tailWord_2093649 prefixEnd_2093649 716698839203456214905993 := by
  unfold tailWord_2093649
  simp only [CollatzResearch.WordTrace]
  refine ⟨76361652392074714626964001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50907768261383143084642667 76361652392074714626964001)
  ·
    refine ⟨57271239294056035970223001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76361652392074714626964001 57271239294056035970223001)
    ·
      refine ⟨42953429470542026977667251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57271239294056035970223001 42953429470542026977667251)
      ·
        refine ⟨64430144205813040466500877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42953429470542026977667251 64430144205813040466500877)
        ·
          refine ⟨24161304077179890174937829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64430144205813040466500877 24161304077179890174937829)
          ·
            refine ⟨4530244514471229407800843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24161304077179890174937829 4530244514471229407800843)
            ·
              refine ⟨6795366771706844111701265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530244514471229407800843 6795366771706844111701265)
              ·
                refine ⟨5096525078780133083775949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795366771706844111701265 5096525078780133083775949)
                ·
                  refine ⟨1911196904542549906415981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5096525078780133083775949 1911196904542549906415981)
                  ·
                    refine ⟨716698839203456214905993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911196904542549906415981 716698839203456214905993)
                    ·
                      rfl

theorem cell22_2093649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_2093649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093649 prefixEnd_2093649 := by exact prefixLift 2093649
  have htrace : WordTrace (prefixWord ++ tailWord_2093649) baseStart_2093649 baseEnd_2093649 := by
    simpa [prefixWord, tailWord_2093649, baseEnd_2093649] using wordTrace_append hprefix tailTrace_2093649
  have hstable : (prefixWord ++ tailWord_2093649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093649).length < 2 ^ (prefixWord ++ tailWord_2093649).sum := by decide
  have hdescent : baseEnd_2093649 < baseStart_2093649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093692 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_2093692 : Nat := 118140960795 + 2093692 * 2 ^ 59
def prefixEnd_2093692 : Nat := 4983230072969 + 3 ^ 40 * 2093692 * 2
def baseEnd_2093692 : Nat := 716713558982218436080861

theorem tailTrace_2093692 : CollatzResearch.WordTrace tailWord_2093692 prefixEnd_2093692 716713558982218436080861 := by
  unfold tailWord_2093692
  simp only [CollatzResearch.WordTrace]
  refine ⟨38181610365459466485389665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50908813820612621980519553 38181610365459466485389665)
  ·
    refine ⟨28636207774094599864042249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38181610365459466485389665 28636207774094599864042249)
    ·
      refine ⟨21477155830570949898031687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28636207774094599864042249 21477155830570949898031687)
      ·
        refine ⟨32215733745856424847047531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21477155830570949898031687 32215733745856424847047531)
        ·
          refine ⟨48323600618784637270571297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32215733745856424847047531 48323600618784637270571297)
          ·
            refine ⟨36242700464088477952928473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48323600618784637270571297 36242700464088477952928473)
            ·
              refine ⟨27182025348066358464696355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36242700464088477952928473 27182025348066358464696355)
              ·
                refine ⟨40773038022099537697044533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27182025348066358464696355 40773038022099537697044533)
                ·
                  refine ⟨3822472314571831659097925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40773038022099537697044533 3822472314571831659097925)
                  ·
                    refine ⟨716713558982218436080861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822472314571831659097925 716713558982218436080861)
                    ·
                      rfl

theorem cell22_2093692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_2093692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093692 prefixEnd_2093692 := by exact prefixLift 2093692
  have htrace : WordTrace (prefixWord ++ tailWord_2093692) baseStart_2093692 baseEnd_2093692 := by
    simpa [prefixWord, tailWord_2093692, baseEnd_2093692] using wordTrace_append hprefix tailTrace_2093692
  have hstable : (prefixWord ++ tailWord_2093692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093692).length < 2 ^ (prefixWord ++ tailWord_2093692).sum := by decide
  have hdescent : baseEnd_2093692 < baseStart_2093692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093726 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2093726 : Nat := 118140960795 + 2093726 * 2 ^ 59
def prefixEnd_2093726 : Nat := 4983230072969 + 3 ^ 40 * 2093726 * 2
def baseEnd_2093726 : Nat := 716725197877053680730757

theorem tailTrace_2093726 : CollatzResearch.WordTrace tailWord_2093726 prefixEnd_2093726 716725197877053680730757 := by
  unfold tailWord_2093726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545557601599469597189629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50909640541863837851678021 9545557601599469597189629)
  ·
    refine ⟨3579584100599801098946111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9545557601599469597189629 3579584100599801098946111)
    ·
      refine ⟨5369376150899701648419167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579584100599801098946111 5369376150899701648419167)
      ·
        refine ⟨8054064226349552472628751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369376150899701648419167 8054064226349552472628751)
        ·
          refine ⟨12081096339524328708943127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054064226349552472628751 12081096339524328708943127)
          ·
            refine ⟨18121644509286493063414691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081096339524328708943127 18121644509286493063414691)
            ·
              refine ⟨27182466763929739595122037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18121644509286493063414691 27182466763929739595122037)
              ·
                refine ⟨2548356259118413087042691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27182466763929739595122037 2548356259118413087042691)
                ·
                  refine ⟨3822534388677619630564037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548356259118413087042691 3822534388677619630564037)
                  ·
                    refine ⟨716725197877053680730757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822534388677619630564037 716725197877053680730757)
                    ·
                      rfl

theorem cell22_2093726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2093726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093726 prefixEnd_2093726 := by exact prefixLift 2093726
  have htrace : WordTrace (prefixWord ++ tailWord_2093726) baseStart_2093726 baseEnd_2093726 := by
    simpa [prefixWord, tailWord_2093726, baseEnd_2093726] using wordTrace_append hprefix tailTrace_2093726
  have hstable : (prefixWord ++ tailWord_2093726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093726).length < 2 ^ (prefixWord ++ tailWord_2093726).sum := by decide
  have hdescent : baseEnd_2093726 < baseStart_2093726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093737 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_2093737 : Nat := 118140960795 + 2093737 * 2 ^ 59
def prefixEnd_2093737 : Nat := 4983230072969 + 3 ^ 40 * 2093737 * 2
def baseEnd_2093737 : Nat := 716728963401853318705723

theorem tailTrace_2093737 : CollatzResearch.WordTrace tailWord_2093737 prefixEnd_2093737 716728963401853318705723 := by
  unfold tailWord_2093737
  simp only [CollatzResearch.WordTrace]
  refine ⟨76364862015755905656167465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50909908010503937104111643 76364862015755905656167465)
  ·
    refine ⟨57273646511816929242125599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76364862015755905656167465 57273646511816929242125599)
    ·
      refine ⟨85910469767725393863188399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57273646511816929242125599 85910469767725393863188399)
      ·
        refine ⟨128865704651588090794782599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85910469767725393863188399 128865704651588090794782599)
        ·
          refine ⟨193298556977382136192173899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128865704651588090794782599 193298556977382136192173899)
          ·
            refine ⟨289947835466073204288260849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193298556977382136192173899 289947835466073204288260849)
            ·
              refine ⟨217460876599554903216195637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289947835466073204288260849 217460876599554903216195637)
              ·
                refine ⟨20386957181208272176518341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217460876599554903216195637 20386957181208272176518341)
                ·
                  refine ⟨3822554471476551033097189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20386957181208272176518341 3822554471476551033097189)
                  ·
                    refine ⟨716728963401853318705723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822554471476551033097189 716728963401853318705723)
                    ·
                      rfl

theorem cell22_2093737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_2093737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093737 prefixEnd_2093737 := by exact prefixLift 2093737
  have htrace : WordTrace (prefixWord ++ tailWord_2093737) baseStart_2093737 baseEnd_2093737 := by
    simpa [prefixWord, tailWord_2093737, baseEnd_2093737] using wordTrace_append hprefix tailTrace_2093737
  have hstable : (prefixWord ++ tailWord_2093737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093737).length < 2 ^ (prefixWord ++ tailWord_2093737).sum := by decide
  have hdescent : baseEnd_2093737 < baseStart_2093737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093741 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2093741 : Nat := 118140960795 + 2093741 * 2 ^ 59
def prefixEnd_2093741 : Nat := 4983230072969 + 3 ^ 40 * 2093741 * 2
def baseEnd_2093741 : Nat := 238910110894532880535237

theorem tailTrace_2093741 : CollatzResearch.WordTrace tailWord_2093741 prefixEnd_2093741 238910110894532880535237 := by
  unfold tailWord_2093741
  simp only [CollatzResearch.WordTrace]
  refine ⟨76365007907741414339313077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50910005271827609559542051 76365007907741414339313077)
  ·
    refine ⟨7159219491350757594310601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76365007907741414339313077 7159219491350757594310601)
    ·
      refine ⟨5369414618513068195732951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7159219491350757594310601 5369414618513068195732951)
      ·
        refine ⟨8054121927769602293599427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369414618513068195732951 8054121927769602293599427)
        ·
          refine ⟨12081182891654403440399141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054121927769602293599427 12081182891654403440399141)
          ·
            refine ⟨2265221792185200645074839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12081182891654403440399141 2265221792185200645074839)
            ·
              refine ⟨3397832688277800967612259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265221792185200645074839 3397832688277800967612259)
              ·
                refine ⟨5096749032416701451418389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397832688277800967612259 5096749032416701451418389)
                ·
                  refine ⟨238910110894532880535237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5096749032416701451418389 238910110894532880535237)
                  ·
                    rfl

theorem cell22_2093741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2093741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093741 prefixEnd_2093741 := by exact prefixLift 2093741
  have htrace : WordTrace (prefixWord ++ tailWord_2093741) baseStart_2093741 baseEnd_2093741 := by
    simpa [prefixWord, tailWord_2093741, baseEnd_2093741] using wordTrace_append hprefix tailTrace_2093741
  have hstable : (prefixWord ++ tailWord_2093741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093741).length < 2 ^ (prefixWord ++ tailWord_2093741).sum := by decide
  have hdescent : baseEnd_2093741 < baseStart_2093741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093756 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_2093756 : Nat := 118140960795 + 2093756 * 2 ^ 59
def prefixEnd_2093756 : Nat := 4983230072969 + 3 ^ 40 * 2093756 * 2
def baseEnd_2093756 : Nat := 716735467490143602480665

theorem tailTrace_2093756 : CollatzResearch.WordTrace tailWord_2093756 prefixEnd_2093756 716735467490143602480665 := by
  unfold tailWord_2093756
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182777501343535950554561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50910370001791381267406081 38182777501343535950554561)
  ·
    refine ⟨28637083126007651962915921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38182777501343535950554561 28637083126007651962915921)
    ·
      refine ⟨21477812344505738972186941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28637083126007651962915921 21477812344505738972186941)
      ·
        refine ⟨8054179629189652114570103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21477812344505738972186941 8054179629189652114570103)
        ·
          refine ⟨12081269443784478171855155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054179629189652114570103 12081269443784478171855155)
          ·
            refine ⟨18121904165676717257782733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081269443784478171855155 18121904165676717257782733)
            ·
              refine ⟨6795714062128768971668525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18121904165676717257782733 6795714062128768971668525)
              ·
                refine ⟨2548392773298288364375697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6795714062128768971668525 2548392773298288364375697)
                ·
                  refine ⟨1911294579973716273281773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548392773298288364375697 1911294579973716273281773)
                  ·
                    refine ⟨716735467490143602480665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911294579973716273281773 716735467490143602480665)
                    ·
                      rfl

theorem cell22_2093756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_2093756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093756 prefixEnd_2093756 := by exact prefixLift 2093756
  have htrace : WordTrace (prefixWord ++ tailWord_2093756) baseStart_2093756 baseEnd_2093756 := by
    simpa [prefixWord, tailWord_2093756, baseEnd_2093756] using wordTrace_append hprefix tailTrace_2093756
  have hstable : (prefixWord ++ tailWord_2093756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093756).length < 2 ^ (prefixWord ++ tailWord_2093756).sum := by decide
  have hdescent : baseEnd_2093756 < baseStart_2093756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093773 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2093773 : Nat := 118140960795 + 2093773 * 2 ^ 59
def prefixEnd_2093773 : Nat := 4983230072969 + 3 ^ 40 * 2093773 * 2
def baseEnd_2093773 : Nat := 716741286937561224805613

theorem tailTrace_2093773 : CollatzResearch.WordTrace tailWord_2093773 prefixEnd_2093773 716741286937561224805613 := by
  unfold tailWord_2093773
  simp only [CollatzResearch.WordTrace]
  refine ⟨76366175043625483804477973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50910783362416989202985315 76366175043625483804477973)
  ·
    refine ⟨3579664455169944553334905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76366175043625483804477973 3579664455169944553334905)
    ·
      refine ⟨2684748341377458415001179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3579664455169944553334905 2684748341377458415001179)
      ·
        refine ⟨4027122512066187622501769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684748341377458415001179 4027122512066187622501769)
        ·
          refine ⟨3020341884049640716876327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4027122512066187622501769 3020341884049640716876327)
          ·
            refine ⟨4530512826074461075314491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020341884049640716876327 4530512826074461075314491)
            ·
              refine ⟨6795769239111691612971737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530512826074461075314491 6795769239111691612971737)
              ·
                refine ⟨5096826929333768709728803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795769239111691612971737 5096826929333768709728803)
                ·
                  refine ⟨7645240394000653064593205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096826929333768709728803 7645240394000653064593205)
                  ·
                    refine ⟨716741286937561224805613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7645240394000653064593205 716741286937561224805613)
                    ·
                      rfl

theorem cell22_2093773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2093773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093773 prefixEnd_2093773 := by exact prefixLift 2093773
  have htrace : WordTrace (prefixWord ++ tailWord_2093773) baseStart_2093773 baseEnd_2093773 := by
    simpa [prefixWord, tailWord_2093773, baseEnd_2093773] using wordTrace_append hprefix tailTrace_2093773
  have hstable : (prefixWord ++ tailWord_2093773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093773).length < 2 ^ (prefixWord ++ tailWord_2093773).sum := by decide
  have hdescent : baseEnd_2093773 < baseStart_2093773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093906 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2093906 : Nat := 118140960795 + 2093906 * 2 ^ 59
def prefixEnd_2093906 : Nat := 4983230072969 + 3 ^ 40 * 2093906 * 2
def baseEnd_2093906 : Nat := 716786815555593211230205

theorem tailTrace_2093906 : CollatzResearch.WordTrace tailWord_2093906 prefixEnd_2093906 716786815555593211230205 := by
  unfold tailWord_2093906
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092756488035911879767393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50914017301429098346046381 19092756488035911879767393)
  ·
    refine ⟨14319567366026933909825545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19092756488035911879767393 14319567366026933909825545)
    ·
      refine ⟨10739675524520200432369159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14319567366026933909825545 10739675524520200432369159)
      ·
        refine ⟨16109513286780300648553739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739675524520200432369159 16109513286780300648553739)
        ·
          refine ⟨24164269930170450972830609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16109513286780300648553739 24164269930170450972830609)
          ·
            refine ⟨18123202447627838229622957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24164269930170450972830609 18123202447627838229622957)
            ·
              refine ⟨6796200917860439336108609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18123202447627838229622957 6796200917860439336108609)
              ·
                refine ⟨5097150688395329502081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6796200917860439336108609 5097150688395329502081457)
                ·
                  refine ⟨3822863016296497126561093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5097150688395329502081457 3822863016296497126561093)
                  ·
                    refine ⟨716786815555593211230205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822863016296497126561093 716786815555593211230205)
                    ·
                      rfl

theorem cell22_2093906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2093906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093906 prefixEnd_2093906 := by exact prefixLift 2093906
  have htrace : WordTrace (prefixWord ++ tailWord_2093906) baseStart_2093906 baseEnd_2093906 := by
    simpa [prefixWord, tailWord_2093906, baseEnd_2093906] using wordTrace_append hprefix tailTrace_2093906
  have hstable : (prefixWord ++ tailWord_2093906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093906).length < 2 ^ (prefixWord ++ tailWord_2093906).sum := by decide
  have hdescent : baseEnd_2093906 < baseStart_2093906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093936 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_2093936 : Nat := 118140960795 + 2093936 * 2 ^ 59
def prefixEnd_2093936 : Nat := 4983230072969 + 3 ^ 40 * 2093936 * 2
def baseEnd_2093936 : Nat := 716797085168683132980113

theorem tailTrace_2093936 : CollatzResearch.WordTrace tailWord_2093936 prefixEnd_2093936 716797085168683132980113 := by
  unfold tailWord_2093936
  simp only [CollatzResearch.WordTrace]
  refine ⟨38186060071017481321330831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50914746761356641761774441 38186060071017481321330831)
  ·
    refine ⟨57279090106526221981996247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38186060071017481321330831 57279090106526221981996247)
    ·
      refine ⟨85918635159789332972994371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57279090106526221981996247 85918635159789332972994371)
      ·
        refine ⟨128877952739683999459491557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85918635159789332972994371 128877952739683999459491557)
        ·
          refine ⟨24164616138690749898654667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128877952739683999459491557 24164616138690749898654667)
          ·
            refine ⟨36246924208036124847982001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24164616138690749898654667 36246924208036124847982001)
            ·
              refine ⟨27185193156027093635986501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36246924208036124847982001 27185193156027093635986501)
              ·
                refine ⟨5097223716755080056747469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27185193156027093635986501 5097223716755080056747469)
                ·
                  refine ⟨1911458893783155021280301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5097223716755080056747469 1911458893783155021280301)
                  ·
                    refine ⟨716797085168683132980113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911458893783155021280301 716797085168683132980113)
                    ·
                      rfl

theorem cell22_2093936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_2093936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093936 prefixEnd_2093936 := by exact prefixLift 2093936
  have htrace : WordTrace (prefixWord ++ tailWord_2093936) baseStart_2093936 baseEnd_2093936 := by
    simpa [prefixWord, tailWord_2093936, baseEnd_2093936] using wordTrace_append hprefix tailTrace_2093936
  have hstable : (prefixWord ++ tailWord_2093936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093936).length < 2 ^ (prefixWord ++ tailWord_2093936).sum := by decide
  have hdescent : baseEnd_2093936 < baseStart_2093936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093949 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2093949 : Nat := 118140960795 + 2093949 * 2 ^ 59
def prefixEnd_2093949 : Nat := 4983230072969 + 3 ^ 40 * 2093949 * 2
def baseEnd_2093949 : Nat := 238933845111451810801691

theorem tailTrace_2093949 : CollatzResearch.WordTrace tailWord_2093949 prefixEnd_2093949 238933845111451810801691 := by
  unfold tailWord_2093949
  simp only [CollatzResearch.WordTrace]
  refine ⟨76372594290987865862884901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50915062860658577241923267 76372594290987865862884901)
  ·
    refine ⟨14319861429560224849290919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76372594290987865862884901 14319861429560224849290919)
    ·
      refine ⟨21479792144340337273936379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14319861429560224849290919 21479792144340337273936379)
      ·
        refine ⟨32219688216510505910904569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21479792144340337273936379 32219688216510505910904569)
        ·
          refine ⟨24164766162382879433178427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32219688216510505910904569 24164766162382879433178427)
          ·
            refine ⟨36247149243574319149767641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24164766162382879433178427 36247149243574319149767641)
            ·
              refine ⟨27185361932680739362325731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36247149243574319149767641 27185361932680739362325731)
              ·
                refine ⟨40778042899021109043488597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27185361932680739362325731 40778042899021109043488597)
                ·
                  refine ⟨238933845111451810801691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40778042899021109043488597 238933845111451810801691)
                  ·
                    rfl

theorem cell22_2093949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2093949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093949 prefixEnd_2093949 := by exact prefixLift 2093949
  have htrace : WordTrace (prefixWord ++ tailWord_2093949) baseStart_2093949 baseEnd_2093949 := by
    simpa [prefixWord, tailWord_2093949, baseEnd_2093949] using wordTrace_append hprefix tailTrace_2093949
  have hstable : (prefixWord ++ tailWord_2093949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093949).length < 2 ^ (prefixWord ++ tailWord_2093949).sum := by decide
  have hdescent : baseEnd_2093949 < baseStart_2093949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093981 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2093981 : Nat := 118140960795 + 2093981 * 2 ^ 59
def prefixEnd_2093981 : Nat := 4983230072969 + 3 ^ 40 * 2093981 * 2
def baseEnd_2093981 : Nat := 716812489588318015604975

theorem tailTrace_2093981 : CollatzResearch.WordTrace tailWord_2093981 prefixEnd_2093981 716812489588318015604975 := by
  unfold tailWord_2093981
  simp only [CollatzResearch.WordTrace]
  refine ⟨76373761426871935328049797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50915840951247956885366531 76373761426871935328049797)
  ·
    refine ⟨14320080267538487874009337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76373761426871935328049797 14320080267538487874009337)
    ·
      refine ⟨10740060200653865905507003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14320080267538487874009337 10740060200653865905507003)
      ·
        refine ⟨16110090300980798858260505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740060200653865905507003 16110090300980798858260505)
        ·
          refine ⟨12082567725735599143695379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16110090300980798858260505 12082567725735599143695379)
          ·
            refine ⟨18123851588603398715543069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082567725735599143695379 18123851588603398715543069)
            ·
              refine ⟨6796444345726274518328651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18123851588603398715543069 6796444345726274518328651)
              ·
                refine ⟨10194666518589411777492977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796444345726274518328651 10194666518589411777492977)
                ·
                  refine ⟨7645999888942058833119733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10194666518589411777492977 7645999888942058833119733)
                  ·
                    refine ⟨716812489588318015604975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7645999888942058833119733 716812489588318015604975)
                    ·
                      rfl

theorem cell22_2093981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2093981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2093981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2093981 prefixEnd_2093981 := by exact prefixLift 2093981
  have htrace : WordTrace (prefixWord ++ tailWord_2093981) baseStart_2093981 baseEnd_2093981 := by
    simpa [prefixWord, tailWord_2093981, baseEnd_2093981] using wordTrace_append hprefix tailTrace_2093981
  have hstable : (prefixWord ++ tailWord_2093981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093981).length < 2 ^ (prefixWord ++ tailWord_2093981).sum := by decide
  have hdescent : baseEnd_2093981 < baseStart_2093981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094004 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2094004 : Nat := 118140960795 + 2094004 * 2 ^ 59
def prefixEnd_2094004 : Nat := 4983230072969 + 3 ^ 40 * 2094004 * 2
def baseEnd_2094004 : Nat := 716820362958353622279905

theorem tailTrace_2094004 : CollatzResearch.WordTrace tailWord_2094004 prefixEnd_2094004 716820362958353622279905 := by
  unfold tailWord_2094004
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187300152894305128068533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50916400203859073504091377 38187300152894305128068533)
  ·
    refine ⟨3580059389333841105756425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38187300152894305128068533 3580059389333841105756425)
    ·
      refine ⟨2685044542000380829317319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3580059389333841105756425 2685044542000380829317319)
      ·
        refine ⟨4027566813000571243975979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685044542000380829317319 4027566813000571243975979)
        ·
          refine ⟨6041350219500856865963969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027566813000571243975979 6041350219500856865963969)
          ·
            refine ⟨4531012664625642649472977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6041350219500856865963969 4531012664625642649472977)
            ·
              refine ⟨3398259498469231987104733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531012664625642649472977 3398259498469231987104733)
              ·
                refine ⟨1274347311925961995164275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3398259498469231987104733 1274347311925961995164275)
                ·
                  refine ⟨1911520967888942992746413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274347311925961995164275 1911520967888942992746413)
                  ·
                    refine ⟨716820362958353622279905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911520967888942992746413 716820362958353622279905)
                    ·
                      rfl

theorem cell22_2094004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2094004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094004 prefixEnd_2094004 := by exact prefixLift 2094004
  have htrace : WordTrace (prefixWord ++ tailWord_2094004) baseStart_2094004 baseEnd_2094004 := by
    simpa [prefixWord, tailWord_2094004, baseEnd_2094004] using wordTrace_append hprefix tailTrace_2094004
  have hstable : (prefixWord ++ tailWord_2094004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094004).length < 2 ^ (prefixWord ++ tailWord_2094004).sum := by decide
  have hdescent : baseEnd_2094004 < baseStart_2094004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094028 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 4]
def baseStart_2094028 : Nat := 118140960795 + 2094028 * 2 ^ 59
def prefixEnd_2094028 : Nat := 4983230072969 + 3 ^ 40 * 2094028 * 2
def baseEnd_2094028 : Nat := 238942859549608519893277

theorem tailTrace_2094028 : CollatzResearch.WordTrace tailWord_2094028 prefixEnd_2094028 238942859549608519893277 := by
  unfold tailWord_2094028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187737828850831177505369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50916983771801108236673825 38187737828850831177505369)
  ·
    refine ⟨28640803371638123383129027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38187737828850831177505369 28640803371638123383129027)
    ·
      refine ⟨42961205057457185074693541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28640803371638123383129027 42961205057457185074693541)
      ·
        refine ⟨8055225948273222201505039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42961205057457185074693541 8055225948273222201505039)
        ·
          refine ⟨12082838922409833302257559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055225948273222201505039 12082838922409833302257559)
          ·
            refine ⟨18124258383614749953386339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082838922409833302257559 18124258383614749953386339)
            ·
              refine ⟨27186387575422124930079509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18124258383614749953386339 27186387575422124930079509)
              ·
                refine ⟨1274361917597912106097477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27186387575422124930079509 1274361917597912106097477)
                ·
                  refine ⟨238942859549608519893277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274361917597912106097477 238942859549608519893277)
                  ·
                    rfl

theorem cell22_2094028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_2094028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094028 prefixEnd_2094028 := by exact prefixLift 2094028
  have htrace : WordTrace (prefixWord ++ tailWord_2094028) baseStart_2094028 baseEnd_2094028 := by
    simpa [prefixWord, tailWord_2094028, baseEnd_2094028] using wordTrace_append hprefix tailTrace_2094028
  have hstable : (prefixWord ++ tailWord_2094028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094028).length < 2 ^ (prefixWord ++ tailWord_2094028).sum := by decide
  have hdescent : baseEnd_2094028 < baseStart_2094028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094041 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_2094041 : Nat := 118140960795 + 2094041 * 2 ^ 59
def prefixEnd_2094041 : Nat := 4983230072969 + 3 ^ 40 * 2094041 * 2
def baseEnd_2094041 : Nat := 716833028814497859104791

theorem tailTrace_2094041 : CollatzResearch.WordTrace tailWord_2094041 prefixEnd_2094041 716833028814497859104791 := by
  unfold tailWord_2094041
  simp only [CollatzResearch.WordTrace]
  refine ⟨76375949806654565575233977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50917299871103043716822651 76375949806654565575233977)
  ·
    refine ⟨57281962354990924181425483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76375949806654565575233977 57281962354990924181425483)
    ·
      refine ⟨85922943532486386272138225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57281962354990924181425483 85922943532486386272138225)
      ·
        refine ⟨64442207649364789704103669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85922943532486386272138225 64442207649364789704103669)
        ·
          refine ⟨6041456967127949034759719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64442207649364789704103669 6041456967127949034759719)
          ·
            refine ⟨9062185450691923552139579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041456967127949034759719 9062185450691923552139579)
            ·
              refine ⟨13593278176037885328209369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062185450691923552139579 13593278176037885328209369)
              ·
                refine ⟨10194958632028413996157027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13593278176037885328209369 10194958632028413996157027)
                ·
                  refine ⟨15292437948042620994235541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194958632028413996157027 15292437948042620994235541)
                  ·
                    refine ⟨716833028814497859104791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15292437948042620994235541 716833028814497859104791)
                    ·
                      rfl

theorem cell22_2094041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_2094041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094041 prefixEnd_2094041 := by exact prefixLift 2094041
  have htrace : WordTrace (prefixWord ++ tailWord_2094041) baseStart_2094041 baseEnd_2094041 := by
    simpa [prefixWord, tailWord_2094041, baseEnd_2094041] using wordTrace_append hprefix tailTrace_2094041
  have hstable : (prefixWord ++ tailWord_2094041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094041).length < 2 ^ (prefixWord ++ tailWord_2094041).sum := by decide
  have hdescent : baseEnd_2094041 < baseStart_2094041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094062 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_2094062 : Nat := 118140960795 + 2094062 * 2 ^ 59
def prefixEnd_2094062 : Nat := 4983230072969 + 3 ^ 40 * 2094062 * 2
def baseEnd_2094062 : Nat := 238946739181220268109909

theorem tailTrace_2094062 : CollatzResearch.WordTrace tailWord_2094062 prefixEnd_2094062 238946739181220268109909 := by
  unfold tailWord_2094062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9547089467447310770218555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50917810493052324107832293 9547089467447310770218555)
  ·
    refine ⟨14320634201170966155327833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9547089467447310770218555 14320634201170966155327833)
    ·
      refine ⟨10740475650878224616495875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14320634201170966155327833 10740475650878224616495875)
      ·
        refine ⟨16110713476317336924743813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740475650878224616495875 16110713476317336924743813)
        ·
          refine ⟨3020758776809500673389465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16110713476317336924743813 3020758776809500673389465)
          ·
            refine ⟨2265569082607125505042099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3020758776809500673389465 2265569082607125505042099)
            ·
              refine ⟨3398353623910688257563149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265569082607125505042099 3398353623910688257563149)
              ·
                refine ⟨1274382608966508096586181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3398353623910688257563149 1274382608966508096586181)
                ·
                  refine ⟨238946739181220268109909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274382608966508096586181 238946739181220268109909)
                  ·
                    rfl

theorem cell22_2094062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_2094062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094062 prefixEnd_2094062 := by exact prefixLift 2094062
  have htrace : WordTrace (prefixWord ++ tailWord_2094062) baseStart_2094062 baseEnd_2094062 := by
    simpa [prefixWord, tailWord_2094062, baseEnd_2094062] using wordTrace_append hprefix tailTrace_2094062
  have hstable : (prefixWord ++ tailWord_2094062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094062).length < 2 ^ (prefixWord ++ tailWord_2094062).sum := by decide
  have hdescent : baseEnd_2094062 < baseStart_2094062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094150 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2094150 : Nat := 118140960795 + 2094150 * 2 ^ 59
def prefixEnd_2094150 : Nat := 4983230072969 + 3 ^ 40 * 2094150 * 2
def baseEnd_2094150 : Nat := 716870341742057908129457

theorem tailTrace_2094150 : CollatzResearch.WordTrace tailWord_2094150 prefixEnd_2094150 716870341742057908129457 := by
  unfold tailWord_2094150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386872667601864912217247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50919950242173118127301269 2386872667601864912217247)
  ·
    refine ⟨3580309001402797368325871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2386872667601864912217247 3580309001402797368325871)
    ·
      refine ⟨5370463502104196052488807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3580309001402797368325871 5370463502104196052488807)
      ·
        refine ⟨8055695253156294078733211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370463502104196052488807 8055695253156294078733211)
        ·
          refine ⟨12083542879734441118099817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055695253156294078733211 12083542879734441118099817)
          ·
            refine ⟨9062657159800830838574863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12083542879734441118099817 9062657159800830838574863)
            ·
              refine ⟨13593985739701246257862295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062657159800830838574863 13593985739701246257862295)
              ·
                refine ⟨20390978609551869386793443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593985739701246257862295 20390978609551869386793443)
                ·
                  refine ⟨30586467914327804080190165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20390978609551869386793443 30586467914327804080190165)
                  ·
                    refine ⟨716870341742057908129457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30586467914327804080190165 716870341742057908129457)
                    ·
                      rfl

theorem cell22_2094150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2094150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094150 prefixEnd_2094150 := by exact prefixLift 2094150
  have htrace : WordTrace (prefixWord ++ tailWord_2094150) baseStart_2094150 baseEnd_2094150 := by
    simpa [prefixWord, tailWord_2094150, baseEnd_2094150] using wordTrace_append hprefix tailTrace_2094150
  have hstable : (prefixWord ++ tailWord_2094150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094150).length < 2 ^ (prefixWord ++ tailWord_2094150).sum := by decide
  have hdescent : baseEnd_2094150 < baseStart_2094150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094191 : List Nat := [1, 1, 2, 1, 3, 3, 11]
def baseStart_2094191 : Nat := 118140960795 + 2094191 * 2 ^ 59
def prefixEnd_2094191 : Nat := 4983230072969 + 3 ^ 40 * 2094191 * 2
def baseEnd_2094191 : Nat := 26551273217775832142753

theorem tailTrace_2094191 : CollatzResearch.WordTrace tailWord_2094191 prefixEnd_2094191 26551273217775832142753 := by
  unfold tailWord_2094191
  simp only [CollatzResearch.WordTrace]
  refine ⟨76381420756111141193194427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50920947170740760795462951 76381420756111141193194427)
  ·
    refine ⟨114572131134166711789791641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76381420756111141193194427 114572131134166711789791641)
    ·
      refine ⟨85929098350625033842343731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114572131134166711789791641 85929098350625033842343731)
      ·
        refine ⟨128893647525937550763515597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85929098350625033842343731 128893647525937550763515597)
        ·
          refine ⟨48335117822226581536318349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128893647525937550763515597 48335117822226581536318349)
          ·
            refine ⟨18125669183334968076119381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48335117822226581536318349 18125669183334968076119381)
            ·
              refine ⟨26551273217775832142753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18125669183334968076119381 26551273217775832142753)
              ·
                rfl

theorem cell22_2094191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 11].length) (baseStart_2094191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094191 prefixEnd_2094191 := by exact prefixLift 2094191
  have htrace : WordTrace (prefixWord ++ tailWord_2094191) baseStart_2094191 baseEnd_2094191 := by
    simpa [prefixWord, tailWord_2094191, baseEnd_2094191] using wordTrace_append hprefix tailTrace_2094191
  have hstable : (prefixWord ++ tailWord_2094191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094191).length < 2 ^ (prefixWord ++ tailWord_2094191).sum := by decide
  have hdescent : baseEnd_2094191 < baseStart_2094191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094197 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 6]
def baseStart_2094197 : Nat := 118140960795 + 2094197 * 2 ^ 59
def prefixEnd_2094197 : Nat := 4983230072969 + 3 ^ 40 * 2094197 * 2
def baseEnd_2094197 : Nat := 238962143600855150734771

theorem tailTrace_2094197 : CollatzResearch.WordTrace tailWord_2094197 prefixEnd_2094197 238962143600855150734771 := by
  unfold tailWord_2094197
  simp only [CollatzResearch.WordTrace]
  refine ⟨76381639594089404217912845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50921093062726269478608563 76381639594089404217912845)
  ·
    refine ⟨28643114847783526581717317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76381639594089404217912845 28643114847783526581717317)
    ·
      refine ⟨5370584033959411234071997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28643114847783526581717317 5370584033959411234071997)
      ·
        refine ⟨2013969012734779212776999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5370584033959411234071997 2013969012734779212776999)
        ·
          refine ⟨3020953519102168819165499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013969012734779212776999 3020953519102168819165499)
          ·
            refine ⟨4531430278653253228748249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020953519102168819165499 4531430278653253228748249)
            ·
              refine ⟨3398572708989939921561187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531430278653253228748249 3398572708989939921561187)
              ·
                refine ⟨5097859063484909882341781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398572708989939921561187 5097859063484909882341781)
                ·
                  refine ⟨238962143600855150734771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5097859063484909882341781 238962143600855150734771)
                  ·
                    rfl

theorem cell22_2094197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_2094197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094197 prefixEnd_2094197 := by exact prefixLift 2094197
  have htrace : WordTrace (prefixWord ++ tailWord_2094197) baseStart_2094197 baseEnd_2094197 := by
    simpa [prefixWord, tailWord_2094197, baseEnd_2094197] using wordTrace_append hprefix tailTrace_2094197
  have hstable : (prefixWord ++ tailWord_2094197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094197).length < 2 ^ (prefixWord ++ tailWord_2094197).sum := by decide
  have hdescent : baseEnd_2094197 < baseStart_2094197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094223 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 9, 3]
def baseStart_2094223 : Nat := 118140960795 + 2094223 * 2 ^ 59
def prefixEnd_2094223 : Nat := 4983230072969 + 3 ^ 40 * 2094223 * 2
def baseEnd_2094223 : Nat := 716895331133910051054233

theorem tailTrace_2094223 : CollatzResearch.WordTrace tailWord_2094223 prefixEnd_2094223 716895331133910051054233 := by
  unfold tailWord_2094223
  simp only [CollatzResearch.WordTrace]
  refine ⟨76382587891995210658359323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50921725261330140438906215 76382587891995210658359323)
  ·
    refine ⟨114573881837992815987538985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76382587891995210658359323 114573881837992815987538985)
    ·
      refine ⟨85930411378494611990654239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114573881837992815987538985 85930411378494611990654239)
      ·
        refine ⟨128895617067741917985981359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85930411378494611990654239 128895617067741917985981359)
        ·
          refine ⟨193343425601612876978972039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128895617067741917985981359 193343425601612876978972039)
          ·
            refine ⟨290015138402419315468458059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193343425601612876978972039 290015138402419315468458059)
            ·
              refine ⟨435022707603628973202687089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290015138402419315468458059 435022707603628973202687089)
              ·
                refine ⟨326267030702721729902015317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435022707603628973202687089 326267030702721729902015317)
                ·
                  refine ⟨1911720883023760136144621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 326267030702721729902015317 1911720883023760136144621)
                  ·
                    refine ⟨716895331133910051054233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911720883023760136144621 716895331133910051054233)
                    ·
                      rfl

theorem cell22_2094223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_2094223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094223 prefixEnd_2094223 := by exact prefixLift 2094223
  have htrace : WordTrace (prefixWord ++ tailWord_2094223) baseStart_2094223 baseEnd_2094223 := by
    simpa [prefixWord, tailWord_2094223, baseEnd_2094223] using wordTrace_append hprefix tailTrace_2094223
  have hstable : (prefixWord ++ tailWord_2094223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094223).length < 2 ^ (prefixWord ++ tailWord_2094223).sum := by decide
  have hdescent : baseEnd_2094223 < baseStart_2094223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094242 : List Nat := [3, 3, 1, 3, 3, 1, 8]
def baseStart_2094242 : Nat := 118140960795 + 2094242 * 2 ^ 59
def prefixEnd_2094242 : Nat := 4983230072969 + 3 ^ 40 * 2094242 * 2
def baseEnd_2094242 : Nat := 26551919823044456845525

theorem tailTrace_2094242 : CollatzResearch.WordTrace tailWord_2094242 prefixEnd_2094242 26551919823044456845525 := by
  unfold tailWord_2094242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095820219731594225825245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50922187252617584602200653 19095820219731594225825245)
  ·
    refine ⟨7160932582399347834684467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19095820219731594225825245 7160932582399347834684467)
    ·
      refine ⟨10741398873599021752026701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160932582399347834684467 10741398873599021752026701)
      ·
        refine ⟨4028024577599633157010013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10741398873599021752026701 4028024577599633157010013)
        ·
          refine ⟨1510509216599862433878755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4028024577599633157010013 1510509216599862433878755)
          ·
            refine ⟨2265763824899793650818133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510509216599862433878755 2265763824899793650818133)
            ·
              refine ⟨26551919823044456845525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2265763824899793650818133 26551919823044456845525)
              ·
                rfl

theorem cell22_2094242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 8].length) (baseStart_2094242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094242 prefixEnd_2094242 := by exact prefixLift 2094242
  have htrace : WordTrace (prefixWord ++ tailWord_2094242) baseStart_2094242 baseEnd_2094242 := by
    simpa [prefixWord, tailWord_2094242, baseEnd_2094242] using wordTrace_append hprefix tailTrace_2094242
  have hstable : (prefixWord ++ tailWord_2094242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094242).length < 2 ^ (prefixWord ++ tailWord_2094242).sum := by decide
  have hdescent : baseEnd_2094242 < baseStart_2094242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094257 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_2094257 : Nat := 118140960795 + 2094257 * 2 ^ 59
def prefixEnd_2094257 : Nat := 4983230072969 + 3 ^ 40 * 2094257 * 2
def baseEnd_2094257 : Nat := 716906970028745295704129

theorem tailTrace_2094257 : CollatzResearch.WordTrace tailWord_2094257 prefixEnd_2094257 716906970028745295704129 := by
  unfold tailWord_2094257
  simp only [CollatzResearch.WordTrace]
  refine ⟨76383827973872034465097025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50922551982581356310064683 76383827973872034465097025)
  ·
    refine ⟨57287870980404025848822769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76383827973872034465097025 57287870980404025848822769)
    ·
      refine ⟨42965903235303019386617077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57287870980404025848822769 42965903235303019386617077)
      ·
        refine ⟨4028053428309658067495351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42965903235303019386617077 4028053428309658067495351)
        ·
          refine ⟨6042080142464487101243027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028053428309658067495351 6042080142464487101243027)
          ·
            refine ⟨9063120213696730651864541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042080142464487101243027 9063120213696730651864541)
            ·
              refine ⟨3398670080136273994449203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9063120213696730651864541 3398670080136273994449203)
              ·
                refine ⟨5098005120204410991673805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398670080136273994449203 5098005120204410991673805)
                ·
                  refine ⟨1911751920076654121877677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5098005120204410991673805 1911751920076654121877677)
                  ·
                    refine ⟨716906970028745295704129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911751920076654121877677 716906970028745295704129)
                    ·
                      rfl

theorem cell22_2094257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_2094257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094257 prefixEnd_2094257 := by exact prefixLift 2094257
  have htrace : WordTrace (prefixWord ++ tailWord_2094257) baseStart_2094257 baseEnd_2094257 := by
    simpa [prefixWord, tailWord_2094257, baseEnd_2094257] using wordTrace_append hprefix tailTrace_2094257
  have hstable : (prefixWord ++ tailWord_2094257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094257).length < 2 ^ (prefixWord ++ tailWord_2094257).sum := by decide
  have hdescent : baseEnd_2094257 < baseStart_2094257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094330 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_2094330 : Nat := 118140960795 + 2094330 * 2 ^ 59
def prefixEnd_2094330 : Nat := 4983230072969 + 3 ^ 40 * 2094330 * 2
def baseEnd_2094330 : Nat := 716931959420597438628905

theorem tailTrace_2094330 : CollatzResearch.WordTrace tailWord_2094330 prefixEnd_2094330 716931959420597438628905 := by
  unfold tailWord_2094330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096622625651891983126111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50924327001738378621669629 19096622625651891983126111)
  ·
    refine ⟨28644933938477837974689167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19096622625651891983126111 28644933938477837974689167)
    ·
      refine ⟨42967400907716756962033751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28644933938477837974689167 42967400907716756962033751)
      ·
        refine ⟨64451101361575135443050627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42967400907716756962033751 64451101361575135443050627)
        ·
          refine ⟨96676652042362703164575941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64451101361575135443050627 96676652042362703164575941)
          ·
            refine ⟨18126872257943006843357989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96676652042362703164575941 18126872257943006843357989)
            ·
              refine ⟨3398788548364313783129623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18126872257943006843357989 3398788548364313783129623)
              ·
                refine ⟨5098182822546470674694435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398788548364313783129623 5098182822546470674694435)
                ·
                  refine ⟨7647274233819706012041653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098182822546470674694435 7647274233819706012041653)
                  ·
                    refine ⟨716931959420597438628905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7647274233819706012041653 716931959420597438628905)
                    ·
                      rfl

theorem cell22_2094330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_2094330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094330 prefixEnd_2094330 := by exact prefixLift 2094330
  have htrace : WordTrace (prefixWord ++ tailWord_2094330) baseStart_2094330 baseEnd_2094330 := by
    simpa [prefixWord, tailWord_2094330, baseEnd_2094330] using wordTrace_append hprefix tailTrace_2094330
  have hstable : (prefixWord ++ tailWord_2094330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094330).length < 2 ^ (prefixWord ++ tailWord_2094330).sum := by decide
  have hdescent : baseEnd_2094330 < baseStart_2094330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094409 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 1, 3]
def baseStart_2094409 : Nat := 118140960795 + 2094409 * 2 ^ 59
def prefixEnd_2094409 : Nat := 4983230072969 + 3 ^ 40 * 2094409 * 2
def baseEnd_2094409 : Nat := 716959002735067565903663

theorem tailTrace_2094409 : CollatzResearch.WordTrace tailWord_2094409 prefixEnd_2094409 716959002735067565903663 := by
  unfold tailWord_2094409
  simp only [CollatzResearch.WordTrace]
  refine ⟨76389371869321364424630281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50926247912880909616420187 76389371869321364424630281)
  ·
    refine ⟨57292028901991023318472711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76389371869321364424630281 57292028901991023318472711)
    ·
      refine ⟨85938043352986534977709067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57292028901991023318472711 85938043352986534977709067)
      ·
        refine ⟨128907065029479802466563601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85938043352986534977709067 128907065029479802466563601)
        ·
          refine ⟨96680298772109851849922701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128907065029479802466563601 96680298772109851849922701)
          ·
            refine ⟨36255112039541194443721013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96680298772109851849922701 36255112039541194443721013)
            ·
              refine ⟨3398916753706986979098845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36255112039541194443721013 3398916753706986979098845)
              ·
                refine ⟨1274593782640120117162067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3398916753706986979098845 1274593782640120117162067)
                ·
                  refine ⟨1911890673960180175743101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274593782640120117162067 1911890673960180175743101)
                  ·
                    refine ⟨716959002735067565903663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911890673960180175743101 716959002735067565903663)
                    ·
                      rfl

theorem cell22_2094409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_2094409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094409 prefixEnd_2094409 := by exact prefixLift 2094409
  have htrace : WordTrace (prefixWord ++ tailWord_2094409) baseStart_2094409 baseEnd_2094409 := by
    simpa [prefixWord, tailWord_2094409, baseEnd_2094409] using wordTrace_append hprefix tailTrace_2094409
  have hstable : (prefixWord ++ tailWord_2094409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094409).length < 2 ^ (prefixWord ++ tailWord_2094409).sum := by decide
  have hdescent : baseEnd_2094409 < baseStart_2094409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094450 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_2094450 : Nat := 118140960795 + 2094450 * 2 ^ 59
def prefixEnd_2094450 : Nat := 4983230072969 + 3 ^ 40 * 2094450 * 2
def baseEnd_2094450 : Nat := 238991012624319041876179

theorem tailTrace_2094450 : CollatzResearch.WordTrace tailWord_2094450 prefixEnd_2094450 238991012624319041876179 := by
  unfold tailWord_2094450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097716815543207106718201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50927244841448552284581869 19097716815543207106718201)
  ·
    refine ⟨14323287611657405330038651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19097716815543207106718201 14323287611657405330038651)
    ·
      refine ⟨21484931417486107995057977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323287611657405330038651 21484931417486107995057977)
      ·
        refine ⟨16113698563114580996293483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21484931417486107995057977 16113698563114580996293483)
        ·
          refine ⟨24170547844671871494440225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16113698563114580996293483 24170547844671871494440225)
          ·
            refine ⟨18127910883503903620830169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24170547844671871494440225 18127910883503903620830169)
            ·
              refine ⟨13595933162627927715622627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18127910883503903620830169 13595933162627927715622627)
              ·
                refine ⟨20393899743941891573433941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595933162627927715622627 20393899743941891573433941)
                ·
                  refine ⟨238991012624319041876179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20393899743941891573433941 238991012624319041876179)
                  ·
                    rfl

theorem cell22_2094450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_2094450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094450 prefixEnd_2094450 := by exact prefixLift 2094450
  have htrace : WordTrace (prefixWord ++ tailWord_2094450) baseStart_2094450 baseEnd_2094450 := by
    simpa [prefixWord, tailWord_2094450, baseEnd_2094450] using wordTrace_append hprefix tailTrace_2094450
  have hstable : (prefixWord ++ tailWord_2094450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094450).length < 2 ^ (prefixWord ++ tailWord_2094450).sum := by decide
  have hdescent : baseEnd_2094450 < baseStart_2094450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094578 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_2094578 : Nat := 118140960795 + 2094578 * 2 ^ 59
def prefixEnd_2094578 : Nat := 4983230072969 + 3 ^ 40 * 2094578 * 2
def baseEnd_2094578 : Nat := 717016854888807458428145

theorem tailTrace_2094578 : CollatzResearch.WordTrace tailWord_2094578 prefixEnd_2094578 717016854888807458428145 := by
  unfold tailWord_2094578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098883951427276571883097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50930357203806070858354925 19098883951427276571883097)
  ·
    refine ⟨14324162963570457428912323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19098883951427276571883097 14324162963570457428912323)
    ·
      refine ⟨21486244445355686143368485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324162963570457428912323 21486244445355686143368485)
      ·
        refine ⟨4028670833504191151881591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21486244445355686143368485 4028670833504191151881591)
        ·
          refine ⟨6043006250256286727822387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028670833504191151881591 6043006250256286727822387)
          ·
            refine ⟨9064509375384430091733581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043006250256286727822387 9064509375384430091733581)
            ·
              refine ⟨3399191015769161284400093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064509375384430091733581 3399191015769161284400093)
              ·
                refine ⟨1274696630913435481650035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3399191015769161284400093 1274696630913435481650035)
                ·
                  refine ⟨1912044946370153222475053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274696630913435481650035 1912044946370153222475053)
                  ·
                    refine ⟨717016854888807458428145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912044946370153222475053 717016854888807458428145)
                    ·
                      rfl

theorem cell22_2094578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_2094578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094578 prefixEnd_2094578 := by exact prefixLift 2094578
  have htrace : WordTrace (prefixWord ++ tailWord_2094578) baseStart_2094578 baseEnd_2094578 := by
    simpa [prefixWord, tailWord_2094578, baseEnd_2094578] using wordTrace_append hprefix tailTrace_2094578
  have hstable : (prefixWord ++ tailWord_2094578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094578).length < 2 ^ (prefixWord ++ tailWord_2094578).sum := by decide
  have hdescent : baseEnd_2094578 < baseStart_2094578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094634 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2094634 : Nat := 118140960795 + 2094634 * 2 ^ 59
def prefixEnd_2094634 : Nat := 4983230072969 + 3 ^ 40 * 2094634 * 2
def baseEnd_2094634 : Nat := 717036024833241979027973

theorem tailTrace_2094634 : CollatzResearch.WordTrace tailWord_2094634 prefixEnd_2094634 717036024833241979027973 := by
  unfold tailWord_2094634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099394573376556962892739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50931718862337485234380637 19099394573376556962892739)
  ·
    refine ⟨28649091860064835444339109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19099394573376556962892739 28649091860064835444339109)
    ·
      refine ⟨5371704723762156645813583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28649091860064835444339109 5371704723762156645813583)
      ·
        refine ⟨8057557085643234968720375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371704723762156645813583 8057557085643234968720375)
        ·
          refine ⟨12086335628464852453080563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057557085643234968720375 12086335628464852453080563)
          ·
            refine ⟨18129503442697278679620845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086335628464852453080563 18129503442697278679620845)
            ·
              refine ⟨6798563791011479504857817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18129503442697278679620845 6798563791011479504857817)
              ·
                refine ⟨5098922843258609628643363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798563791011479504857817 5098922843258609628643363)
                ·
                  refine ⟨7648384264887914442965045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098922843258609628643363 7648384264887914442965045)
                  ·
                    refine ⟨717036024833241979027973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7648384264887914442965045 717036024833241979027973)
                    ·
                      rfl

theorem cell22_2094634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2094634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094634 prefixEnd_2094634 := by exact prefixLift 2094634
  have htrace : WordTrace (prefixWord ++ tailWord_2094634) baseStart_2094634 baseEnd_2094634 := by
    simpa [prefixWord, tailWord_2094634, baseEnd_2094634] using wordTrace_append hprefix tailTrace_2094634
  have hstable : (prefixWord ++ tailWord_2094634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094634).length < 2 ^ (prefixWord ++ tailWord_2094634).sum := by decide
  have hdescent : baseEnd_2094634 < baseStart_2094634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094638 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2094638 : Nat := 118140960795 + 2094638 * 2 ^ 59
def prefixEnd_2094638 : Nat := 4983230072969 + 3 ^ 40 * 2094638 * 2
def baseEnd_2094638 : Nat := 717037394114987301927961

theorem tailTrace_2094638 : CollatzResearch.WordTrace tailWord_2094638 prefixEnd_2094638 717037394114987301927961 := by
  unfold tailWord_2094638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549715523186467066839571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50931816123661157689811045 9549715523186467066839571)
  ·
    refine ⟨14324573284779700600259357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9549715523186467066839571 14324573284779700600259357)
    ·
      refine ⟨5371714981792387725097259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14324573284779700600259357 5371714981792387725097259)
      ·
        refine ⟨8057572472688581587645889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371714981792387725097259 8057572472688581587645889)
        ·
          refine ⟨6043179354516436190734417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8057572472688581587645889 6043179354516436190734417)
          ·
            refine ⟨4532384515887327143050813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6043179354516436190734417 4532384515887327143050813)
            ·
              refine ⟨1699644193457747678644055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4532384515887327143050813 1699644193457747678644055)
              ·
                refine ⟨2549466290186621517966083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699644193457747678644055 2549466290186621517966083)
                ·
                  refine ⟨3824199435279932276949125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549466290186621517966083 3824199435279932276949125)
                  ·
                    refine ⟨717037394114987301927961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824199435279932276949125 717037394114987301927961)
                    ·
                      rfl

theorem cell22_2094638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2094638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094638 prefixEnd_2094638 := by exact prefixLift 2094638
  have htrace : WordTrace (prefixWord ++ tailWord_2094638) baseStart_2094638 baseEnd_2094638 := by
    simpa [prefixWord, tailWord_2094638, baseEnd_2094638] using wordTrace_append hprefix tailTrace_2094638
  have hstable : (prefixWord ++ tailWord_2094638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094638).length < 2 ^ (prefixWord ++ tailWord_2094638).sum := by decide
  have hdescent : baseEnd_2094638 < baseStart_2094638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094649 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_2094649 : Nat := 118140960795 + 2094649 * 2 ^ 59
def prefixEnd_2094649 : Nat := 4983230072969 + 3 ^ 40 * 2094649 * 2
def baseEnd_2094649 : Nat := 717041159639786939902927

theorem tailTrace_2094649 : CollatzResearch.WordTrace tailWord_2094649 prefixEnd_2094649 717041159639786939902927 := by
  unfold tailWord_2094649
  simp only [CollatzResearch.WordTrace]
  refine ⟨76398125388451885413367001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50932083592301256942244667 76398125388451885413367001)
  ·
    refine ⟨57298594041338914060025251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76398125388451885413367001 57298594041338914060025251)
    ·
      refine ⟨85947891062008371090037877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57298594041338914060025251 85947891062008371090037877)
      ·
        refine ⟨8057614787063284789691051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85947891062008371090037877 8057614787063284789691051)
        ·
          refine ⟨12086422180594927184536577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057614787063284789691051 12086422180594927184536577)
          ·
            refine ⟨9064816635446195388402433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086422180594927184536577 9064816635446195388402433)
            ·
              refine ⟨6798612476584646541301825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9064816635446195388402433 6798612476584646541301825)
              ·
                refine ⟨5098959357438484905976369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798612476584646541301825 5098959357438484905976369)
                ·
                  refine ⟨3824219518078863679482277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098959357438484905976369 3824219518078863679482277)
                  ·
                    refine ⟨717041159639786939902927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824219518078863679482277 717041159639786939902927)
                    ·
                      rfl

theorem cell22_2094649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_2094649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094649 prefixEnd_2094649 := by exact prefixLift 2094649
  have htrace : WordTrace (prefixWord ++ tailWord_2094649) baseStart_2094649 baseEnd_2094649 := by
    simpa [prefixWord, tailWord_2094649, baseEnd_2094649] using wordTrace_append hprefix tailTrace_2094649
  have hstable : (prefixWord ++ tailWord_2094649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094649).length < 2 ^ (prefixWord ++ tailWord_2094649).sum := by decide
  have hdescent : baseEnd_2094649 < baseStart_2094649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094677 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2094677 : Nat := 118140960795 + 2094677 * 2 ^ 59
def prefixEnd_2094677 : Nat := 4983230072969 + 3 ^ 40 * 2094677 * 2
def baseEnd_2094677 : Nat := 717050744612004200202841

theorem tailTrace_2094677 : CollatzResearch.WordTrace tailWord_2094677 prefixEnd_2094677 717050744612004200202841 := by
  unfold tailWord_2094677
  simp only [CollatzResearch.WordTrace]
  refine ⟨76399146632350446195386285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50932764421566964130257523 76399146632350446195386285)
  ·
    refine ⟨28649679987131417323269857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76399146632350446195386285 28649679987131417323269857)
    ·
      refine ⟨21487259990348562992452393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28649679987131417323269857 21487259990348562992452393)
      ·
        refine ⟨16115444992761422244339295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21487259990348562992452393 16115444992761422244339295)
        ·
          refine ⟨24173167489142133366508943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16115444992761422244339295 24173167489142133366508943)
          ·
            refine ⟨36259751233713200049763415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24173167489142133366508943 36259751233713200049763415)
            ·
              refine ⟨54389626850569800074645123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36259751233713200049763415 54389626850569800074645123)
              ·
                refine ⟨81584440275854700111967685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54389626850569800074645123 81584440275854700111967685)
                ·
                  refine ⟨15297082551722756270993941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81584440275854700111967685 15297082551722756270993941)
                  ·
                    refine ⟨717050744612004200202841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15297082551722756270993941 717050744612004200202841)
                    ·
                      rfl

theorem cell22_2094677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2094677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094677 prefixEnd_2094677 := by exact prefixLift 2094677
  have htrace : WordTrace (prefixWord ++ tailWord_2094677) baseStart_2094677 baseEnd_2094677 := by
    simpa [prefixWord, tailWord_2094677, baseEnd_2094677] using wordTrace_append hprefix tailTrace_2094677
  have hstable : (prefixWord ++ tailWord_2094677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094677).length < 2 ^ (prefixWord ++ tailWord_2094677).sum := by decide
  have hdescent : baseEnd_2094677 < baseStart_2094677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094679 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 5, 3]
def baseStart_2094679 : Nat := 118140960795 + 2094679 * 2 ^ 59
def prefixEnd_2094679 : Nat := 4983230072969 + 3 ^ 40 * 2094679 * 2
def baseEnd_2094679 : Nat := 717051429252876861652835

theorem tailTrace_2094679 : CollatzResearch.WordTrace tailWord_2094679 prefixEnd_2094679 717051429252876861652835 := by
  unfold tailWord_2094679
  simp only [CollatzResearch.WordTrace]
  refine ⟨76399219578343200536959091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50932813052228800357972727 76399219578343200536959091)
  ·
    refine ⟨114598829367514800805438637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76399219578343200536959091 114598829367514800805438637)
    ·
      refine ⟨42974561012818050302039489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114598829367514800805438637 42974561012818050302039489)
      ·
        refine ⟨32230920759613537726529617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42974561012818050302039489 32230920759613537726529617)
        ·
          refine ⟨24173190569710153294897213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32230920759613537726529617 24173190569710153294897213)
          ·
            refine ⟨9064946463641307485586455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24173190569710153294897213 9064946463641307485586455)
            ·
              refine ⟨13597419695461961228379683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064946463641307485586455 13597419695461961228379683)
              ·
                refine ⟨20396129543192941842569525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597419695461961228379683 20396129543192941842569525)
                ·
                  refine ⟨1912137144674338297740893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20396129543192941842569525 1912137144674338297740893)
                  ·
                    refine ⟨717051429252876861652835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912137144674338297740893 717051429252876861652835)
                    ·
                      rfl

theorem cell22_2094679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_2094679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094679 prefixEnd_2094679 := by exact prefixLift 2094679
  have htrace : WordTrace (prefixWord ++ tailWord_2094679) baseStart_2094679 baseEnd_2094679 := by
    simpa [prefixWord, tailWord_2094679, baseEnd_2094679] using wordTrace_append hprefix tailTrace_2094679
  have hstable : (prefixWord ++ tailWord_2094679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094679).length < 2 ^ (prefixWord ++ tailWord_2094679).sum := by decide
  have hdescent : baseEnd_2094679 < baseStart_2094679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094737 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 8]
def baseStart_2094737 : Nat := 118140960795 + 2094737 * 2 ^ 59
def prefixEnd_2094737 : Nat := 4983230072969 + 3 ^ 40 * 2094737 * 2
def baseEnd_2094737 : Nat := 239023761279394681234219

theorem tailTrace_2094737 : CollatzResearch.WordTrace tailWord_2094737 prefixEnd_2094737 239023761279394681234219 := by
  unfold tailWord_2094737
  simp only [CollatzResearch.WordTrace]
  refine ⟨76401335012133076442570465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50934223341422050961713643 76401335012133076442570465)
  ·
    refine ⟨57301001259099807331927849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76401335012133076442570465 57301001259099807331927849)
    ·
      refine ⟨42975750944324855498945887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57301001259099807331927849 42975750944324855498945887)
      ·
        refine ⟨64463626416487283248418831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42975750944324855498945887 64463626416487283248418831)
        ·
          refine ⟨96695439624730924872628247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64463626416487283248418831 96695439624730924872628247)
          ·
            refine ⟨145043159437096387308942371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96695439624730924872628247 145043159437096387308942371)
            ·
              refine ⟨217564739155644580963413557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145043159437096387308942371 217564739155644580963413557)
              ·
                refine ⟨20396694295841679465320021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217564739155644580963413557 20396694295841679465320021)
                ·
                  refine ⟨239023761279394681234219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20396694295841679465320021 239023761279394681234219)
                  ·
                    rfl

theorem cell22_2094737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_2094737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094737 prefixEnd_2094737 := by exact prefixLift 2094737
  have htrace : WordTrace (prefixWord ++ tailWord_2094737) baseStart_2094737 baseEnd_2094737 := by
    simpa [prefixWord, tailWord_2094737, baseEnd_2094737] using wordTrace_append hprefix tailTrace_2094737
  have hstable : (prefixWord ++ tailWord_2094737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094737).length < 2 ^ (prefixWord ++ tailWord_2094737).sum := by decide
  have hdescent : baseEnd_2094737 < baseStart_2094737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094756 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_2094756 : Nat := 118140960795 + 2094756 * 2 ^ 59
def prefixEnd_2094756 : Nat := 4983230072969 + 3 ^ 40 * 2094756 * 2
def baseEnd_2094756 : Nat := 717077787926474327477599

theorem tailTrace_2094756 : CollatzResearch.WordTrace tailWord_2094756 prefixEnd_2094756 717077787926474327477599 := by
  unfold tailWord_2094756
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201013999532121343756061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50934685332709495125008081 38201013999532121343756061)
  ·
    refine ⟨14325380249824545503908523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38201013999532121343756061 14325380249824545503908523)
    ·
      refine ⟨21488070374736818255862785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14325380249824545503908523 21488070374736818255862785)
      ·
        refine ⟨16116052781052613691897089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21488070374736818255862785 16116052781052613691897089)
        ·
          refine ⟨12087039585789460268922817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16116052781052613691897089 12087039585789460268922817)
          ·
            refine ⟨9065279689342095201692113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087039585789460268922817 9065279689342095201692113)
            ·
              refine ⟨6798959767006571401269085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065279689342095201692113 6798959767006571401269085)
              ·
                refine ⟨2549609912627464275475907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6798959767006571401269085 2549609912627464275475907)
                ·
                  refine ⟨3824414868941196413213861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549609912627464275475907 3824414868941196413213861)
                  ·
                    refine ⟨717077787926474327477599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824414868941196413213861 717077787926474327477599)
                    ·
                      rfl

theorem cell22_2094756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_2094756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094756 prefixEnd_2094756 := by exact prefixLift 2094756
  have htrace : WordTrace (prefixWord ++ tailWord_2094756) baseStart_2094756 baseEnd_2094756 := by
    simpa [prefixWord, tailWord_2094756, baseEnd_2094756] using wordTrace_append hprefix tailTrace_2094756
  have hstable : (prefixWord ++ tailWord_2094756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094756).length < 2 ^ (prefixWord ++ tailWord_2094756).sum := by decide
  have hdescent : baseEnd_2094756 < baseStart_2094756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094784 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_2094784 : Nat := 118140960795 + 2094784 * 2 ^ 59
def prefixEnd_2094784 : Nat := 4983230072969 + 3 ^ 40 * 2094784 * 2
def baseEnd_2094784 : Nat := 717087372898691587777513

theorem tailTrace_2094784 : CollatzResearch.WordTrace tailWord_2094784 prefixEnd_2094784 717087372898691587777513 := by
  unfold tailWord_2094784
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201524621481401734765703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50935366161975202313020937 38201524621481401734765703)
  ·
    refine ⟨57302286932222102602148555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38201524621481401734765703 57302286932222102602148555)
    ·
      refine ⟨85953430398333153903222833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57302286932222102602148555 85953430398333153903222833)
      ·
        refine ⟨64465072798749865427417125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85953430398333153903222833 64465072798749865427417125)
        ·
          refine ⟨12087201149765599767640711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64465072798749865427417125 12087201149765599767640711)
          ·
            refine ⟨18130801724648399651461067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12087201149765599767640711 18130801724648399651461067)
            ·
              refine ⟨27196202586972599477191601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18130801724648399651461067 27196202586972599477191601)
              ·
                refine ⟨20397151940229449607893701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27196202586972599477191601 20397151940229449607893701)
                ·
                  refine ⟨3824465988793021801480069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20397151940229449607893701 3824465988793021801480069)
                  ·
                    refine ⟨717087372898691587777513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824465988793021801480069 717087372898691587777513)
                    ·
                      rfl

theorem cell22_2094784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_2094784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094784 prefixEnd_2094784 := by exact prefixLift 2094784
  have htrace : WordTrace (prefixWord ++ tailWord_2094784) baseStart_2094784 baseEnd_2094784 := by
    simpa [prefixWord, tailWord_2094784, baseEnd_2094784] using wordTrace_append hprefix tailTrace_2094784
  have hstable : (prefixWord ++ tailWord_2094784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094784).length < 2 ^ (prefixWord ++ tailWord_2094784).sum := by decide
  have hdescent : baseEnd_2094784 < baseStart_2094784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094790 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2094790 : Nat := 118140960795 + 2094790 * 2 ^ 59
def prefixEnd_2094790 : Nat := 4983230072969 + 3 ^ 40 * 2094790 * 2
def baseEnd_2094790 : Nat := 717089426821309572127495

theorem tailTrace_2094790 : CollatzResearch.WordTrace tailWord_2094790 prefixEnd_2094790 717089426821309572127495 := by
  unfold tailWord_2094790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387602127529408327945307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50935512053960710996166549 2387602127529408327945307)
  ·
    refine ⟨3581403191294112491917961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2387602127529408327945307 3581403191294112491917961)
    ·
      refine ⟨2686052393470584368938471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3581403191294112491917961 2686052393470584368938471)
      ·
        refine ⟨4029078590205876553407707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2686052393470584368938471 4029078590205876553407707)
        ·
          refine ⟨6043617885308814830111561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029078590205876553407707 6043617885308814830111561)
          ·
            refine ⟨4532713413981611122583671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6043617885308814830111561 4532713413981611122583671)
            ·
              refine ⟨6799070120972416683875507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532713413981611122583671 6799070120972416683875507)
              ·
                refine ⟨10198605181458625025813261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799070120972416683875507 10198605181458625025813261)
                ·
                  refine ⟨3824476943046984384679973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10198605181458625025813261 3824476943046984384679973)
                  ·
                    refine ⟨717089426821309572127495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824476943046984384679973 717089426821309572127495)
                    ·
                      rfl

theorem cell22_2094790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2094790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094790 prefixEnd_2094790 := by exact prefixLift 2094790
  have htrace : WordTrace (prefixWord ++ tailWord_2094790) baseStart_2094790 baseEnd_2094790 := by
    simpa [prefixWord, tailWord_2094790, baseEnd_2094790] using wordTrace_append hprefix tailTrace_2094790
  have hstable : (prefixWord ++ tailWord_2094790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094790).length < 2 ^ (prefixWord ++ tailWord_2094790).sum := by decide
  have hdescent : baseEnd_2094790 < baseStart_2094790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094801 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_2094801 : Nat := 118140960795 + 2094801 * 2 ^ 59
def prefixEnd_2094801 : Nat := 4983230072969 + 3 ^ 40 * 2094801 * 2
def baseEnd_2094801 : Nat := 717093192346109210102461

theorem tailTrace_2094801 : CollatzResearch.WordTrace tailWord_2094801 prefixEnd_2094801 717093192346109210102461 := by
  unfold tailWord_2094801
  simp only [CollatzResearch.WordTrace]
  refine ⟨76403669283901215372900257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50935779522600810248600171 76403669283901215372900257)
  ·
    refine ⟨57302751962925911529675193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76403669283901215372900257 57302751962925911529675193)
    ·
      refine ⟨42977063972194433647256395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57302751962925911529675193 42977063972194433647256395)
      ·
        refine ⟨64465595958291650470884593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42977063972194433647256395 64465595958291650470884593)
        ·
          refine ⟨48349196968718737853163445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64465595958291650470884593 48349196968718737853163445)
          ·
            refine ⟨4532737215817381673734073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48349196968718737853163445 4532737215817381673734073)
            ·
              refine ⟨3399552911863036255300555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4532737215817381673734073 3399552911863036255300555)
              ·
                refine ⟨5099329367794554382950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399552911863036255300555 5099329367794554382950833)
                ·
                  refine ⟨3824497025845915787213125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099329367794554382950833 3824497025845915787213125)
                  ·
                    refine ⟨717093192346109210102461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824497025845915787213125 717093192346109210102461)
                    ·
                      rfl

theorem cell22_2094801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_2094801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094801 prefixEnd_2094801 := by exact prefixLift 2094801
  have htrace : WordTrace (prefixWord ++ tailWord_2094801) baseStart_2094801 baseEnd_2094801 := by
    simpa [prefixWord, tailWord_2094801, baseEnd_2094801] using wordTrace_append hprefix tailTrace_2094801
  have hstable : (prefixWord ++ tailWord_2094801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094801).length < 2 ^ (prefixWord ++ tailWord_2094801).sum := by decide
  have hdescent : baseEnd_2094801 < baseStart_2094801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094831 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 3, 3]
def baseStart_2094831 : Nat := 118140960795 + 2094831 * 2 ^ 59
def prefixEnd_2094831 : Nat := 4983230072969 + 3 ^ 40 * 2094831 * 2
def baseEnd_2094831 : Nat := 717103461959199131852369

theorem tailTrace_2094831 : CollatzResearch.WordTrace tailWord_2094831 prefixEnd_2094831 717103461959199131852369 := by
  unfold tailWord_2094831
  simp only [CollatzResearch.WordTrace]
  refine ⟨76404763473792530496492347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50936508982528353664328231 76404763473792530496492347)
  ·
    refine ⟨114607145210688795744738521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76404763473792530496492347 114607145210688795744738521)
    ·
      refine ⟨85955358908016596808553891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114607145210688795744738521 85955358908016596808553891)
      ·
        refine ⟨128933038362024895212830837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85955358908016596808553891 128933038362024895212830837)
        ·
          refine ⟨12087472346439833926202891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128933038362024895212830837 12087472346439833926202891)
          ·
            refine ⟨18131208519659750889304337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12087472346439833926202891 18131208519659750889304337)
            ·
              refine ⟨13598406389744813166978253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18131208519659750889304337 13598406389744813166978253)
              ·
                refine ⟨5099402396154304937616845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13598406389744813166978253 5099402396154304937616845)
                ·
                  refine ⟨1912275898557864351606317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5099402396154304937616845 1912275898557864351606317)
                  ·
                    refine ⟨717103461959199131852369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912275898557864351606317 717103461959199131852369)
                    ·
                      rfl

theorem cell22_2094831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_2094831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094831 prefixEnd_2094831 := by exact prefixLift 2094831
  have htrace : WordTrace (prefixWord ++ tailWord_2094831) baseStart_2094831 baseEnd_2094831 := by
    simpa [prefixWord, tailWord_2094831, baseEnd_2094831] using wordTrace_append hprefix tailTrace_2094831
  have hstable : (prefixWord ++ tailWord_2094831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094831).length < 2 ^ (prefixWord ++ tailWord_2094831).sum := by decide
  have hdescent : baseEnd_2094831 < baseStart_2094831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094906 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_2094906 : Nat := 118140960795 + 2094906 * 2 ^ 59
def prefixEnd_2094906 : Nat := 4983230072969 + 3 ^ 40 * 2094906 * 2
def baseEnd_2094906 : Nat := 239043045330641312075713

theorem tailTrace_2094906 : CollatzResearch.WordTrace tailWord_2094906 prefixEnd_2094906 239043045330641312075713 := by
  unfold tailWord_2094906
  simp only [CollatzResearch.WordTrace]
  refine ⟨19101874737130204576368143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50938332632347212203648381 19101874737130204576368143)
  ·
    refine ⟨28652812105695306864552215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19101874737130204576368143 28652812105695306864552215)
    ·
      refine ⟨42979218158542960296828323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28652812105695306864552215 42979218158542960296828323)
      ·
        refine ⟨64468827237814440445242485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42979218158542960296828323 64468827237814440445242485)
        ·
          refine ⟨6043952553545103791741483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64468827237814440445242485 6043952553545103791741483)
          ·
            refine ⟨9065928830317655687612225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043952553545103791741483 9065928830317655687612225)
            ·
              refine ⟨6799446622738241765709169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065928830317655687612225 6799446622738241765709169)
              ·
                refine ⟨5099584967053681324281877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799446622738241765709169 5099584967053681324281877)
                ·
                  refine ⟨239043045330641312075713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5099584967053681324281877 239043045330641312075713)
                  ·
                    rfl

theorem cell22_2094906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_2094906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094906 prefixEnd_2094906 := by exact prefixLift 2094906
  have htrace : WordTrace (prefixWord ++ tailWord_2094906) baseStart_2094906 baseEnd_2094906 := by
    simpa [prefixWord, tailWord_2094906, baseEnd_2094906] using wordTrace_append hprefix tailTrace_2094906
  have hstable : (prefixWord ++ tailWord_2094906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094906).length < 2 ^ (prefixWord ++ tailWord_2094906).sum := by decide
  have hdescent : baseEnd_2094906 < baseStart_2094906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094921 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_2094921 : Nat := 118140960795 + 2094921 * 2 ^ 59
def prefixEnd_2094921 : Nat := 4983230072969 + 3 ^ 40 * 2094921 * 2
def baseEnd_2094921 : Nat := 717134270798468897102093

theorem tailTrace_2094921 : CollatzResearch.WordTrace tailWord_2094921 prefixEnd_2094921 717134270798468897102093 := by
  unfold tailWord_2094921
  simp only [CollatzResearch.WordTrace]
  refine ⟨76408046043466475867268617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50938697362310983911512411 76408046043466475867268617)
  ·
    refine ⟨57306034532599856900451463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76408046043466475867268617 57306034532599856900451463)
    ·
      refine ⟨85959051798899785350677195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57306034532599856900451463 85959051798899785350677195)
      ·
        refine ⟨128938577698349678026015793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85959051798899785350677195 128938577698349678026015793)
        ·
          refine ⟨96703933273762258519511845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128938577698349678026015793 96703933273762258519511845)
          ·
            refine ⟨18131987488830423472408471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96703933273762258519511845 18131987488830423472408471)
            ·
              refine ⟨27197981233245635208612707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18131987488830423472408471 27197981233245635208612707)
              ·
                refine ⟨40796971849868452812919061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27197981233245635208612707 40796971849868452812919061)
                ·
                  refine ⟨1912358055462583725605581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40796971849868452812919061 1912358055462583725605581)
                  ·
                    refine ⟨717134270798468897102093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912358055462583725605581 717134270798468897102093)
                    ·
                      rfl

theorem cell22_2094921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_2094921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094921 prefixEnd_2094921 := by exact prefixLift 2094921
  have htrace : WordTrace (prefixWord ++ tailWord_2094921) baseStart_2094921 baseEnd_2094921 := by
    simpa [prefixWord, tailWord_2094921, baseEnd_2094921] using wordTrace_append hprefix tailTrace_2094921
  have hstable : (prefixWord ++ tailWord_2094921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094921).length < 2 ^ (prefixWord ++ tailWord_2094921).sum := by decide
  have hdescent : baseEnd_2094921 < baseStart_2094921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094925 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2094925 : Nat := 118140960795 + 2094925 * 2 ^ 59
def prefixEnd_2094925 : Nat := 4983230072969 + 3 ^ 40 * 2094925 * 2
def baseEnd_2094925 : Nat := 717135640080214220002081

theorem tailTrace_2094925 : CollatzResearch.WordTrace tailWord_2094925 prefixEnd_2094925 717135640080214220002081 := by
  unfold tailWord_2094925
  simp only [CollatzResearch.WordTrace]
  refine ⟨76408191935451984550414229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50938794623634656366942819 76408191935451984550414229)
  ·
    refine ⟨3581633996974311775800667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76408191935451984550414229 3581633996974311775800667)
    ·
      refine ⟨5372450995461467663701001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581633996974311775800667 5372450995461467663701001)
      ·
        refine ⟨4029338246596100747775751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5372450995461467663701001 4029338246596100747775751)
        ·
          refine ⟨6044007369894151121663627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029338246596100747775751 6044007369894151121663627)
          ·
            refine ⟨9066011054841226682495441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044007369894151121663627 9066011054841226682495441)
            ·
              refine ⟨6799508291130920011871581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9066011054841226682495441 6799508291130920011871581)
              ·
                refine ⟨2549815609174095004451843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6799508291130920011871581 2549815609174095004451843)
                ·
                  refine ⟨3824723413761142506677765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549815609174095004451843 3824723413761142506677765)
                  ·
                    refine ⟨717135640080214220002081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824723413761142506677765 717135640080214220002081)
                    ·
                      rfl

theorem cell22_2094925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2094925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094925 prefixEnd_2094925 := by exact prefixLift 2094925
  have htrace : WordTrace (prefixWord ++ tailWord_2094925) baseStart_2094925 baseEnd_2094925 := by
    simpa [prefixWord, tailWord_2094925, baseEnd_2094925] using wordTrace_append hprefix tailTrace_2094925
  have hstable : (prefixWord ++ tailWord_2094925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094925).length < 2 ^ (prefixWord ++ tailWord_2094925).sum := by decide
  have hdescent : baseEnd_2094925 < baseStart_2094925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094938 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_2094938 : Nat := 118140960795 + 2094938 * 2 ^ 59
def prefixEnd_2094938 : Nat := 4983230072969 + 3 ^ 40 * 2094938 * 2
def baseEnd_2094938 : Nat := 717140090245886519427041

theorem tailTrace_2094938 : CollatzResearch.WordTrace tailWord_2094938 prefixEnd_2094938 717140090245886519427041 := by
  unfold tailWord_2094938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102166521101221942659367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50939110722936591847091645 19102166521101221942659367)
  ·
    refine ⟨28653249781651832913989051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19102166521101221942659367 28653249781651832913989051)
    ·
      refine ⟨42979874672477749370983577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28653249781651832913989051 42979874672477749370983577)
      ·
        refine ⟨32234906004358312028237683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42979874672477749370983577 32234906004358312028237683)
        ·
          refine ⟨48352359006537468042356525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32234906004358312028237683 48352359006537468042356525)
          ·
            refine ⟨18132134627451550515883697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48352359006537468042356525 18132134627451550515883697)
            ·
              refine ⟨13599100970588662886912773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18132134627451550515883697 13599100970588662886912773)
              ·
                refine ⟨2549831431985374291296145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13599100970588662886912773 2549831431985374291296145)
                ·
                  refine ⟨1912373573989030718472109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2549831431985374291296145 1912373573989030718472109)
                  ·
                    refine ⟨717140090245886519427041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912373573989030718472109 717140090245886519427041)
                    ·
                      rfl

theorem cell22_2094938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_2094938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094938 prefixEnd_2094938 := by exact prefixLift 2094938
  have htrace : WordTrace (prefixWord ++ tailWord_2094938) baseStart_2094938 baseEnd_2094938 := by
    simpa [prefixWord, tailWord_2094938, baseEnd_2094938] using wordTrace_append hprefix tailTrace_2094938
  have hstable : (prefixWord ++ tailWord_2094938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094938).length < 2 ^ (prefixWord ++ tailWord_2094938).sum := by decide
  have hdescent : baseEnd_2094938 < baseStart_2094938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094940 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 6]
def baseStart_2094940 : Nat := 118140960795 + 2094940 * 2 ^ 59
def prefixEnd_2094940 : Nat := 4983230072969 + 3 ^ 40 * 2094940 * 2
def baseEnd_2094940 : Nat := 239046924962253060292345

theorem tailTrace_2094940 : CollatzResearch.WordTrace tailWord_2094940 prefixEnd_2094940 239046924962253060292345 := by
  unfold tailWord_2094940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38204369515198821056105137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50939159353598428074806849 38204369515198821056105137)
  ·
    refine ⟨28653277136399115792078853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38204369515198821056105137 28653277136399115792078853)
    ·
      refine ⟨5372489463074834211014785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28653277136399115792078853 5372489463074834211014785)
      ·
        refine ⟨4029367097306125658261089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5372489463074834211014785 4029367097306125658261089)
        ·
          refine ⟨3022025322979594243695817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4029367097306125658261089 3022025322979594243695817)
          ·
            refine ⟨2266518992234695682771863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3022025322979594243695817 2266518992234695682771863)
            ·
              refine ⟨3399778488352043524157795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266518992234695682771863 3399778488352043524157795)
              ·
                refine ⟨5099667732528065286236693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399778488352043524157795 5099667732528065286236693)
                ·
                  refine ⟨239046924962253060292345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5099667732528065286236693 239046924962253060292345)
                  ·
                    rfl

theorem cell22_2094940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_2094940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094940 prefixEnd_2094940 := by exact prefixLift 2094940
  have htrace : WordTrace (prefixWord ++ tailWord_2094940) baseStart_2094940 baseEnd_2094940 := by
    simpa [prefixWord, tailWord_2094940, baseEnd_2094940] using wordTrace_append hprefix tailTrace_2094940
  have hstable : (prefixWord ++ tailWord_2094940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094940).length < 2 ^ (prefixWord ++ tailWord_2094940).sum := by decide
  have hdescent : baseEnd_2094940 < baseStart_2094940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094951 : List Nat := [1, 1, 5, 1, 2, 1, 4, 7]
def baseStart_2094951 : Nat := 118140960795 + 2094951 * 2 ^ 59
def prefixEnd_2094951 : Nat := 4983230072969 + 3 ^ 40 * 2094951 * 2
def baseEnd_2094951 : Nat := 79682726712395424316889

theorem tailTrace_2094951 : CollatzResearch.WordTrace tailWord_2094951 prefixEnd_2094951 79682726712395424316889 := by
  unfold tailWord_2094951
  simp only [CollatzResearch.WordTrace]
  refine ⟨76409140233357790990860707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50939426822238527327240471 76409140233357790990860707)
  ·
    refine ⟨114613710350036686486291061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76409140233357790990860707 114613710350036686486291061)
    ·
      refine ⟨10745035345315939358089787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114613710350036686486291061 10745035345315939358089787)
      ·
        refine ⟨16117553017973909037134681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10745035345315939358089787 16117553017973909037134681)
        ·
          refine ⟨12088164763480431777851011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16117553017973909037134681 12088164763480431777851011)
          ·
            refine ⟨18132247145220647666776517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12088164763480431777851011 18132247145220647666776517)
            ·
              refine ⟨3399796339728871437520597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18132247145220647666776517 3399796339728871437520597)
              ·
                refine ⟨79682726712395424316889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3399796339728871437520597 79682726712395424316889)
                ·
                  rfl

theorem cell22_2094951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 7].length) (baseStart_2094951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2094951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2094951 prefixEnd_2094951 := by exact prefixLift 2094951
  have htrace : WordTrace (prefixWord ++ tailWord_2094951) baseStart_2094951 baseEnd_2094951 := by
    simpa [prefixWord, tailWord_2094951, baseEnd_2094951] using wordTrace_append hprefix tailTrace_2094951
  have hstable : (prefixWord ++ tailWord_2094951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094951).length < 2 ^ (prefixWord ++ tailWord_2094951).sum := by decide
  have hdescent : baseEnd_2094951 < baseStart_2094951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095056 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_2095056 : Nat := 118140960795 + 2095056 * 2 ^ 59
def prefixEnd_2095056 : Nat := 4983230072969 + 3 ^ 40 * 2095056 * 2
def baseEnd_2095056 : Nat := 717180484057373544976679

theorem tailTrace_2095056 : CollatzResearch.WordTrace tailWord_2095056 prefixEnd_2095056 717180484057373544976679 := by
  unfold tailWord_2095056
  simp only [CollatzResearch.WordTrace]
  refine ⟨38206484948988696961716511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50941979931984929282288681 38206484948988696961716511)
  ·
    refine ⟨57309727423483045442574767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38206484948988696961716511 57309727423483045442574767)
    ·
      refine ⟨85964591135224568163862151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57309727423483045442574767 85964591135224568163862151)
      ·
        refine ⟨128946886702836852245793227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85964591135224568163862151 128946886702836852245793227)
        ·
          refine ⟨193420330054255278368689841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128946886702836852245793227 193420330054255278368689841)
          ·
            refine ⟨145065247540691458776517381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193420330054255278368689841 145065247540691458776517381)
            ·
              refine ⟨27199733913879648520597009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145065247540691458776517381 27199733913879648520597009)
              ·
                refine ⟨20399800435409736390447757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27199733913879648520597009 20399800435409736390447757)
                ·
                  refine ⟨7649925163278651146417909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20399800435409736390447757 7649925163278651146417909)
                  ·
                    refine ⟨717180484057373544976679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7649925163278651146417909 717180484057373544976679)
                    ·
                      rfl

theorem cell22_2095056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_2095056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095056 prefixEnd_2095056 := by exact prefixLift 2095056
  have htrace : WordTrace (prefixWord ++ tailWord_2095056) baseStart_2095056 baseEnd_2095056 := by
    simpa [prefixWord, tailWord_2095056, baseEnd_2095056] using wordTrace_append hprefix tailTrace_2095056
  have hstable : (prefixWord ++ tailWord_2095056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095056).length < 2 ^ (prefixWord ++ tailWord_2095056).sum := by decide
  have hdescent : baseEnd_2095056 < baseStart_2095056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095073 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_2095073 : Nat := 118140960795 + 2095073 * 2 ^ 59
def prefixEnd_2095073 : Nat := 4983230072969 + 3 ^ 40 * 2095073 * 2
def baseEnd_2095073 : Nat := 717186303504791167301627

theorem tailTrace_2095073 : CollatzResearch.WordTrace tailWord_2095073 prefixEnd_2095073 717186303504791167301627 := by
  unfold tailWord_2095073
  simp only [CollatzResearch.WordTrace]
  refine ⟨76413589938915805826801873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50942393292610537217867915 76413589938915805826801873)
  ·
    refine ⟨57310192454186854370101405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76413589938915805826801873 57310192454186854370101405)
    ·
      refine ⟨21491322170320070388788027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57310192454186854370101405 21491322170320070388788027)
      ·
        refine ⟨32236983255480105583182041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21491322170320070388788027 32236983255480105583182041)
        ·
          refine ⟨24177737441610079187386531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32236983255480105583182041 24177737441610079187386531)
          ·
            refine ⟨36266606162415118781079797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24177737441610079187386531 36266606162415118781079797)
            ·
              refine ⟨3399994327726417385726231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36266606162415118781079797 3399994327726417385726231)
              ·
                refine ⟨5099991491589626078589347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399994327726417385726231 5099991491589626078589347)
                ·
                  refine ⟨7649987237384439117884021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099991491589626078589347 7649987237384439117884021)
                  ·
                    refine ⟨717186303504791167301627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7649987237384439117884021 717186303504791167301627)
                    ·
                      rfl

theorem cell22_2095073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_2095073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095073 prefixEnd_2095073 := by exact prefixLift 2095073
  have htrace : WordTrace (prefixWord ++ tailWord_2095073) baseStart_2095073 baseEnd_2095073 := by
    simpa [prefixWord, tailWord_2095073, baseEnd_2095073] using wordTrace_append hprefix tailTrace_2095073
  have hstable : (prefixWord ++ tailWord_2095073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095073).length < 2 ^ (prefixWord ++ tailWord_2095073).sum := by decide
  have hdescent : baseEnd_2095073 < baseStart_2095073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095131 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 9]
def baseStart_2095131 : Nat := 118140960795 + 2095131 * 2 ^ 59
def prefixEnd_2095131 : Nat := 4983230072969 + 3 ^ 40 * 2095131 * 2
def baseEnd_2095131 : Nat := 239068719363366116450483

theorem tailTrace_2095131 : CollatzResearch.WordTrace tailWord_2095131 prefixEnd_2095131 239068719363366116450483 := by
  unfold tailWord_2095131
  simp only [CollatzResearch.WordTrace]
  refine ⟨76415705372705681732413247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50943803581803787821608831 76415705372705681732413247)
  ·
    refine ⟨114623558059058522598619871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76415705372705681732413247 114623558059058522598619871)
    ·
      refine ⟨171935337088587783897929807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114623558059058522598619871 171935337088587783897929807)
      ·
        refine ⟨257903005632881675846894711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171935337088587783897929807 257903005632881675846894711)
        ·
          refine ⟨386854508449322513770342067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257903005632881675846894711 386854508449322513770342067)
          ·
            refine ⟨580281762673983770655513101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386854508449322513770342067 580281762673983770655513101)
            ·
              refine ⟨217605661002743913995817413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580281762673983770655513101 217605661002743913995817413)
              ·
                refine ⟨40801061438014483874215765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217605661002743913995817413 40801061438014483874215765)
                ·
                  refine ⟨239068719363366116450483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40801061438014483874215765 239068719363366116450483)
                  ·
                    rfl

theorem cell22_2095131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_2095131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095131 prefixEnd_2095131 := by exact prefixLift 2095131
  have htrace : WordTrace (prefixWord ++ tailWord_2095131) baseStart_2095131 baseEnd_2095131 := by
    simpa [prefixWord, tailWord_2095131, baseEnd_2095131] using wordTrace_append hprefix tailTrace_2095131
  have hstable : (prefixWord ++ tailWord_2095131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095131).length < 2 ^ (prefixWord ++ tailWord_2095131).sum := by decide
  have hdescent : baseEnd_2095131 < baseStart_2095131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095165 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 5]
def baseStart_2095165 : Nat := 118140960795 + 2095165 * 2 ^ 59
def prefixEnd_2095165 : Nat := 4983230072969 + 3 ^ 40 * 2095165 * 2
def baseEnd_2095165 : Nat := 239072598994977864667115

theorem tailTrace_2095165 : CollatzResearch.WordTrace tailWord_2095165 prefixEnd_2095165 239072598994977864667115 := by
  unfold tailWord_2095165
  simp only [CollatzResearch.WordTrace]
  refine ⟨76416945454582505539150949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50944630303055003692767299 76416945454582505539150949)
  ·
    refine ⟨14328177272734219788590803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76416945454582505539150949 14328177272734219788590803)
    ·
      refine ⟨21492265909101329682886205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14328177272734219788590803 21492265909101329682886205)
      ·
        refine ⟨8059599715912998631082327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21492265909101329682886205 8059599715912998631082327)
        ·
          refine ⟨12089399573869497946623491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059599715912998631082327 12089399573869497946623491)
          ·
            refine ⟨18134099360804246919935237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089399573869497946623491 18134099360804246919935237)
            ·
              refine ⟨3400143630150796297487857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18134099360804246919935237 3400143630150796297487857)
              ·
                refine ⟨2550107722613097223115893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400143630150796297487857 2550107722613097223115893)
                ·
                  refine ⟨239072598994977864667115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2550107722613097223115893 239072598994977864667115)
                  ·
                    rfl

theorem cell22_2095165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_2095165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095165 prefixEnd_2095165 := by exact prefixLift 2095165
  have htrace : WordTrace (prefixWord ++ tailWord_2095165) baseStart_2095165 baseEnd_2095165 := by
    simpa [prefixWord, tailWord_2095165, baseEnd_2095165] using wordTrace_append hprefix tailTrace_2095165
  have hstable : (prefixWord ++ tailWord_2095165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095165).length < 2 ^ (prefixWord ++ tailWord_2095165).sum := by decide
  have hdescent : baseEnd_2095165 < baseStart_2095165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095169 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2095169 : Nat := 118140960795 + 2095169 * 2 ^ 59
def prefixEnd_2095169 : Nat := 4983230072969 + 3 ^ 40 * 2095169 * 2
def baseEnd_2095169 : Nat := 717219166266678916901333

theorem tailTrace_2095169 : CollatzResearch.WordTrace tailWord_2095169 prefixEnd_2095169 717219166266678916901333 := by
  unfold tailWord_2095169
  simp only [CollatzResearch.WordTrace]
  refine ⟨76417091346568014222296561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50944727564378676148197707 76417091346568014222296561)
  ·
    refine ⟨57312818509926010666722421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76417091346568014222296561 57312818509926010666722421)
    ·
      refine ⟨5373076735305563500005227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57312818509926010666722421 5373076735305563500005227)
      ·
        refine ⟨8059615102958345250007841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373076735305563500005227 8059615102958345250007841)
        ·
          refine ⟨6044711327218758937505881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8059615102958345250007841 6044711327218758937505881)
          ·
            refine ⟨4533533495414069203129411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6044711327218758937505881 4533533495414069203129411)
            ·
              refine ⟨6800300243121103804694117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533533495414069203129411 6800300243121103804694117)
              ·
                refine ⟨1275056295585206963380147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6800300243121103804694117 1275056295585206963380147)
                ·
                  refine ⟨1912584443377810445070221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275056295585206963380147 1912584443377810445070221)
                  ·
                    refine ⟨717219166266678916901333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912584443377810445070221 717219166266678916901333)
                    ·
                      rfl

theorem cell22_2095169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2095169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095169 prefixEnd_2095169 := by exact prefixLift 2095169
  have htrace : WordTrace (prefixWord ++ tailWord_2095169) baseStart_2095169 baseEnd_2095169 := by
    simpa [prefixWord, tailWord_2095169, baseEnd_2095169] using wordTrace_append hprefix tailTrace_2095169
  have hstable : (prefixWord ++ tailWord_2095169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095169).length < 2 ^ (prefixWord ++ tailWord_2095169).sum := by decide
  have hdescent : baseEnd_2095169 < baseStart_2095169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095193 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 6]
def baseStart_2095193 : Nat := 118140960795 + 2095193 * 2 ^ 59
def prefixEnd_2095193 : Nat := 4983230072969 + 3 ^ 40 * 2095193 * 2
def baseEnd_2095193 : Nat := 239075793985716951433753

theorem tailTrace_2095193 : CollatzResearch.WordTrace tailWord_2095193 prefixEnd_2095193 239075793985716951433753 := by
  unfold tailWord_2095193
  simp only [CollatzResearch.WordTrace]
  refine ⟨76417966698481066321170233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50945311132320710880780155 76417966698481066321170233)
  ·
    refine ⟨57313475023860799740877675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76417966698481066321170233 57313475023860799740877675)
    ·
      refine ⟨85970212535791199611316513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57313475023860799740877675 85970212535791199611316513)
      ·
        refine ⟨64477659401843399708487385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85970212535791199611316513 64477659401843399708487385)
        ·
          refine ⟨48358244551382549781365539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64477659401843399708487385 48358244551382549781365539)
          ·
            refine ⟨72537366827073824672048309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48358244551382549781365539 72537366827073824672048309)
            ·
              refine ⟨6800378140038171063004529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72537366827073824672048309 6800378140038171063004529)
              ·
                refine ⟨5100283605028628297253397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800378140038171063004529 5100283605028628297253397)
                ·
                  refine ⟨239075793985716951433753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5100283605028628297253397 239075793985716951433753)
                  ·
                    rfl

theorem cell22_2095193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_2095193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095193 prefixEnd_2095193 := by exact prefixLift 2095193
  have htrace : WordTrace (prefixWord ++ tailWord_2095193) baseStart_2095193 baseEnd_2095193 := by
    simpa [prefixWord, tailWord_2095193, baseEnd_2095193] using wordTrace_append hprefix tailTrace_2095193
  have hstable : (prefixWord ++ tailWord_2095193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095193).length < 2 ^ (prefixWord ++ tailWord_2095193).sum := by decide
  have hdescent : baseEnd_2095193 < baseStart_2095193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095212 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_2095212 : Nat := 118140960795 + 2095212 * 2 ^ 59
def prefixEnd_2095212 : Nat := 4983230072969 + 3 ^ 40 * 2095212 * 2
def baseEnd_2095212 : Nat := 717233886045441138076201

theorem tailTrace_2095212 : CollatzResearch.WordTrace tailWord_2095212 prefixEnd_2095212 717233886045441138076201 := by
  unfold tailWord_2095212
  simp only [CollatzResearch.WordTrace]
  refine ⟨38209329842706116283055945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50945773123608155044074593 38209329842706116283055945)
  ·
    refine ⟨28656997382029587212291959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38209329842706116283055945 28656997382029587212291959)
    ·
      refine ⟨42985496073044380818437939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28656997382029587212291959 42985496073044380818437939)
      ·
        refine ⟨64478244109566571227656909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42985496073044380818437939 64478244109566571227656909)
        ·
          refine ⟨24179341541087464210371341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64478244109566571227656909 24179341541087464210371341)
          ·
            refine ⟨9067253077907799078889253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24179341541087464210371341 9067253077907799078889253)
            ·
              refine ⟨1700109952107712327291735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9067253077907799078889253 1700109952107712327291735)
              ·
                refine ⟨2550164928161568490937603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700109952107712327291735 2550164928161568490937603)
                ·
                  refine ⟨3825247392242352736406405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550164928161568490937603 3825247392242352736406405)
                  ·
                    refine ⟨717233886045441138076201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825247392242352736406405 717233886045441138076201)
                    ·
                      rfl

theorem cell22_2095212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_2095212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095212 prefixEnd_2095212 := by exact prefixLift 2095212
  have htrace : WordTrace (prefixWord ++ tailWord_2095212) baseStart_2095212 baseEnd_2095212 := by
    simpa [prefixWord, tailWord_2095212, baseEnd_2095212] using wordTrace_append hprefix tailTrace_2095212
  have hstable : (prefixWord ++ tailWord_2095212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095212).length < 2 ^ (prefixWord ++ tailWord_2095212).sum := by decide
  have hdescent : baseEnd_2095212 < baseStart_2095212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095240 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_2095240 : Nat := 118140960795 + 2095240 * 2 ^ 59
def prefixEnd_2095240 : Nat := 4983230072969 + 3 ^ 40 * 2095240 * 2
def baseEnd_2095240 : Nat := 717243471017658398376115

theorem tailTrace_2095240 : CollatzResearch.WordTrace tailWord_2095240 prefixEnd_2095240 717243471017658398376115 := by
  unfold tailWord_2095240
  simp only [CollatzResearch.WordTrace]
  refine ⟨38209840464655396674065587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50946453952873862232087449 38209840464655396674065587)
  ·
    refine ⟨57314760696983095011098381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38209840464655396674065587 57314760696983095011098381)
    ·
      refine ⟨21493035261368660629161893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57314760696983095011098381 21493035261368660629161893)
      ·
        refine ⟨4029944111506623867967855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21493035261368660629161893 4029944111506623867967855)
        ·
          refine ⟨6044916167259935801951783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029944111506623867967855 6044916167259935801951783)
          ·
            refine ⟨9067374250889903702927675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044916167259935801951783 9067374250889903702927675)
            ·
              refine ⟨13601061376334855554391513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067374250889903702927675 13601061376334855554391513)
              ·
                refine ⟨10200796032251141665793635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13601061376334855554391513 10200796032251141665793635)
                ·
                  refine ⟨15301194048376712498690453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200796032251141665793635 15301194048376712498690453)
                  ·
                    refine ⟨717243471017658398376115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15301194048376712498690453 717243471017658398376115)
                    ·
                      rfl

theorem cell22_2095240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_2095240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095240 prefixEnd_2095240 := by exact prefixLift 2095240
  have htrace : WordTrace (prefixWord ++ tailWord_2095240) baseStart_2095240 baseEnd_2095240 := by
    simpa [prefixWord, tailWord_2095240, baseEnd_2095240] using wordTrace_append hprefix tailTrace_2095240
  have hstable : (prefixWord ++ tailWord_2095240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095240).length < 2 ^ (prefixWord ++ tailWord_2095240).sum := by decide
  have hdescent : baseEnd_2095240 < baseStart_2095240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095242 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_2095242 : Nat := 118140960795 + 2095242 * 2 ^ 59
def prefixEnd_2095242 : Nat := 4983230072969 + 3 ^ 40 * 2095242 * 2
def baseEnd_2095242 : Nat := 717244155658531059826109

theorem tailTrace_2095242 : CollatzResearch.WordTrace tailWord_2095242 prefixEnd_2095242 717244155658531059826109 := by
  unfold tailWord_2095242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104938468825886922425995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50946502583535698459802653 19104938468825886922425995)
  ·
    refine ⟨28657407703238830383638993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19104938468825886922425995 28657407703238830383638993)
    ·
      refine ⟨21493055777429122787729245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28657407703238830383638993 21493055777429122787729245)
      ·
        refine ⟨8059895916535921045398467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21493055777429122787729245 8059895916535921045398467)
        ·
          refine ⟨12089843874803881568097701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059895916535921045398467 12089843874803881568097701)
          ·
            refine ⟨2266845726525727794018319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12089843874803881568097701 2266845726525727794018319)
            ·
              refine ⟨3400268589788591691027479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266845726525727794018319 3400268589788591691027479)
              ·
                refine ⟨5100402884682887536541219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400268589788591691027479 5100402884682887536541219)
                ·
                  refine ⟨7650604327024331304811829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100402884682887536541219 7650604327024331304811829)
                  ·
                    refine ⟨717244155658531059826109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7650604327024331304811829 717244155658531059826109)
                    ·
                      rfl

theorem cell22_2095242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_2095242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095242 prefixEnd_2095242 := by exact prefixLift 2095242
  have htrace : WordTrace (prefixWord ++ tailWord_2095242) baseStart_2095242 baseEnd_2095242 := by
    simpa [prefixWord, tailWord_2095242, baseEnd_2095242] using wordTrace_append hprefix tailTrace_2095242
  have hstable : (prefixWord ++ tailWord_2095242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095242).length < 2 ^ (prefixWord ++ tailWord_2095242).sum := by decide
  have hdescent : baseEnd_2095242 < baseStart_2095242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095253 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2095253 : Nat := 118140960795 + 2095253 * 2 ^ 59
def prefixEnd_2095253 : Nat := 4983230072969 + 3 ^ 40 * 2095253 * 2
def baseEnd_2095253 : Nat := 717247921183330697801075

theorem tailTrace_2095253 : CollatzResearch.WordTrace tailWord_2095253 prefixEnd_2095253 717247921183330697801075 := by
  unfold tailWord_2095253
  simp only [CollatzResearch.WordTrace]
  refine ⟨76420155078263696568354413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50946770052175797712236275 76420155078263696568354413)
  ·
    refine ⟨28657558154348886213132905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76420155078263696568354413 28657558154348886213132905)
    ·
      refine ⟨21493168615761664659849679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28657558154348886213132905 21493168615761664659849679)
      ·
        refine ⟨32239752923642496989774519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21493168615761664659849679 32239752923642496989774519)
        ·
          refine ⟨48359629385463745484661779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32239752923642496989774519 48359629385463745484661779)
          ·
            refine ⟨72539444078195618226992669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48359629385463745484661779 72539444078195618226992669)
            ·
              refine ⟨27202291529323356835122251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72539444078195618226992669 27202291529323356835122251)
              ·
                refine ⟨40803437293985035252683377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27202291529323356835122251 40803437293985035252683377)
                ·
                  refine ⟨30602577970488776439512533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40803437293985035252683377 30602577970488776439512533)
                  ·
                    refine ⟨717247921183330697801075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30602577970488776439512533 717247921183330697801075)
                    ·
                      rfl

theorem cell22_2095253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2095253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095253 prefixEnd_2095253 := by exact prefixLift 2095253
  have htrace : WordTrace (prefixWord ++ tailWord_2095253) baseStart_2095253 baseEnd_2095253 := by
    simpa [prefixWord, tailWord_2095253, baseEnd_2095253] using wordTrace_append hprefix tailTrace_2095253
  have hstable : (prefixWord ++ tailWord_2095253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095253).length < 2 ^ (prefixWord ++ tailWord_2095253).sum := by decide
  have hdescent : baseEnd_2095253 < baseStart_2095253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095254 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2095254 : Nat := 118140960795 + 2095254 * 2 ^ 59
def prefixEnd_2095254 : Nat := 4983230072969 + 3 ^ 40 * 2095254 * 2
def baseEnd_2095254 : Nat := 717248263503767028526073

theorem tailTrace_2095254 : CollatzResearch.WordTrace tailWord_2095254 prefixEnd_2095254 717248263503767028526073 := by
  unfold tailWord_2095254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776261971953754608696301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50946794367506715826093877 4776261971953754608696301)
  ·
    refine ⟨1791098239482657978261113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4776261971953754608696301 1791098239482657978261113)
    ·
      refine ⟨1343323679611993483695835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1791098239482657978261113 1343323679611993483695835)
      ·
        refine ⟨2014985519417990225543753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343323679611993483695835 2014985519417990225543753)
        ·
          refine ⟨1511239139563492669157815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014985519417990225543753 1511239139563492669157815)
          ·
            refine ⟨2266858709345239003736723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511239139563492669157815 2266858709345239003736723)
            ·
              refine ⟨3400288064017858505605085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266858709345239003736723 3400288064017858505605085)
              ·
                refine ⟨1275108024006696939601907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3400288064017858505605085 1275108024006696939601907)
                ·
                  refine ⟨1912662036010045409402861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275108024006696939601907 1912662036010045409402861)
                  ·
                    refine ⟨717248263503767028526073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912662036010045409402861 717248263503767028526073)
                    ·
                      rfl

theorem cell22_2095254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2095254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095254 prefixEnd_2095254 := by exact prefixLift 2095254
  have htrace : WordTrace (prefixWord ++ tailWord_2095254) baseStart_2095254 baseEnd_2095254 := by
    simpa [prefixWord, tailWord_2095254, baseEnd_2095254] using wordTrace_append hprefix tailTrace_2095254
  have hstable : (prefixWord ++ tailWord_2095254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095254).length < 2 ^ (prefixWord ++ tailWord_2095254).sum := by decide
  have hdescent : baseEnd_2095254 < baseStart_2095254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095255 : List Nat := [1, 1, 3, 3, 4, 1, 1, 8]
def baseStart_2095255 : Nat := 118140960795 + 2095255 * 2 ^ 59
def prefixEnd_2095255 : Nat := 4983230072969 + 3 ^ 40 * 2095255 * 2
def baseEnd_2095255 : Nat := 79694289536022595472341

theorem tailTrace_2095255 : CollatzResearch.WordTrace tailWord_2095255 prefixEnd_2095255 79694289536022595472341 := by
  unfold tailWord_2095255
  simp only [CollatzResearch.WordTrace]
  refine ⟨76420228024256450909927219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50946818682837633939951479 76420228024256450909927219)
  ·
    refine ⟨114630342036384676364890829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76420228024256450909927219 114630342036384676364890829)
    ·
      refine ⟨42986378263644253636834061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114630342036384676364890829 42986378263644253636834061)
      ·
        refine ⟨16119891848866595113812773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42986378263644253636834061 16119891848866595113812773)
        ·
          refine ⟨3022479721662486583839895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16119891848866595113812773 3022479721662486583839895)
          ·
            refine ⟨4533719582493729875759843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022479721662486583839895 4533719582493729875759843)
            ·
              refine ⟨6800579373740594813639765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533719582493729875759843 6800579373740594813639765)
              ·
                refine ⟨79694289536022595472341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6800579373740594813639765 79694289536022595472341)
                ·
                  rfl

theorem cell22_2095255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 8].length) (baseStart_2095255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095255 prefixEnd_2095255 := by exact prefixLift 2095255
  have htrace : WordTrace (prefixWord ++ tailWord_2095255) baseStart_2095255 baseEnd_2095255 := by
    simpa [prefixWord, tailWord_2095255, baseEnd_2095255] using wordTrace_append hprefix tailTrace_2095255
  have hstable : (prefixWord ++ tailWord_2095255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095255).length < 2 ^ (prefixWord ++ tailWord_2095255).sum := by decide
  have hdescent : baseEnd_2095255 < baseStart_2095255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
